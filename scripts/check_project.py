#!/usr/bin/env python3
"""Kiểm tra mô-đun, phát biểu chưa chứng minh và các khóa phụ thuộc."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys
from typing import Optional

ROOT = Path(__file__).resolve().parent.parent
TOOLCHAIN = "leanprover/lean4:v4.33.0"
LEAN_COMMIT = "d8b18978322de05a8f3dba51ef03cf5461676c17"
MATHLIB_REV = "db584cd6d46c92f209a44c0f1c829460d327499d"
MODULE = re.compile(r"calculus(?:\.[A-Za-z][A-Za-z0-9_]*)*")
DECLARATION = re.compile(r"calculus(?:\.[A-Za-z][A-Za-z0-9_']*)+")
SOURCE_EXERCISES = (
    {
        'source_id': 'C01-S04-exercise-016.p02',
        'declaration': 'calculus.Chapter01.Section04Exercises.source_even_criterion_and_negation',
        'module': 'calculus.Chapter01.Section04Exercises',
    },
    {
        'source_id': 'C01-S04-exercise-016.p06',
        'declaration': 'calculus.Chapter01.Section04Exercises.not_source_bounded_oscillation_iff',
        'module': 'calculus.Chapter01.Section04Exercises',
    },
    {
        'source_id': 'C02-S01-remark-004',
        'declaration': 'calculus.Chapter02.Section01.source_sup_inf_rules',
        'module': 'calculus.Chapter02.Section01',
    },
    {
        'source_id': 'C02-S03-example-006.proof-strict-error',
        'declaration': 'calculus.Chapter02.Section03.source_alternating_odd_strict_error',
        'module': 'calculus.Chapter02.Section03',
    },
    {
        'source_id': 'C02-S04-theorem-005.proof-sign-interval',
        'declaration': 'calculus.Chapter02.Section04.source_zero_mul_signed_interval',
        'module': 'calculus.Chapter02.Section04',
    },
    {
        'source_id': 'C02-S05-theorem-001.proof-strict-reciprocal-bound',
        'declaration': 'calculus.Chapter02.Section05.source_reciprocal_strict_error_bound',
        'module': 'calculus.Chapter02.Section05',
    },
    {
        'source_id': 'C02-S07-exercise-004',
        'declaration': 'calculus.Chapter02.Section06Supplement.source_arithmetic_harmonic_mean_convergence',
        'module': 'calculus.Chapter02.Section06Supplement',
    },
    {
        'source_id': 'C02-S08-theorem-006.proof-initial-anchor',
        'declaration': 'calculus.Chapter02.Section07.source_ratio_initial_anchor',
        'module': 'calculus.Chapter02.Section07',
    },
    {
        'source_id': 'C02-S10-example-001.proof-repeated-index',
        'declaration': 'calculus.Chapter02.Section09.source_reciprocal_repeated_index_identity',
        'module': 'calculus.Chapter02.Section09',
    },
    {
        'source_id': 'C02-S10-exercise-013',
        'declaration': 'calculus.Chapter02.Section09.source_natural_sequence_eventually_constant',
        'module': 'calculus.Chapter02.Section09',
    },
    {
        'source_id': 'C02-S10-exercise-014',
        'declaration': 'calculus.Chapter02.Section09.source_convergent_of_bounded_steps',
        'module': 'calculus.Chapter02.Section09',
    },
    {
        'source_id': 'C02-S11-definition-001.p05',
        'declaration': 'calculus.Chapter02.Section10.source_finite_part_sup_inf_definition',
        'module': 'calculus.Chapter02.Section10',
    },
    {
        'source_id': 'C02-S11-prose-L2937',
        'declaration': 'calculus.Chapter02.Section10.source_finite_part_extrema_exist',
        'module': 'calculus.Chapter02.Section10',
    },
    {
        'source_id': 'C02-S11-theorem-001.proof-strict-tail-supremum',
        'declaration': 'calculus.Chapter02.Section10Supplement.source_strict_tail_supremum_subsequence',
        'module': 'calculus.Chapter02.Section10Supplement',
    },
    {
        'source_id': 'C04-S03-exercise-005',
        'declaration': 'calculus.Chapter04.Section03ExercisesBasic.source_exponential_ratio_witness',
        'module': 'calculus.Chapter04.Section03ExercisesBasic',
    },
)


def fail(message: str) -> None:
    raise ValueError(message)


def code_only(text: str) -> str:
    """Xóa chú thích lồng nhau và chuỗi Lean nhưng giữ dòng để định vị lỗi."""
    out: list[str] = []
    i = 0
    depth = 0
    in_string = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                out.extend("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif in_string:
            if text[i] == "\\":
                out.extend("  ")
                i += 2
            else:
                in_string = text[i] != '"'
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            out.extend("  ")
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end == -1:
                out.extend(" " * (len(text) - i))
                break
            out.extend(" " * (end - i))
            i = end
        elif text[i] == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def source_exercises() -> list[dict[str, str]]:
    """Kiểm tra đúng các phát biểu gốc được phép giữ bằng `sorry`."""
    if not isinstance(SOURCE_EXERCISES, tuple):
        fail("Invalid original-source exercise allowlist")
    seen: set[str] = set()
    for exercise in SOURCE_EXERCISES:
        if not isinstance(exercise, dict) or set(exercise) != {"source_id", "declaration", "module"} or \
                any(not isinstance(value, str) or value != value.strip() for value in exercise.values()):
            fail("Invalid original-source exercise entry")
        source_id, name, module = (exercise[key] for key in ("source_id", "declaration", "module"))
        if not re.fullmatch(r"C[0-9]{2}-[^\s]+", source_id) or not DECLARATION.fullmatch(name) or \
                not MODULE.fullmatch(module) or not name.startswith(module + "."):
            fail(f"Invalid original-source exercise reference: {exercise!r}")
        if name in seen:
            fail(f"Duplicate original-source exercise declaration: {name}")
        seen.add(name)
    return [dict(exercise) for exercise in SOURCE_EXERCISES]


def exercise_sorry_positions(code: str, module: str,
                             exercises: list[dict[str, str]]) -> tuple[set[int], set[str]]:
    """Chỉ nhận thân `by sorry` của đúng định lí và namespace đã khai báo."""
    approved = {entry["declaration"]: entry for entry in exercises}
    commands = list(re.finditer(r"^\S[^\n]*", code, re.MULTILINE))
    scopes: list[tuple[str, str]] = []
    positions: set[int] = set()
    seen: set[str] = set()
    for index, command in enumerate(commands):
        line = command[0].strip()
        opening = re.fullmatch(r"(namespace|section)(?:\s+([A-Za-z_][A-Za-z0-9_.']*))?", line)
        if opening:
            scopes.append((opening[1], opening[2] or ""))
            continue
        if re.fullmatch(r"end(?:\s+[A-Za-z_][A-Za-z0-9_.']*)?", line):
            if scopes:
                scopes.pop()
            continue
        declaration = re.match(r"theorem\s+([A-Za-z_][A-Za-z0-9_.']*)\b", line)
        if not declaration:
            continue
        local_name = declaration[1]
        namespace = ".".join(name for kind, name in scopes if kind == "namespace")
        name = local_name.removeprefix("_root_.") if local_name.startswith("_root_.") else \
            ".".join(part for part in (namespace, local_name) if part)
        if name not in approved:
            continue
        if approved[name]["module"] != module:
            fail(f"Original-source exercise {name} is in the wrong module: {module}")
        if name in seen:
            fail(f"Repeated original-source exercise declaration: {name}")
        end = commands[index + 1].start() if index + 1 < len(commands) else len(code)
        body = re.search(r":=\s*by\s+(sorry)\s*\Z", code[command.start():end])
        if body is None:
            fail(f"Original-source exercise must have exactly a `by sorry` proof: {name}")
        positions.add(command.start() + body.start(1))
        seen.add(name)
    return positions, seen


def modules_and_gap_scan() -> tuple[dict[str, Path], set[str]]:
    files = [ROOT / "calculus.lean", *sorted((ROOT / "calculus").rglob("*.lean"))]
    if not files[0].is_file():
        fail("Missing root import file calculus.lean")
    modules = {
        str(path.relative_to(ROOT).with_suffix("")).replace("/", "."): path
        for path in files
    }
    exercises = source_exercises()
    seen_exercises: set[str] = set()
    graph: dict[str, list[str]] = {}
    banned = re.compile(
        r"\b(?:sorry|admit|sorryAx|axiom|native_decide|unsafe|implemented_by|extern)\b"
        r"|\bLean\.(?:ofReduceBool|ofReduceNat)\b"
        r"|\bset_option\s+(?:debug\.skipKernelTC)\s+true\b"
        r"|\bset_option\s+(?:warningAsError|warn\.sorry|linter(?:\.[A-Za-z0-9_]+)?)\s+false\b"
    )
    for module, path in modules.items():
        code = code_only(path.read_text(encoding="utf-8"))
        approved_positions, found = exercise_sorry_positions(code, module, exercises)
        seen_exercises.update(found)
        for match in banned.finditer(code):
            if match[0] == "sorry" and match.start() in approved_positions:
                continue
            line = code[:match.start()].count("\n") + 1
            fail(f"Prohibited proof/trust or warning-suppression token: {path}:{line}: {match[0]}")
        imports: list[str] = []
        for line in code.splitlines():
            match = re.match(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(.+?)\s*$", line)
            if match:
                imports.extend(match[1].split())
        graph[module] = [name for name in imports if name == "calculus" or name.startswith("calculus.")]
        for dependency in graph[module]:
            if dependency not in modules:
                fail(f"Missing imported project module: {module} imports {dependency}")
    visiting: set[str] = set()
    reached: set[str] = set()

    def visit(module: str) -> None:
        if module in visiting:
            fail(f"Project import cycle through {module}")
        if module in reached:
            return
        visiting.add(module)
        for dependency in graph[module]:
            visit(dependency)
        visiting.remove(module)
        reached.add(module)

    visit("calculus")
    missing = set(modules) - reached
    if missing:
        fail("Project modules omitted from calculus.lean: " + ", ".join(sorted(missing)))
    missing_exercises = {entry["declaration"] for entry in exercises} - seen_exercises
    if missing_exercises:
        fail("Original-source exercises without their declared `by sorry` theorem: "
             + ", ".join(sorted(missing_exercises)))
    return modules, reached


def write_exercise_table() -> int:
    """Ghi đúng danh sách cho phép hiện hành để Lean kiểm tra từng phát biểu."""
    exercises = source_exercises()
    output = ROOT / ".lake/audit-source-exercises.txt"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("".join(
        f"{entry['source_id']}\t{entry['declaration']}\t{entry['module']}\n"
        for entry in sorted(exercises, key=lambda entry: (entry["source_id"], entry["declaration"]))
    ), encoding="utf-8")
    return len(exercises)


def locks(checkouts: bool) -> None:
    if (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip() != TOOLCHAIN:
        fail(f"Toolchain changed from the reviewed pin {TOOLCHAIN}")
    config = (ROOT / "lakefile.toml").read_text(encoding="utf-8")
    if not re.search(rf'^rev\s*=\s*"{MATHLIB_REV}"\s*$', config, re.MULTILINE):
        fail("lakefile.toml does not contain the reviewed mathlib pin")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    if manifest["packagesDir"] != ".lake/packages":
        fail("Manifest packagesDir must remain the project-local .lake/packages")
    packages = manifest["packages"]
    mathlib = [package for package in packages if package["name"] == "mathlib"]
    if len(mathlib) != 1 or mathlib[0]["rev"] != MATHLIB_REV:
        fail("Manifest mathlib revision does not match the reviewed pin")
    for package in packages:
        if package["type"] != "git" or not re.fullmatch(r"[0-9a-f]{40}", package["rev"]):
            fail(f"Dependency is not locked to a full Git commit: {package['name']}")
        if checkouts:
            path = ROOT / manifest["packagesDir"] / package["name"]
            package_root = ROOT / ".lake/packages"
            if package_root.resolve() != package_root or not path.resolve().is_relative_to(package_root):
                fail(f"Dependency checkout resolves outside project-local .lake/packages: {package['name']}")
            result = subprocess.run(["git", "-C", str(path), "rev-parse", "HEAD"], capture_output=True, text=True, check=True)
            if result.stdout.strip() != package["rev"]:
                fail(f"Dependency checkout differs from manifest: {package['name']}")
            dirty = subprocess.run(["git", "-C", str(path), "status", "--porcelain", "--untracked-files=no"], capture_output=True, text=True, check=True)
            if dirty.stdout.strip():
                fail(f"Tracked dependency sources are modified: {package['name']}")
    print(f"LOCKS_OK: {TOOLCHAIN}; mathlib {MATHLIB_REV}; {len(packages)} pinned Git dependencies" + ("; checkouts clean" if checkouts else ""))


def runtime(path: Optional[Path] = None) -> None:
    if path is None:
        path = ROOT / ".lake/verification/lean-version.log"
    version = path.read_text(encoding="utf-8").strip()
    if not re.fullmatch(rf"Lean \(version 4\.33\.0, .*commit {LEAN_COMMIT}, Release\)", version):
        fail(f"Actual compiler does not match the reviewed Lean release: {version}")
    print(f"RUNTIME_OK: Lean 4.33.0; compiler commit {LEAN_COMMIT}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--locks-only", action="store_true")
    parser.add_argument("--checkouts", action="store_true")
    parser.add_argument("--runtime", action="store_true")
    parser.add_argument("--runtime-log", type=Path,
                        help="Nhật ký phiên bản Lean; mặc định .lake/verification/lean-version.log")
    args = parser.parse_args()
    try:
        locks(args.checkouts)
        if args.runtime:
            runtime(args.runtime_log)
        if not args.locks_only:
            _, reached = modules_and_gap_scan()
            count = write_exercise_table()
            print(f"PROJECT_OK: {len(reached)} project modules; "
                  f"{count} explicitly approved original-source assertions with sorry")
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError, json.JSONDecodeError) as error:
        print(f"CHECK_FAILED: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
