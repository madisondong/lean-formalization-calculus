#!/usr/bin/env python3
"""Kiểm tra danh sách `sorry` được phép và ngăn chúng đi vào các chứng minh khác."""

from contextlib import redirect_stderr, redirect_stdout
import io
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import check_project


PROJECT_ROOT = Path(__file__).resolve().parent.parent
SOURCE_ID = "C02-S10-exercise-013"
MODULE = "calculus.SourceExerciseFixture"
NAME = MODULE + ".original_assertion"
ENTRY = {"source_id": SOURCE_ID, "declaration": NAME, "module": MODULE}
EXERCISE = """/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem original_assertion : False := by
  sorry
"""


class SourceExerciseChecks(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.root_patch = patch.object(check_project, "ROOT", self.root)
        self.root_patch.start()
        self.addCleanup(self.root_patch.stop)
        (self.root / "calculus").mkdir()
        (self.root / "calculus.lean").write_text(f"import {MODULE}\n", encoding="utf-8")
        self.source = self.root / "calculus/SourceExerciseFixture.lean"
        self.write_source(EXERCISE)
        self.allowlist_patch = patch.object(check_project, "SOURCE_EXERCISES", (dict(ENTRY),))
        self.allowlist_patch.start()
        self.addCleanup(self.allowlist_patch.stop)

    def write_source(self, body, namespace=MODULE):
        self.source.write_text(f"namespace {namespace}\n{body}\nend {namespace}\n", encoding="utf-8")

    def set_allowlist(self, entries):
        check_project.SOURCE_EXERCISES = tuple(dict(entry) for entry in entries)

    def run_main(self, *arguments):
        output = io.StringIO()
        with patch.object(check_project, "locks"), patch.object(sys, "argv", ["check_project.py", *arguments]), \
                redirect_stdout(output), redirect_stderr(output):
            result = check_project.main()
        return result, output.getvalue()

    def test_project_checks_need_no_external_registry(self):
        result, output = self.run_main()
        self.assertEqual(result, 0, output)
        self.assertIn("PROJECT_OK: 2 project modules; 1 explicitly approved", output)
        self.assertNotIn("COVERAGE_OK", output)
        self.assertEqual((self.root / ".lake/audit-source-exercises.txt").read_text(),
                         f"{SOURCE_ID}\t{NAME}\t{MODULE}\n")
        self.assertFalse((self.root / ".lake/audit-source-declarations.txt").exists())
        self.assertFalse((self.root / "Audit").exists())
        self.assertFalse((self.root / "audit/data").exists())

    def test_current_allowlist_replaces_a_stale_generated_table_in_exact_order(self):
        second = {**ENTRY, "source_id": "C02-S10-exercise-014", "declaration": MODULE + ".second"}
        self.set_allowlist([second, ENTRY])
        self.write_source(EXERCISE + EXERCISE.replace("original_assertion", "second"))
        output = self.root / ".lake/audit-source-exercises.txt"
        output.parent.mkdir()
        output.write_text("stale\n")
        result, diagnostics = self.run_main()
        self.assertEqual(result, 0, diagnostics)
        self.assertEqual(output.read_text(), f"{SOURCE_ID}\t{NAME}\t{MODULE}\n"
                         f"C02-S10-exercise-014\t{MODULE}.second\t{MODULE}\n")

    def test_failed_gap_scan_does_not_write_an_approval_table(self):
        self.write_source(EXERCISE + "\ntheorem extra : False := by sorry\n")
        with patch.object(check_project, "write_exercise_table") as writer:
            result, output = self.run_main()
        self.assertEqual(result, 1)
        self.assertIn("Prohibited", output)
        writer.assert_not_called()

    def test_removed_approval_never_authorizes_an_active_hole(self):
        self.set_allowlist([])
        with self.assertRaisesRegex(ValueError, "Prohibited"):
            check_project.modules_and_gap_scan()

    def test_locks_only_does_not_read_the_exercise_allowlist(self):
        with patch.object(check_project, "SOURCE_EXERCISES", None):
            result, output = self.run_main("--locks-only")
        self.assertEqual(result, 0, output)
        self.assertNotIn("PROJECT_OK", output)
        self.assertFalse((self.root / ".lake/audit-source-exercises.txt").exists())

    def test_comments_and_strings_do_not_supply_or_hide_active_holes(self):
        self.set_allowlist([])
        self.write_source('/- theorem x : False := by sorry /- admit -/ -/\n'
                          'def text : String := "sorry admit sorryAx"\n'
                          'theorem complete : True := by trivial\n')
        check_project.modules_and_gap_scan()
        self.write_source('def text : String := "sorry"\n' + EXERCISE)
        with self.assertRaisesRegex(ValueError, "Prohibited"):
            check_project.modules_and_gap_scan()

    def test_unapproved_or_nontrivial_holes_and_trust_shortcuts_fail(self):
        cases = [
            EXERCISE + "\ntheorem other : False := by sorry\n",
            EXERCISE.replace("  sorry", "  have h : True := by trivial\n  sorry"),
            EXERCISE.replace("  sorry", "  sorry\n  sorry"),
            EXERCISE.replace("  sorry", "  sorry!"),
            EXERCISE.replace("  sorry", "  admit"),
            EXERCISE + "\naxiom extra : False\n",
            EXERCISE + "\nset_option warn.sorry false\n",
            EXERCISE + "\nset_option warningAsError false\n",
            EXERCISE + "\nset_option linter.unusedVariables false\n",
            EXERCISE + "\nset_option debug.skipKernelTC true\n",
            EXERCISE + "\ndef trust : False := sorryAx False true\n",
            EXERCISE + "\ntheorem trust : True := by native_decide\n",
            EXERCISE + "\nunsafe def trust : Nat := 0\n",
            EXERCISE + "\n@[implemented_by other] def trust : Nat := 0\n",
            EXERCISE + '\n@[extern "trust"] opaque trust : Nat\n',
            EXERCISE + "\ndef trust := Lean.ofReduceBool\n",
            EXERCISE + "\ndef trust := Lean.ofReduceNat\n",
        ]
        for body in cases:
            with self.subTest(body=body):
                self.write_source(body)
                with self.assertRaises(ValueError):
                    check_project.modules_and_gap_scan()

    def test_wrong_namespace_or_definition_is_not_an_approved_theorem(self):
        for body, namespace in [(EXERCISE, "calculus.Other"),
                                (EXERCISE.replace("theorem ", "def "), MODULE)]:
            with self.subTest(namespace=namespace, body=body):
                self.write_source(body, namespace)
                with self.assertRaises(ValueError):
                    check_project.modules_and_gap_scan()

    def test_exact_qualified_and_nested_namespace_theorems_are_accepted(self):
        self.source.write_text(EXERCISE.replace("theorem original_assertion",
                                               "theorem _root_." + NAME), encoding="utf-8")
        check_project.modules_and_gap_scan()
        self.source.write_text("namespace calculus\nnamespace SourceExerciseFixture\nsection\n" +
                               EXERCISE + "end\nend SourceExerciseFixture\nend calculus\n", encoding="utf-8")
        check_project.modules_and_gap_scan()

    def test_completed_or_absent_exercise_requires_allowlist_update(self):
        for body in ["theorem original_assertion : True := by trivial\n", ""]:
            with self.subTest(body=body):
                self.write_source(body)
                with self.assertRaisesRegex(ValueError, "Original-source exercise"):
                    check_project.modules_and_gap_scan()

    def test_duplicate_or_invalid_allowlist_entries_fail(self):
        self.set_allowlist([ENTRY, ENTRY])
        with self.assertRaisesRegex(ValueError, "Duplicate"):
            check_project.source_exercises()
        for value in [None, [ENTRY], ("not an exercise entry",)]:
            with self.subTest(value=value), patch.object(check_project, "SOURCE_EXERCISES", value):
                with self.assertRaisesRegex(ValueError, "Invalid original-source exercise"):
                    check_project.source_exercises()

    def test_source_id_module_and_declaration_are_validated(self):
        cases = [{**ENTRY, "source_id": "not-a-source-id"},
                 {**ENTRY, "source_id": SOURCE_ID + "\tother"},
                 {**ENTRY, "module": "other.Module"},
                 {**ENTRY, "declaration": "calculus.Other.claim"},
                 {**ENTRY, "module": MODULE + " "},
                 {**ENTRY, "declaration": NAME + "\n"},
                 {**ENTRY, "extra": "ignored"}]
        for entry in cases:
            with self.subTest(entry=entry):
                self.set_allowlist([entry])
                with self.assertRaises(ValueError):
                    check_project.source_exercises()
        self.set_allowlist([{**ENTRY, "module": "calculus"}])
        with self.assertRaisesRegex(ValueError, "wrong module"):
            check_project.modules_and_gap_scan()

    def test_unimported_module_is_rejected(self):
        (self.root / "calculus/Omitted.lean").write_text("theorem complete : True := by trivial\n")
        with self.assertRaisesRegex(ValueError, "omitted"):
            check_project.modules_and_gap_scan()

    def test_missing_import_and_import_cycle_are_rejected(self):
        (self.root / "calculus.lean").write_text("import calculus.Missing\n")
        with self.assertRaisesRegex(ValueError, "Missing imported"):
            check_project.modules_and_gap_scan()
        (self.root / "calculus.lean").write_text(f"import {MODULE}\n")
        self.source.write_text("import calculus\n" + self.source.read_text())
        with self.assertRaisesRegex(ValueError, "cycle"):
            check_project.modules_and_gap_scan()

    def test_runtime_checks_the_selected_log_and_rejects_another_compiler(self):
        log = self.root / "new-run/lean-version.log"
        log.parent.mkdir()
        log.write_text(f"Lean (version 4.33.0, x86_64-apple-darwin, "
                       f"commit {check_project.LEAN_COMMIT}, Release)\n")
        result, output = self.run_main("--locks-only", "--runtime", "--runtime-log", str(log))
        self.assertEqual(result, 0, output)
        self.assertIn("RUNTIME_OK", output)
        self.assertFalse((self.root / ".lake/verification").exists())
        log.write_text("Lean (version 4.32.0, another compiler, Release)\n")
        result, output = self.run_main("--locks-only", "--runtime", "--runtime-log", str(log))
        self.assertEqual(result, 1)
        self.assertIn("Actual compiler does not match", output)


class KernelExerciseTrustBoundary(unittest.TestCase):
    """Dùng chính bộ kiểm toán của dự án trên mô-đun Lean nhỏ, độc lập với mathlib."""

    @classmethod
    def setUpClass(cls):
        cls.audit = (PROJECT_ROOT / "Audit/CheckAxioms.lean").read_text(encoding="utf-8").replace(
            "import calculus\n", f"import {MODULE}\n", 1)
        cls.toolchain = (PROJECT_ROOT / "lean-toolchain").read_text().strip()

    def run_audit(self, declarations=EXERCISE, exercise_table=None):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "calculus/SourceExerciseFixture.lean"
            source.parent.mkdir()
            source.write_text("import Lean.Elab.GuardMsgs\nnamespace " + MODULE + "\n" +
                              declarations + "\nend " + MODULE + "\n", encoding="utf-8")
            env = {**os.environ, "ELAN_TOOLCHAIN": self.toolchain, "LEAN_PATH": str(root),
                   "LEAN_NUM_THREADS": "1"}
            built = subprocess.run(["lean", "--root", str(root), "-o", str(source.with_suffix(".olean")),
                                    str(source)], cwd=root, env=env, capture_output=True, text=True, timeout=60)
            self.assertEqual(built.returncode, 0, built.stdout + built.stderr)
            (root / ".lake").mkdir()
            (root / ".lake/audit-source-exercises.txt").write_text(
                f"{SOURCE_ID}\t{NAME}\t{MODULE}\n" if exercise_table is None else exercise_table)
            audit_path = root / "AuditFixture.lean"
            audit_path.write_text(self.audit, encoding="utf-8")
            result = subprocess.run(["lean", "-DwarningAsError=true", str(audit_path)],
                                    cwd=root, env=env, capture_output=True, text=True, timeout=60)
            return result.returncode, result.stdout + result.stderr

    def test_exact_original_assertion_passes_with_distinct_diagnostics(self):
        code, output = self.run_audit(EXERCISE + "\ntheorem complete : True := by trivial\n")
        self.assertEqual(code, 0, output)
        self.assertIn(f"SOURCE_EXERCISE_TYPE {SOURCE_ID} {NAME}: False", output)
        self.assertIn("1 original-source exercises", output)
        self.assertIn(f"AXIOMS {MODULE}.complete: []", output)
        self.assertNotIn(f"AXIOMS {NAME}:", output.replace("SOURCE_EXERCISE_AXIOMS", "EXERCISE"))

    def test_transitive_use_in_another_theorem_is_rejected(self):
        code, output = self.run_audit(EXERCISE +
            "\ntheorem contaminated : False := original_assertion\n")
        self.assertNotEqual(code, 0, output)
        self.assertIn(f"Axiom audit failed for {MODULE}.contaminated", output)
        self.assertIn("sorryAx", output)

    def test_transitive_use_in_a_definition_is_rejected(self):
        code, output = self.run_audit(EXERCISE +
            "\nnoncomputable def contaminated : Nat := False.elim original_assertion\n")
        self.assertNotEqual(code, 0, output)
        self.assertIn(f"Axiom audit failed for {MODULE}.contaminated", output)
        self.assertIn("sorryAx", output)

    def test_project_module_origin_is_audited_outside_the_project_namespace(self):
        code, output = self.run_audit(EXERCISE + f"\nend {MODULE}\nnamespace Other\n"
            f"theorem contaminated : False := {NAME}\nend Other\nnamespace {MODULE}\n")
        self.assertNotEqual(code, 0, output)
        self.assertIn("Axiom audit failed for Other.contaminated", output)

    def test_new_axiom_is_rejected_even_though_lean_accepts_it(self):
        code, output = self.run_audit(EXERCISE + "\naxiom extra : False\n")
        self.assertNotEqual(code, 0, output)
        self.assertIn(f"Axiom audit failed for {MODULE}.extra", output)

    def test_missing_approval_does_not_exempt_a_module(self):
        code, output = self.run_audit(exercise_table="")
        self.assertNotEqual(code, 0, output)
        self.assertIn(f"Axiom audit failed for {NAME}", output)

    def test_duplicate_or_missing_exported_exercise_fails(self):
        row = f"{SOURCE_ID}\t{NAME}\t{MODULE}\n"
        code, output = self.run_audit(exercise_table=row + row)
        self.assertNotEqual(code, 0, output)
        self.assertIn("Repeated original-source exercise", output)
        code, output = self.run_audit(exercise_table=row.replace(NAME, MODULE + ".missing"))
        self.assertNotEqual(code, 0, output)
        self.assertIn("not exported", output)

    def test_module_and_theorem_kind_are_checked(self):
        code, output = self.run_audit(exercise_table=f"{SOURCE_ID}\t{NAME}\tcalculus.Other\n")
        self.assertNotEqual(code, 0, output)
        self.assertIn("Original-source exercise module mismatch", output)
        code, output = self.run_audit(EXERCISE.replace("theorem ", "def ").replace(": False", ": Nat"))
        self.assertNotEqual(code, 0, output)
        self.assertIn("Original-source exercise is not a theorem", output)

    def test_completed_statement_cannot_retain_exercise_exemption(self):
        code, output = self.run_audit("theorem original_assertion : True := by trivial\n")
        self.assertNotEqual(code, 0, output)
        self.assertIn("no longer contains sorryAx", output)


if __name__ == "__main__":
    unittest.main()
