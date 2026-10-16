#!/usr/bin/env python3
"""Biên dịch lần lượt các mô-đun theo thứ tự phụ thuộc để giảm bộ nhớ dùng cùng lúc."""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys

from check_project import ROOT, code_only, modules_and_gap_scan


def build_order() -> list[str]:
    modules, _ = modules_and_gap_scan()
    seen: set[str] = set()
    order: list[str] = []

    def visit(module: str) -> None:
        if module in seen:
            return
        seen.add(module)
        code = code_only(modules[module].read_text(encoding="utf-8"))
        for match in re.finditer(
            r"^\s*(?:(?:public|private|meta)\s+)*import\s+(.+?)\s*$", code, re.M
        ):
            for dependency in match[1].split():
                if dependency in modules:
                    visit(dependency)
        order.append(module)

    visit("calculus")
    return order


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--print-order", action="store_true")
    args = parser.parse_args()
    order = build_order()
    if args.print_order:
        print("\n".join(order))
        return 0
    env = {**os.environ, "LEAN_NUM_THREADS": "1"}
    for index, module in enumerate(order, 1):
        print(f"BUILD_MODULE {index}/{len(order)}: {module}", flush=True)
        result = subprocess.run(["lake", "--wfail", "build", module], cwd=ROOT, env=env)
        if result.returncode:
            return result.returncode
    print(f"SEQUENTIAL_BUILD_OK: {len(order)} modules", flush=True)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except ValueError as error:
        print(f"BUILD_FAILED: {error}", file=sys.stderr)
        sys.exit(1)
