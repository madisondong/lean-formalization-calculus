#!/usr/bin/env bash
# Biên dịch và kiểm tra tiên đề; giữ nhật ký riêng cho mỗi lần chạy.
set -euo pipefail
export LEAN_NUM_THREADS=1
project_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$project_dir"
mkdir -p .lake/verification
verification_dir="$(mktemp -d .lake/verification/run-XXXXXXXX)"
printf 'VERIFICATION_LOGS: %s\n' "$verification_dir"

python3 scripts/check_project.py --locks-only 2>&1 | tee "$verification_dir/locks.log"
python3 scripts/test_source_exercises.py 2>&1 | tee "$verification_dir/tests.log"
cp lake-manifest.json "$verification_dir/manifest-before.json"
lake env lean --version | tee "$verification_dir/lean-version.log"
lake --version | tee "$verification_dir/lake-version.log"
python3 scripts/check_project.py --locks-only --runtime \
  --runtime-log "$verification_dir/lean-version.log" 2>&1 | tee "$verification_dir/runtime.log"
python3 scripts/build_sequential.py 2>&1 | tee "$verification_dir/build.log"
cmp lake-manifest.json "$verification_dir/manifest-before.json"
python3 scripts/check_project.py --checkouts 2>&1 | tee "$verification_dir/project.log"
cp .lake/audit-source-exercises.txt "$verification_dir/source-exercises.txt"
lake env lean -DwarningAsError=true Audit/CheckAxioms.lean 2>&1 | tee "$verification_dir/axioms.log"
cmp lake-manifest.json "$verification_dir/manifest-before.json"
printf '%s\n' 'CHECK_OK: build, module coverage, dependency pins, strict axiom audit' \
  | tee "$verification_dir/result.log"
