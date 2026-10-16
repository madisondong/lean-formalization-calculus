#!/usr/bin/env python3
"""Đóng gói thư viện và tài liệu hiện hành theo danh sách tệp được phép."""

from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parent.parent
OUTPUT = ROOT / "output/calculus-companion.zip"
ROOT_FILES = (
    "README.md", "LICENSE", ".gitignore",
    "lean-toolchain", "lakefile.toml", "lake-manifest.json", "calculus.lean",
)
DOCUMENT_FILES = (
    "docs/errata.md", "docs/glossary-vi-en.md",
)
SOURCE_PATTERNS = (
    "calculus/**/*.lean", "Audit/*.lean", "scripts/*.py", "scripts/*.sh",
    ".github/workflows/*.yml", ".github/workflows/*.yaml",
)
EXCLUDED_DIRECTORIES = (
    ".lake/", ".git/", "source/", "output/", "docs/evidence/", "docs/batches/", "docs/history/",
)


def distribution_files() -> list[Path]:
    """Chọn mã và tài liệu cho bản phân phối."""
    files = {ROOT / name for name in (*ROOT_FILES, *DOCUMENT_FILES)}
    for pattern in SOURCE_PATTERNS:
        files.update(ROOT.glob(pattern))
    for path in files:
        if path.is_symlink() or not path.is_file():
            raise ValueError(f"Invalid distribution file: {path}")
    return sorted(files)


def main() -> None:
    files = distribution_files()
    OUTPUT.parent.mkdir(exist_ok=True)
    with zipfile.ZipFile(OUTPUT, "w", compression=zipfile.ZIP_DEFLATED) as archive:
        for path in files:
            archive.write(path, path.relative_to(ROOT).as_posix())
    with zipfile.ZipFile(OUTPUT) as archive:
        bad = archive.testzip()
        if bad:
            raise ValueError(f"Archive CRC error: {bad}")
        names = archive.namelist()
        if any(name.startswith(EXCLUDED_DIRECTORIES) for name in names):
            raise ValueError("Bản phân phối chứa hồ sơ cục bộ, giáo trình hoặc cache")
        print(f"{OUTPUT}: {len(names)} files; {OUTPUT.stat().st_size} bytes; CRC OK")


if __name__ == "__main__":
    main()
