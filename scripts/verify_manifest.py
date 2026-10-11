#!/usr/bin/env python3
"""Verify release hashes and file coverage, or regenerate the release manifest.

Copyright (c) 2026 wang060919. Released under the MIT license.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import os
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "SHA256SUMS"
PRIVATE_DIRS = {".git", ".lake", ".tools", ".work"}
BUILD_SUFFIXES = {".olean", ".ilean", ".c", ".o"}


def release_files():
    if (ROOT / ".git").exists():
        output = subprocess.check_output(
            ["git", "-C", str(ROOT), "ls-files", "-z"], timeout=30)
        files = {os.fsdecode(name) for name in output.split(b"\0") if name}
        return files - {"SHA256SUMS"}
    files = set()
    for directory, subdirs, names in os.walk(ROOT, followlinks=False):
        subdirs[:] = [name for name in subdirs if name not in PRIVATE_DIRS]
        for name in names:
            path = Path(directory) / name
            relative = path.relative_to(ROOT).as_posix()
            if relative != "SHA256SUMS" and path.suffix not in BUILD_SUFFIXES:
                files.add(relative)
    return files


def checked_path(relative):
    path = PurePosixPath(relative)
    if path.is_absolute() or ".." in path.parts or str(path) != relative:
        raise SystemExit(f"Invalid manifest path: {relative}")
    if any(part in PRIVATE_DIRS for part in path.parts):
        raise SystemExit(f"Private directory listed for release: {relative}")
    source = ROOT / relative
    if source.is_symlink() or not source.is_file():
        raise SystemExit(f"Release input must be a regular file: {relative}")
    return source


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true",
                        help="Regenerate SHA256SUMS from the release file inventory")
    options = parser.parse_args()
    files = release_files()
    if options.write:
        MANIFEST.write_text("".join(
            f"{hashlib.sha256(checked_path(name).read_bytes()).hexdigest()}  {name}\n"
            for name in sorted(files)))
        print(f"Wrote SHA256SUMS for {len(files)} release files.")
        return
    entries = {}
    for line in MANIFEST.read_text().splitlines():
        match = re.fullmatch(r"([0-9a-f]{64})  (.+)", line)
        if match is None:
            raise SystemExit("Malformed SHA256SUMS entry")
        digest, name = match.groups()
        if name in entries:
            raise SystemExit(f"Duplicate manifest entry: {name}")
        entries[name] = digest
    missing = files - entries.keys()
    stale = entries.keys() - files
    if missing or stale:
        raise SystemExit(f"Manifest coverage mismatch; unlisted={sorted(missing)}, stale={sorted(stale)}")
    for name, digest in entries.items():
        if hashlib.sha256(checked_path(name).read_bytes()).hexdigest() != digest:
            raise SystemExit(f"SHA256 mismatch: {name}")
    print(f"Verified hashes and complete manifest coverage for {len(entries)} release files.")


if __name__ == "__main__":
    main()
