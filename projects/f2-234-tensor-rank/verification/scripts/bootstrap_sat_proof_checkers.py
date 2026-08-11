#!/usr/bin/env python3
"""Fetch and build pinned DRAT/LRAT proof checkers without silent replacement.

The source is pinned to marijnheule/drat-trim commit
2e3b2dc0ecf938addbd779d42877b6ed69d9a985. Source bytes are hash checked;
derived binaries are tied to their source hashes, compiler identity, flags, and
binary hashes in a local manifest under ``tmp/upstream/sat-proof-checkers``.
An existing mismatch fails loudly and is never rebuilt over in place.
"""

from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "tmp" / "upstream" / "sat-proof-checkers"
COMMIT = "2e3b2dc0ecf938addbd779d42877b6ed69d9a985"
RAW_BASE = f"https://raw.githubusercontent.com/marijnheule/drat-trim/{COMMIT}"
SOURCES = {
    "drat-trim.c": "d834b649f437e091597f5347f259b9f681087f89ca0844d0cee250a1a1a0c2ee",
    "lrat-check.c": "bf07c2ac96b9035da1ebcc578cb95e956a2b795629d613154cdb307f8a8f4a95",
}
BUILDS = {
    "drat-trim": {"source": "drat-trim.c", "flags": ["-std=c99", "-O2"]},
    "lrat-check": {
        "source": "lrat-check.c",
        "flags": ["-std=c99", "-DLONGTYPE", "-O2"],
    },
}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def ensure_source(path: Path, expected: str) -> str:
    if path.exists():
        actual = sha256(path)
        if actual != expected:
            raise RuntimeError(
                f"refusing to overwrite mismatching source {path}: "
                f"expected {expected}, got {actual}"
            )
        return "reused"
    curl = shutil.which("curl")
    if not curl:
        raise RuntimeError("curl not found on PATH")
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.part.{os.getpid()}")
    try:
        completed = subprocess.run(
            [
                curl,
                "--fail",
                "--location",
                "--silent",
                "--show-error",
                "--max-time",
                "600",
                "-o",
                str(temporary),
                f"{RAW_BASE}/{path.name}",
            ],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
        if completed.returncode != 0:
            raise RuntimeError(
                f"curl failed for {path.name}: "
                f"{(completed.stderr or completed.stdout).strip()}"
            )
        actual = sha256(temporary)
        if actual != expected:
            raise RuntimeError(
                f"downloaded source mismatch for {path.name}: "
                f"expected {expected}, got {actual}"
            )
        os.replace(temporary, path)
        return "fetched"
    finally:
        temporary.unlink(missing_ok=True)


def compiler_identity(compiler: str) -> str:
    completed = subprocess.run(
        [compiler, "--version"],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    if completed.returncode != 0:
        raise RuntimeError(f"compiler version check failed: {compiler}")
    return completed.stdout.splitlines()[0]


def verify_existing(manifest_path: Path, compiler: str, identity: str) -> bool:
    if not manifest_path.exists():
        if any((TARGET / name).exists() for name in BUILDS):
            raise RuntimeError("checker binaries exist without a build manifest")
        return False
    manifest = json.loads(manifest_path.read_text())
    expected_header = {
        "format": "sat-proof-checkers-v1",
        "upstream_commit": COMMIT,
        "compiler": compiler,
        "compiler_identity": identity,
        "sources": SOURCES,
    }
    for key, expected in expected_header.items():
        if manifest.get(key) != expected:
            raise RuntimeError(
                f"existing checker manifest mismatch for {key}: "
                f"expected {expected!r}, got {manifest.get(key)!r}"
            )
    for name, build in BUILDS.items():
        entry = manifest.get("binaries", {}).get(name)
        if not entry or entry.get("flags") != build["flags"]:
            raise RuntimeError(f"existing checker manifest mismatch for {name}")
        binary = TARGET / name
        if not binary.is_file():
            raise RuntimeError(f"manifest names missing checker binary: {binary}")
        actual = sha256(binary)
        if actual != entry.get("sha256"):
            raise RuntimeError(
                f"checker binary hash mismatch for {binary}: "
                f"expected {entry.get('sha256')}, got {actual}"
            )
    return True


def build() -> dict:
    source_status = {
        name: ensure_source(TARGET / name, expected)
        for name, expected in SOURCES.items()
    }
    compiler = shutil.which("cc")
    if not compiler:
        raise RuntimeError("C compiler 'cc' not found on PATH")
    identity = compiler_identity(compiler)
    manifest_path = TARGET / "manifest.json"
    if verify_existing(manifest_path, compiler, identity):
        manifest = json.loads(manifest_path.read_text())
        manifest["source_status"] = source_status
        return manifest

    temporary_binaries: dict[str, Path] = {}
    try:
        for name, build_spec in BUILDS.items():
            destination = TARGET / name
            if destination.exists():
                raise RuntimeError(f"refusing to overwrite checker binary: {destination}")
            temporary = TARGET / f".{name}.part.{os.getpid()}"
            command = [
                compiler,
                str(TARGET / build_spec["source"]),
                *build_spec["flags"],
                "-o",
                str(temporary),
            ]
            completed = subprocess.run(
                command,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                check=False,
            )
            if completed.returncode != 0:
                raise RuntimeError(
                    f"checker build failed ({' '.join(command)}):\n{completed.stdout}"
                )
            temporary.chmod(0o755)
            temporary_binaries[name] = temporary

        binaries = {
            name: {
                "source": BUILDS[name]["source"],
                "flags": BUILDS[name]["flags"],
                "sha256": sha256(path),
            }
            for name, path in temporary_binaries.items()
        }
        manifest = {
            "format": "sat-proof-checkers-v1",
            "upstream_commit": COMMIT,
            "compiler": compiler,
            "compiler_identity": identity,
            "sources": SOURCES,
            "binaries": binaries,
        }
        for name, temporary in temporary_binaries.items():
            os.replace(temporary, TARGET / name)
        temporary_manifest = TARGET / f".manifest.json.part.{os.getpid()}"
        temporary_manifest.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
        os.replace(temporary_manifest, manifest_path)
        manifest["source_status"] = source_status
        return manifest
    finally:
        for temporary in temporary_binaries.values():
            temporary.unlink(missing_ok=True)


def main() -> int:
    try:
        manifest = build()
    except Exception as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1
    for name, status in manifest.pop("source_status").items():
        print(f"{status}: {TARGET / name}")
    for name, entry in manifest["binaries"].items():
        print(f"ready: {TARGET / name}  sha256={entry['sha256']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
