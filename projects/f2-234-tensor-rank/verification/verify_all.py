#!/usr/bin/env python3
"""Reproduce the exact F2 rank of the <2,3,4> matrix multiplication tensor.

This driver runs from the root of the extracted reproducibility archive. It
checks every packaged file against ``MANIFEST.sha256``, fetches and hash-checks
the pinned public sources (including refetching the 191 MB/279 MB DRAT/LRAT
proof pair from the permanent Zenodo record, since this public mirror ships
without those two files), freshly replays the finite rank-19 exclusion
certificate (including a DRAT and LRAT proof replay of the profile lemma),
re-runs the 35 unit tests and the exact upper-bound controls, and recompiles
the five-page paper.

``MANIFEST.sha256`` intentionally does not list ``proof.drat``/``proof.lrat``:
those two files are fetched at run time by ``scripts/fetch_proof_pair.py``,
which hash-checks them independently against the same pinned hashes recorded
in the original package. The manifest check that runs before and after this
script covers every file that ships with this mirror.

The archive layout mirrors the source repository, so every packaged module
resolves ``ROOT`` to the extracted archive root and reads its data through the
same repository-relative paths used during the original campaign.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parent
EXPECTED_TESTS = 35
TEST_MODULES = (
    "tests.test_f2_234_tight_row_restriction",
    "tests.test_f2_234_profile_orbits",
    "tests.test_f2_234_tensor_rank_eval",
)
EXACT_CERTIFICATE = (
    "output/f2-234-tensor-rank/exact-rank20-certificate-v2.json"
)
EXPECTED_EXACT_RESULT = {
    "verdict": "EXACT_RANK_VERIFIED",
    "rank": 20,
    "field": "F2",
    "format": "2x3-by-3x4",
    "excluded_rank19_profiles": 252,
    "upper_terms": 20,
}
REPLAY_TIMEOUT_SECONDS = 3600


class ReproductionError(RuntimeError):
    """A required reproduction check failed."""


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def run(
    command: list[str],
    *,
    cwd: Path = ROOT,
    timeout: int = 1800,
    capture: bool = True,
) -> str:
    rendered = " ".join(command)
    print(f"RUN: {rendered}", flush=True)
    process = subprocess.run(
        command,
        cwd=cwd,
        capture_output=capture,
        text=True,
        timeout=timeout,
        env={**os.environ, "PYTHONPATH": str(ROOT)},
    )
    output = (process.stdout or "") + (process.stderr or "")
    if capture and output:
        print(output, end="" if output.endswith("\n") else "\n")
    if process.returncode != 0:
        raise ReproductionError(
            f"command failed with exit code {process.returncode}: {rendered}"
        )
    return output


def verify_manifest() -> None:
    manifest = ROOT / "MANIFEST.sha256"
    if not manifest.is_file():
        raise ReproductionError("MANIFEST.sha256 is missing")
    seen: set[str] = set()
    for line_number, line in enumerate(
        manifest.read_text(encoding="utf-8").splitlines(), start=1
    ):
        match = re.fullmatch(r"([0-9a-f]{64})  (.+)", line)
        if match is None:
            raise ReproductionError(f"invalid manifest line {line_number}")
        expected, relative = match.groups()
        path = Path(relative)
        if path.is_absolute() or ".." in path.parts or relative in seen:
            raise ReproductionError(f"unsafe or duplicate manifest path: {relative}")
        seen.add(relative)
        target = ROOT / path
        if not target.is_file():
            raise ReproductionError(f"manifest file is missing: {relative}")
        actual = sha256(target)
        if actual != expected:
            raise ReproductionError(
                f"manifest mismatch for {relative}: expected {expected}, got {actual}"
            )
    print(f"PASS: manifest verified ({len(seen)} files)")


def verify_tools() -> None:
    if sys.version_info < (3, 10):
        raise ReproductionError("Python 3.10 or newer is required")
    try:
        import numpy  # noqa: F401
    except ImportError as error:
        raise ReproductionError("NumPy is required to read the upstream witness") from error
    for tool in ("bash", "curl", "git", "make"):
        if shutil.which(tool) is None:
            raise ReproductionError(f"required tool is not on PATH: {tool}")
    if shutil.which("cc") is None and shutil.which("gcc") is None:
        raise ReproductionError("a C compiler (cc or gcc) is required for the checkers")
    if shutil.which("tectonic") is None:
        raise ReproductionError(
            "Tectonic is required to compile the paper: "
            "https://tectonic-typesetting.github.io/"
        )
    print("PASS: required command-line tools are available")


def bootstrap_sources() -> None:
    run([sys.executable, "scripts/bootstrap_f2_234_sources.py"], timeout=600)
    run([sys.executable, "scripts/bootstrap_sat_proof_checkers.py"], timeout=900)
    # This public mirror ships without the 191 MB proof.drat and 279 MB
    # proof.lrat files (both exceed GitHub's per-file push limit). Fetch and
    # hash-check them from the permanent Zenodo record before the DRAT/LRAT
    # replay in verify_exact_rank() needs them.
    run([sys.executable, "scripts/fetch_proof_pair.py"], timeout=2400)
    print("PASS: pinned upstream sources, proof checkers, and proof pair are ready")


def verify_exact_rank() -> None:
    output = run(
        [
            sys.executable,
            "-m",
            "experiments.f2_234_tight_row_restriction",
            "verify-exact-rank20",
            "--artifact",
            EXACT_CERTIFICATE,
            "--timeout",
            str(REPLAY_TIMEOUT_SECONDS),
        ],
        timeout=REPLAY_TIMEOUT_SECONDS + 120,
    )
    try:
        result = json.loads(output[output.index("{"): output.rindex("}") + 1])
    except (ValueError, json.JSONDecodeError) as error:
        raise ReproductionError("exact-rank verifier did not emit JSON") from error
    if result != EXPECTED_EXACT_RESULT:
        raise ReproductionError(
            f"exact-rank result mismatch: {json.dumps(result, sort_keys=True)}"
        )
    print("PASS: R_F2(<2,3,4>) = 20 replayed (rank-19 excluded, rank-20 witness verified)")


def verify_controls() -> None:
    run([sys.executable, "-m", "evaluators.f2_234_tensor_rank_eval", "verify-controls"])
    print("PASS: exact upper-bound evaluator controls passed")


def verify_tests() -> None:
    output = run([sys.executable, "-m", "unittest", *TEST_MODULES])
    match = re.search(r"Ran (\d+) tests?", output)
    if match is None or int(match.group(1)) != EXPECTED_TESTS:
        observed = match.group(1) if match else "unknown"
        raise ReproductionError(f"expected {EXPECTED_TESTS} tests, observed {observed}")
    if not re.search(r"^OK$", output, re.MULTILINE):
        raise ReproductionError("test runner did not report OK")
    print(f"PASS: all {EXPECTED_TESTS} tests passed")


def compile_paper(temporary: Path) -> None:
    output = run(
        [
            "tectonic",
            "--keep-logs",
            "--outdir",
            str(temporary),
            str(ROOT / "submission/f2-234-tensor-rank/main.tex"),
        ]
    )
    pdf = temporary / "main.pdf"
    log = temporary / "main.log"
    if not pdf.is_file() or pdf.stat().st_size == 0:
        raise ReproductionError("Tectonic did not produce main.pdf")
    if not log.is_file():
        raise ReproductionError("Tectonic did not retain main.log")
    log_text = log.read_text(encoding="utf-8", errors="replace")
    match = re.search(r"Output written on .+? \((\d+) pages?[,)]", log_text)
    if match is None or int(match.group(1)) != 5:
        observed = match.group(1) if match else "unknown"
        raise ReproductionError(f"expected a five-page paper, observed {observed}")
    print("PASS: paper compiled (5 pages)")


def main() -> int:
    try:
        verify_manifest()
        verify_tools()
        bootstrap_sources()
        verify_exact_rank()
        verify_controls()
        verify_tests()
        with tempfile.TemporaryDirectory(prefix="f2-234-replay-") as directory:
            compile_paper(Path(directory))
        verify_manifest()
    except (OSError, ReproductionError, subprocess.SubprocessError) as error:
        print(f"BROKEN: {error}", file=sys.stderr)
        return 1
    print("PASS: F2 <2,3,4> exact-rank reproduction complete")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
