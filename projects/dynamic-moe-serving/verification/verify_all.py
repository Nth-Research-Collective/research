#!/usr/bin/env python3
"""Reproduce the Dynamic MoE Serving formal and computational evidence."""

from __future__ import annotations

import hashlib
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parent
EXPECTED_TESTS = 24
EXPECTED_OUTPUTS = {
    "output/dynamic-moe-serving/positive-body-reduction-control.json": (
        "53c7ac33689b4cef22057fd1f9c040dab4e00a8aa13c5277b6a1b6e91e041a66"
    ),
    "output/dynamic-moe-serving/formal-reduction-audit.json": (
        "adcb13dad31d6fc688982068396e9733cf3d6f6444285f015cd0e6e1c1fde3f4"
    ),
}
TEST_MODULES = (
    "tests.test_bootstrap_dynamic_moe_sources",
    "tests.test_dynamic_moe_positive_body_eval",
    "tests.test_dynamic_moe_positive_body_formal",
    "tests.test_dynamic_moe_semantics_formal",
    "tests.test_dynamic_moe_lower_bound_formal",
    "tests.test_dynamic_moe_formal_eval",
)


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
    environment: dict[str, str] | None = None,
) -> str:
    rendered = " ".join(command)
    print(f"RUN: {rendered}", flush=True)
    process = subprocess.run(
        command,
        cwd=cwd,
        capture_output=True,
        text=True,
        timeout=1800,
        env={**os.environ, **(environment or {})},
    )
    output = process.stdout + process.stderr
    if output:
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
    for tool in ("bash", "curl", "git"):
        if shutil.which(tool) is None:
            raise ReproductionError(f"required tool is not on PATH: {tool}")
    if shutil.which("tectonic") is None:
        raise ReproductionError(
            "Tectonic is required to compile the paper: "
            "https://tectonic-typesetting.github.io/"
        )
    print("PASS: required command-line tools are available")


def verify_tests() -> None:
    output = run([sys.executable, "-m", "unittest", *TEST_MODULES])
    match = re.search(r"Ran (\d+) tests?", output)
    if match is None or int(match.group(1)) != EXPECTED_TESTS:
        observed = match.group(1) if match else "unknown"
        raise ReproductionError(
            f"expected {EXPECTED_TESTS} tests, observed {observed}"
        )
    if not re.search(r"^OK$", output, re.MULTILINE):
        raise ReproductionError("test runner did not report OK")
    print(f"PASS: all {EXPECTED_TESTS} tests passed")


def build_local_lean_modules() -> None:
    lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    if not Path(lake).is_file():
        raise ReproductionError("Lake was not installed by the Lean bootstrap")
    run(
        [lake, "build", "+LeanProject.DynamicMoeMain"],
        cwd=ROOT / "formal/lean_project",
        environment={"LAKE_JOBS": "1"},
    )
    print("PASS: local Dynamic MoE Lean modules built")


def reproduce_outputs(temporary: Path) -> None:
    generated = {
        "output/dynamic-moe-serving/positive-body-reduction-control.json": (
            temporary / "positive-body-reduction-control.json",
            [sys.executable, "-m", "evaluators.dynamic_moe_positive_body_eval"],
        ),
        "output/dynamic-moe-serving/formal-reduction-audit.json": (
            temporary / "formal-reduction-audit.json",
            [sys.executable, "-m", "evaluators.dynamic_moe_formal_eval"],
        ),
    }
    for relative, (fresh, command) in generated.items():
        run([*command, "--output", str(fresh)])
        expected_hash = EXPECTED_OUTPUTS[relative]
        canonical = ROOT / relative
        actual_hash = sha256(fresh)
        if actual_hash != expected_hash:
            raise ReproductionError(
                f"fresh output mismatch for {relative}: "
                f"expected {expected_hash}, got {actual_hash}"
            )
        if fresh.read_bytes() != canonical.read_bytes():
            raise ReproductionError(
                f"fresh output is not byte-identical to {relative}"
            )
        print(f"PASS: reproduced {relative} ({actual_hash})")


def compile_paper(temporary: Path) -> None:
    output = run(
        [
            "tectonic",
            "--keep-logs",
            "--outdir",
            str(temporary),
            str(ROOT / "paper/main.tex"),
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
    if match is None or int(match.group(1)) != 7:
        observed = match.group(1) if match else "unknown"
        raise ReproductionError(f"expected a seven-page paper, observed {observed}")
    warning_pattern = re.compile(
        r"^(?:warning:|LaTeX Warning:|Package \S+ Warning:|"
        r"Overfull \\|Underfull \\)",
        re.MULTILINE | re.IGNORECASE,
    )
    if warning_pattern.search(output) or warning_pattern.search(log_text):
        raise ReproductionError("paper compilation emitted a warning")
    print("PASS: paper compiled cleanly (7 pages)")


def main() -> int:
    try:
        verify_manifest()
        verify_tools()
        run([sys.executable, "scripts/bootstrap_dynamic_moe_sources.py"])
        run(["bash", "scripts/bootstrap_lean.sh"])
        build_local_lean_modules()
        verify_tests()
        with tempfile.TemporaryDirectory(prefix="dynamic-moe-replay-") as directory:
            temporary = Path(directory)
            reproduce_outputs(temporary)
            compile_paper(temporary)
        verify_manifest()
    except (OSError, ReproductionError, subprocess.SubprocessError) as error:
        print(f"BROKEN: {error}", file=sys.stderr)
        return 1
    print("PASS: Dynamic MoE Serving reproduction complete")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
