"""Replay and compare the exact quartic BPR certificate."""
from __future__ import annotations

import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent
EXPECTED_VERIFIER_SHA256 = (
    "8d4533608a622e7190bca98cc9593d4e6f80bc418d707a93dc77842668afdce2"
)
EXPECTED_CERTIFICATE_SHA256 = (
    "1234e8feb90a19dd7dfd29f82cf92af5cd32ec4141e82d1a4f4d4843c05b7eb6"
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    verifier = ROOT / "verify_counterexample.py"
    certificate = ROOT / "certificate.json"
    if sha256(verifier) != EXPECTED_VERIFIER_SHA256:
        raise SystemExit("verifier hash mismatch")
    if sha256(certificate) != EXPECTED_CERTIFICATE_SHA256:
        raise SystemExit("certificate hash mismatch")

    with tempfile.TemporaryDirectory(prefix="quartic-bpr-") as directory:
        replay = Path(directory) / "certificate.json"
        completed = subprocess.run(
            [sys.executable, str(verifier), "--output", str(replay)],
            check=False,
            capture_output=True,
            text=True,
        )
        if completed.returncode != 0:
            raise SystemExit(completed.stdout + completed.stderr)
        if replay.read_bytes() != certificate.read_bytes():
            raise SystemExit("fresh replay differs from the published certificate")

    print("PASS: exact certificate reproduced byte-for-byte")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
