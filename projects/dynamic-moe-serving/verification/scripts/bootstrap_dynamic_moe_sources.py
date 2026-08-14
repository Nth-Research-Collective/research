#!/usr/bin/env python3
"""Fetch and validate the two pinned sources used by the Dynamic MoE proof."""

from __future__ import annotations

import hashlib
import shutil
import ssl
import sys
import tarfile
import tempfile
import urllib.request
from dataclasses import dataclass
from pathlib import Path

try:
    import certifi
except ImportError:  # pragma: no cover
    certifi = None


ROOT = Path(__file__).resolve().parent.parent
SOURCE_CACHE = ROOT / "tmp" / "upstream" / "dynamic-moe-serving"


@dataclass(frozen=True)
class SourcePin:
    name: str
    url: str
    relative_path: str
    sha256: str
    member: str
    member_sha256: str

    @property
    def target(self) -> Path:
        return SOURCE_CACHE / self.relative_path


SOURCE_PINS = (
    SourcePin(
        name="Huang-Lou-Xiao Mixture-of-Experts Serving v1 source",
        url="https://arxiv.org/e-print/2607.17880v1",
        relative_path="2607.17880v1.tar",
        sha256="f6bdce7169c0ebb487488c4cb23d2b5f9fd48e804a54f8907fa727a699deadd1",
        member="main.tex",
        member_sha256="6eb838ea7cd7f12686851b98f7d31d682a69870a2266568e82bec8065b7e3134",
    ),
    SourcePin(
        name="Bhattacharya-Buchbinder-Levin-Saranurak Chasing Positive Bodies v2 source",
        url="https://arxiv.org/e-print/2304.01889v2",
        relative_path="2304.01889v2.tar",
        sha256="3ba3c5a27674b21fe239d32f193cb6bf8f68dc52db438f7d20e962620b0793a4",
        member="intro.tex",
        member_sha256="0dd945b8905fbcc83ad1a274f86c5a9ed91b64592f5eac23f6c67177f2878ff8",
    ),
)


class BootstrapError(RuntimeError):
    """A local or fetched source failed its immutable identity check."""


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def validate_existing_file(path: Path, expected_sha256: str) -> str:
    if not path.is_file():
        raise BootstrapError(f"expected a file at {path}")
    actual = sha256(path)
    if actual != expected_sha256:
        raise BootstrapError(
            f"existing source mismatch at {path}: expected {expected_sha256}, "
            f"got {actual}; refusing to overwrite it"
        )
    return actual


def validate_archive_member(pin: SourcePin) -> str:
    try:
        with tarfile.open(pin.target, "r:*") as archive:
            extracted = archive.extractfile(pin.member)
            if extracted is None:
                raise BootstrapError(f"{pin.member} is not a regular archive member")
            actual = hashlib.sha256(extracted.read()).hexdigest()
    except (KeyError, tarfile.TarError) as error:
        raise BootstrapError(f"invalid source archive {pin.target}: {error}") from error
    if actual != pin.member_sha256:
        raise BootstrapError(
            f"{pin.member} mismatch in {pin.target}: expected {pin.member_sha256}, got {actual}"
        )
    return actual


def ensure_source(pin: SourcePin) -> None:
    if pin.target.exists():
        actual = validate_existing_file(pin.target, pin.sha256)
        print(f"PASS: reused {pin.name} ({actual})")
    else:
        pin.target.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.NamedTemporaryFile(dir=pin.target.parent, delete=False) as handle:
            temporary = Path(handle.name)
            try:
                request = urllib.request.Request(
                    pin.url, headers={"User-Agent": "nth-research/1.0"}
                )
                context = ssl.create_default_context(
                    cafile=certifi.where() if certifi else None
                )
                with urllib.request.urlopen(request, timeout=120, context=context) as response:
                    shutil.copyfileobj(response, handle)
            except BaseException:
                temporary.unlink(missing_ok=True)
                raise
        actual = sha256(temporary)
        if actual != pin.sha256:
            temporary.unlink(missing_ok=True)
            raise BootstrapError(
                f"downloaded {pin.name} mismatch: expected {pin.sha256}, got {actual}"
            )
        temporary.replace(pin.target)
        print(f"PASS: fetched {pin.name} ({actual})")
    member_hash = validate_archive_member(pin)
    print(f"PASS: pinned {pin.member} present ({member_hash})")


def main() -> int:
    try:
        for pin in SOURCE_PINS:
            ensure_source(pin)
    except (BootstrapError, OSError) as error:
        print(f"BROKEN: {error}", file=sys.stderr)
        return 1
    print("PASS: pinned Dynamic MoE sources are ready")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
