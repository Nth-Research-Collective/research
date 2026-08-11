#!/usr/bin/env python3
"""Fetch the DRAT/LRAT proof pair for the F2 <2,3,4> profile lemma.

This public mirror ships without the two large proof files
(``proof.drat`` at 191 MB and ``proof.lrat`` at 279 MB) because both exceed
GitHub's per-file push limit. They are refetched here from the permanent
Zenodo record before ``verify_all.py`` replays them with ``drat-trim`` and
``lrat-check``.

If both files already exist locally with the correct hashes, this step is a
no-op. Otherwise it downloads the full frozen reproducibility archive from
Zenodo (the only place these two files are hosted), hash-checks the archive,
extracts just the two proof files from it, and hash-checks each extracted
file before letting the rest of the verifier proceed. Any hash mismatch is a
hard failure — there is no silent fallback.
"""

from __future__ import annotations

import hashlib
import shutil
import ssl
import sys
import tempfile
import urllib.request
import zipfile
from pathlib import Path

try:
    import certifi
except ImportError:  # pragma: no cover - the system trust store may work.
    certifi = None


ROOT = Path(__file__).resolve().parent.parent
PROFILE_ORBITS_DIR = ROOT / "output" / "f2-234-tensor-rank" / "profile-orbits"
DRAT_PATH = PROFILE_ORBITS_DIR / "proof.drat"
LRAT_PATH = PROFILE_ORBITS_DIR / "proof.lrat"

DRAT_SHA256 = "55fee5806b2e7fe6f4166ae06bd9125bf3f06cc3dfa3cd7722e77091bff87343"
LRAT_SHA256 = "adce8ddb664eaedafa2b3599822aacddd0800d1721c3edcdf984ffbd8d4f551e"

ZENODO_RECORD_ID = "21895176"
ZENODO_ARCHIVE_NAME = "f2-234-tensor-rank-reproducibility-v1.zip"
ZENODO_ARCHIVE_URL = (
    f"https://zenodo.org/api/records/{ZENODO_RECORD_ID}/files/"
    f"{ZENODO_ARCHIVE_NAME}/content"
)
ZENODO_ARCHIVE_SHA256 = (
    "0953e19648c95ca00f39f4fc6a631060c4430ed2c6352f434b086c28e1757a74"
)
ARCHIVE_ROOT = "f2-234-tensor-rank-reproducibility-v1"
ZIP_MEMBER_DRAT = f"{ARCHIVE_ROOT}/output/f2-234-tensor-rank/profile-orbits/proof.drat"
ZIP_MEMBER_LRAT = f"{ARCHIVE_ROOT}/output/f2-234-tensor-rank/profile-orbits/proof.lrat"


class ProofFetchError(RuntimeError):
    """The proof pair could not be obtained or verified."""


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def already_present() -> bool:
    if not DRAT_PATH.is_file() or not LRAT_PATH.is_file():
        return False
    drat_actual = sha256(DRAT_PATH)
    lrat_actual = sha256(LRAT_PATH)
    if drat_actual != DRAT_SHA256 or lrat_actual != LRAT_SHA256:
        raise ProofFetchError(
            "local proof.drat/proof.lrat exist but do not match the pinned "
            f"hashes (drat={drat_actual}, lrat={lrat_actual}); refusing to "
            "overwrite in place, remove them and rerun"
        )
    return True


def download_archive(destination: Path) -> None:
    request = urllib.request.Request(
        ZENODO_ARCHIVE_URL, headers={"User-Agent": "nth-research/1.0"}
    )
    context = ssl.create_default_context(cafile=certifi.where() if certifi else None)
    with urllib.request.urlopen(request, timeout=1800, context=context) as response:
        with destination.open("wb") as handle:
            shutil.copyfileobj(response, handle)


def extract_member(archive: zipfile.ZipFile, member: str, destination: Path) -> None:
    destination.parent.mkdir(parents=True, exist_ok=True)
    with archive.open(member) as source, tempfile.NamedTemporaryFile(
        dir=destination.parent, delete=False
    ) as handle:
        temporary = Path(handle.name)
        try:
            shutil.copyfileobj(source, handle)
        except BaseException:
            temporary.unlink(missing_ok=True)
            raise
    temporary.replace(destination)


def fetch_proof_pair() -> None:
    with tempfile.TemporaryDirectory(prefix="f2-234-proof-fetch-") as directory:
        archive_path = Path(directory) / ZENODO_ARCHIVE_NAME
        print(f"Downloading {ZENODO_ARCHIVE_URL} (~473 MB, this is the full frozen archive)")
        download_archive(archive_path)
        actual_archive_sha = sha256(archive_path)
        if actual_archive_sha != ZENODO_ARCHIVE_SHA256:
            raise ProofFetchError(
                f"downloaded archive mismatch: expected {ZENODO_ARCHIVE_SHA256}, "
                f"got {actual_archive_sha}"
            )
        print(f"PASS: fetched archive matches pinned hash ({actual_archive_sha})")

        with zipfile.ZipFile(archive_path) as archive:
            names = set(archive.namelist())
            if ZIP_MEMBER_DRAT not in names or ZIP_MEMBER_LRAT not in names:
                raise ProofFetchError(
                    "fetched archive is missing the expected proof-pair members"
                )
            extract_member(archive, ZIP_MEMBER_DRAT, DRAT_PATH)
            extract_member(archive, ZIP_MEMBER_LRAT, LRAT_PATH)

    drat_actual = sha256(DRAT_PATH)
    if drat_actual != DRAT_SHA256:
        DRAT_PATH.unlink(missing_ok=True)
        raise ProofFetchError(
            f"extracted proof.drat mismatch: expected {DRAT_SHA256}, got {drat_actual}"
        )
    lrat_actual = sha256(LRAT_PATH)
    if lrat_actual != LRAT_SHA256:
        LRAT_PATH.unlink(missing_ok=True)
        raise ProofFetchError(
            f"extracted proof.lrat mismatch: expected {LRAT_SHA256}, got {lrat_actual}"
        )
    print(f"PASS: extracted proof.drat matches pinned hash ({drat_actual})")
    print(f"PASS: extracted proof.lrat matches pinned hash ({lrat_actual})")


def main() -> int:
    try:
        if already_present():
            print("PASS: reused local proof.drat/proof.lrat (pinned hashes matched)")
            return 0
        fetch_proof_pair()
    except (ProofFetchError, OSError, zipfile.BadZipFile) as error:
        print(f"BROKEN: {error}", file=sys.stderr)
        return 1
    print("PASS: DRAT/LRAT proof pair is ready")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
