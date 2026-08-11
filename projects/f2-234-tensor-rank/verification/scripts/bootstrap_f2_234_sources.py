#!/usr/bin/env python3
"""Pin, cache, and provenance-check public exact-rank sources for
the 2x3-by-3x4 matrix multiplication tensor over F2.

The raw source is the public AlphaTensor repository file
``algorithms/factorizations_f2.npz`` (blob 74ca8d8d9db45e59d01a2db8cd974896b6497587,
SHA-256 70f09f349d8d2874ef0e0e089459c7320f5aa3eef277df5ffa67f573709db2da).  The
file is cached only under the ignored directory ``tmp/upstream/f2-234-tensor-rank/``
and an existing file whose hash does not match the pin is never overwritten.

AlphaTensor stores decompositions of the symmetrized tensor (A, B) -> (A*B)^T
with the output-dual factor indexed k*a+i.  This script extracts the key
``2,3,4``, reindexes each W column to the canonical output-dual row-major order
(w_canonical[i*4+k] = w_upstream[k*2+i]), and compares the reconstructed
canonical terms against the tracked artifact
``knowledge/data/f2_234_rank20_alphatensor.json`` so that factor order and
indexing convention are provenance-checked.

The same ignored cache also receives Wang's pinned verifier source commit,
the real Git-LFS payloads for the n324 certificate, and a pinned Bazelisk
binary. This avoids mutable git state and a system-wide git-lfs/Bazel install.
"""

from __future__ import annotations

import hashlib
import shutil
import ssl
import sys
import tarfile
import tempfile
import urllib.request
from pathlib import Path

import numpy as np

try:
    import certifi
except ImportError:  # pragma: no cover - the system trust store may work.
    certifi = None


ROOT = Path(__file__).resolve().parent.parent
SCHEMA = "f2-234-tensor-rank-decomposition-v1"
SOURCE_CACHE = ROOT / "tmp" / "upstream" / "f2-234-tensor-rank"
NPZ_NAME = "factorizations_f2.npz"
NPZ_PATH = SOURCE_CACHE / NPZ_NAME

UPSTREAM_URL = (
    "https://raw.githubusercontent.com/google-deepmind/alphatensor/"
    "main/algorithms/factorizations_f2.npz"
)
UPSTREAM_BLOB_SHA = "74ca8d8d9db45e59d01a2db8cd974896b6497587"
UPSTREAM_SHA256 = "70f09f349d8d2874ef0e0e089459c7320f5aa3eef277df5ffa67f573709db2da"
NPZ_KEY = "2,3,4"
EXPECTED_SHAPES = ((6, 20), (12, 20), (8, 20))
ARTIFACT_PATH = ROOT / "knowledge" / "data" / "f2_234_rank20_alphatensor.json"

WANG_COMMIT = "0ab0562f2fb5430e3ce16035e5882720b5bb613b"
WANG_ARCHIVE_NAME = f"wang-{WANG_COMMIT}.tar.gz"
WANG_ARCHIVE_PATH = SOURCE_CACHE / WANG_ARCHIVE_NAME
WANG_ARCHIVE_URL = (
    "https://github.com/wcgbg/tensor-rank-lower-bound/archive/"
    f"{WANG_COMMIT}.tar.gz"
)
WANG_ARCHIVE_SHA256 = "6a71199edb405ff500db770ed872df9fa38845ef852add9bb8e3e48d7fffa6df"
WANG_ARCHIVE_ROOT = f"tensor-rank-lower-bound-{WANG_COMMIT}"
WANG_TREE = SOURCE_CACHE / WANG_ARCHIVE_ROOT
WANG_CERT_NAME = "cert_matrix_q02_n324.pb.txt"
WANG_BTP_NAME = "cert_matrix_q02_n324.btp"
WANG_CERT_PATH = SOURCE_CACHE / WANG_CERT_NAME
WANG_BTP_PATH = SOURCE_CACHE / WANG_BTP_NAME
WANG_MEDIA_ROOT = (
    "https://media.githubusercontent.com/media/wcgbg/tensor-rank-lower-bound/"
    f"{WANG_COMMIT}/certs/matrix"
)
WANG_CERT_URL = f"{WANG_MEDIA_ROOT}/{WANG_CERT_NAME}"
WANG_BTP_URL = f"{WANG_MEDIA_ROOT}/{WANG_BTP_NAME}"
WANG_CERT_SHA256 = "b1926bac436850d6c43c1c909a4bdfd9c84a073ed14b6359635944dfd694316d"
WANG_BTP_SHA256 = "875f7ce52ad6afc9ffbab70269cbaca25cdf205174da2c8e2edec2af5aff2e4d"

BAZELISK_VERSION = "1.29.0"
BAZELISK_NAME = f"bazelisk-darwin-arm64-v{BAZELISK_VERSION}"
BAZELISK_PATH = SOURCE_CACHE / BAZELISK_NAME
BAZELISK_URL = (
    "https://github.com/bazelbuild/bazelisk/releases/download/"
    f"v{BAZELISK_VERSION}/bazelisk-darwin-arm64"
)
BAZELISK_SHA256 = "cee851f726789227d5561004e9904a52be45c3efb56f8b38b6993d6adbaa0409"


class BootstrapError(RuntimeError):
    """A local or fetched source failed its exact identity or content check."""


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


def ensure_pinned_file(path: Path, url: str, expected_sha256: str, label: str) -> None:
    if path.exists():
        actual = validate_existing_file(path, expected_sha256)
        print(f"PASS: reused pinned {label} ({actual})")
        return

    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(dir=path.parent, delete=False) as handle:
        temporary = Path(handle.name)
        try:
            request = urllib.request.Request(
                url, headers={"User-Agent": "nth-research/1.0"}
            )
            context = ssl.create_default_context(
                cafile=certifi.where() if certifi else None
            )
            with urllib.request.urlopen(
                request, timeout=120, context=context
            ) as response:
                shutil.copyfileobj(response, handle)
        except BaseException:
            temporary.unlink(missing_ok=True)
            raise

    actual = sha256(temporary)
    if actual != expected_sha256:
        temporary.unlink(missing_ok=True)
        raise BootstrapError(
            f"downloaded {label} mismatch: expected {expected_sha256}, got {actual}"
        )
    temporary.replace(path)
    print(f"PASS: fetched pinned {label} ({actual})")


def ensure_source() -> None:
    ensure_pinned_file(NPZ_PATH, UPSTREAM_URL, UPSTREAM_SHA256, NPZ_NAME)


def validate_wang_archive(path: Path) -> str:
    """Check the pinned archive has the expected immutable source root."""

    required = (
        f"{WANG_ARCHIVE_ROOT}/.bazeliskrc",
        f"{WANG_ARCHIVE_ROOT}/run.py",
        f"{WANG_ARCHIVE_ROOT}/verifier/README.md",
        f"{WANG_ARCHIVE_ROOT}/verifier/verifier_main.cc",
    )
    try:
        with tarfile.open(path, "r:gz") as archive:
            names = set(archive.getnames())
            missing = [name for name in required if name not in names]
            if missing:
                raise BootstrapError(f"Wang source archive is missing {missing}")
            bazelisk = archive.extractfile(required[0])
            if bazelisk is None:
                raise BootstrapError("Wang .bazeliskrc is not a regular file")
            bazel_version = bazelisk.read().decode().strip()
    except (OSError, tarfile.TarError, UnicodeDecodeError) as error:
        raise BootstrapError(f"invalid Wang source archive {path}: {error}") from error
    if bazel_version != "USE_BAZEL_VERSION=8.3.1":
        raise BootstrapError(f"unexpected Wang Bazel pin {bazel_version!r}")
    return WANG_ARCHIVE_ROOT


def validate_wang_tree(path: Path) -> None:
    required = (path / "run.py", path / "verifier" / "verifier_main.cc")
    missing = [str(item) for item in required if not item.is_file()]
    if missing:
        raise BootstrapError(f"prepared Wang source tree is missing {missing}")
    validate_existing_file(
        path / "certs" / "matrix" / WANG_CERT_NAME, WANG_CERT_SHA256
    )
    validate_existing_file(
        path / "certs" / "matrix" / WANG_BTP_NAME, WANG_BTP_SHA256
    )


def prepare_wang_tree() -> None:
    """Prepare the pinned source tree with real LFS payloads, without git-lfs."""

    validate_wang_archive(WANG_ARCHIVE_PATH)
    if WANG_TREE.exists():
        validate_wang_tree(WANG_TREE)
        print(f"PASS: reused prepared Wang source tree ({WANG_COMMIT})")
        return

    temporary_root = Path(tempfile.mkdtemp(dir=SOURCE_CACHE, prefix="wang-extract-"))
    try:
        with tarfile.open(WANG_ARCHIVE_PATH, "r:gz") as archive:
            archive.extractall(temporary_root, filter="data")
        extracted = temporary_root / WANG_ARCHIVE_ROOT
        if not extracted.is_dir():
            raise BootstrapError(
                f"Wang archive did not produce expected root {WANG_ARCHIVE_ROOT}"
            )
        cert_dir = extracted / "certs" / "matrix"
        cert_dir.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(WANG_CERT_PATH, cert_dir / WANG_CERT_NAME)
        shutil.copyfile(WANG_BTP_PATH, cert_dir / WANG_BTP_NAME)
        validate_wang_tree(extracted)
        extracted.replace(WANG_TREE)
    except BaseException:
        shutil.rmtree(temporary_root, ignore_errors=True)
        raise
    shutil.rmtree(temporary_root, ignore_errors=True)
    print(f"PASS: prepared Wang source tree with exact n324 LFS payloads ({WANG_COMMIT})")


def ensure_wang_sources() -> None:
    ensure_pinned_file(
        WANG_ARCHIVE_PATH,
        WANG_ARCHIVE_URL,
        WANG_ARCHIVE_SHA256,
        "Wang source archive",
    )
    ensure_pinned_file(
        WANG_CERT_PATH, WANG_CERT_URL, WANG_CERT_SHA256, WANG_CERT_NAME
    )
    ensure_pinned_file(
        WANG_BTP_PATH, WANG_BTP_URL, WANG_BTP_SHA256, WANG_BTP_NAME
    )
    ensure_pinned_file(
        BAZELISK_PATH, BAZELISK_URL, BAZELISK_SHA256, BAZELISK_NAME
    )
    BAZELISK_PATH.chmod(0o755)
    prepare_wang_tree()


def canonical_terms_from_npz(path: Path) -> list[dict]:
    """Return the canonical 20 u/v/w terms for the ``2,3,4`` key.

    The stored W factor indexes the symmetrized output (k*a+i); each column is
    reindexed to canonical output-dual row-major order
    w_canonical[i*4+k] = w_upstream[k*2+i].
    """

    try:
        loaded = np.load(path, allow_pickle=True)
        if NPZ_KEY not in loaded.files:
            raise BootstrapError(f"key {NPZ_KEY!r} missing from {path}")
        u, v, w = loaded[NPZ_KEY]
    except (OSError, ValueError) as error:
        raise BootstrapError(f"cannot read {path}: {error}") from error

    shapes = (tuple(int(value) for value in u.shape),
              tuple(int(value) for value in v.shape),
              tuple(int(value) for value in w.shape))
    if shapes != EXPECTED_SHAPES:
        raise BootstrapError(
            f"key {NPZ_KEY!r} shapes {shapes} do not match {EXPECTED_SHAPES}"
        )
    for name, array in (("u", u), ("v", v), ("w", w)):
        if array.dtype.kind not in "iu" or set(array.ravel().tolist()) - {0, 1}:
            raise BootstrapError(f"factor {name} is not binary")

    w_canonical = w.T.reshape((20, 4, 2)).transpose(0, 2, 1).reshape((20, 8)).T
    terms: list[dict] = []
    for rank in range(20):
        triple = (
            tuple(int(value) for value in u[:, rank]),
            tuple(int(value) for value in v[:, rank]),
            tuple(int(value) for value in w_canonical[:, rank]),
        )
        if not any(triple[0]) or not any(triple[1]) or not any(triple[2]):
            raise BootstrapError(f"term {rank} contains a zero factor vector")
        terms.append({"u": list(triple[0]), "v": list(triple[1]), "w": list(triple[2])})
    if len({(tuple(term["u"]), tuple(term["v"]), tuple(term["w"])) for term in terms}) != 20:
        raise BootstrapError("extracted terms contain a duplicate full term")
    return terms


def terms_match_artifact(terms: list[dict], artifact: dict) -> None:
    """Compare reconstructed canonical terms against the tracked artifact."""

    expected_metadata = {
        "schema": SCHEMA,
        "field": "F2",
        "format": "2x3-by-3x4",
    }
    for key, expected in expected_metadata.items():
        if artifact.get(key) != expected:
            raise BootstrapError(
                f"artifact {key} {artifact.get(key)!r} does not match {expected!r}"
            )
    source = artifact.get("primary_source")
    if not isinstance(source, dict):
        raise BootstrapError("artifact primary_source must be an object")
    expected_source = {
        "raw_url": UPSTREAM_URL,
        "blob_sha": UPSTREAM_BLOB_SHA,
        "file_sha256": UPSTREAM_SHA256,
        "npz_key": NPZ_KEY,
        "factor_array_shapes": [list(shape) for shape in EXPECTED_SHAPES],
    }
    for key, expected in expected_source.items():
        if source.get(key) != expected:
            raise BootstrapError(
                f"artifact primary_source.{key} {source.get(key)!r} "
                f"does not match {expected!r}"
            )
    if artifact.get("declared_rank") != 20:
        raise BootstrapError(
            f"artifact declared rank {artifact.get('declared_rank')!r} is not 20"
        )
    tracked = artifact.get("terms")
    if not isinstance(tracked, list) or len(tracked) != len(terms):
        raise BootstrapError(
            f"artifact terms do not match: expected {len(terms)}, got "
            f"{len(tracked) if isinstance(tracked, list) else type(tracked).__name__}"
        )
    for index, (extracted, recorded) in enumerate(zip(terms, tracked, strict=True)):
        if extracted != recorded:
            for name in ("u", "v", "w"):
                if extracted[name] != recorded.get(name):
                    raise BootstrapError(
                        f"artifact term {index} factor {name} differs from "
                        f"the pinned source reconstruction"
                    )
            raise BootstrapError(f"artifact term {index} differs from the pinned source")
    print(f"PASS: canonical terms match the tracked artifact ({len(terms)} terms)")


def main() -> int:
    try:
        ensure_source()
        terms = canonical_terms_from_npz(NPZ_PATH)
        with ARTIFACT_PATH.open() as handle:
            import json

            artifact = json.load(handle)
        terms_match_artifact(terms, artifact)
        ensure_wang_sources()
    except (BootstrapError, OSError) as error:
        print(f"BROKEN: {error}", file=sys.stderr)
        return 1
    print("PASS: pinned F2 <2,3,4> upper- and lower-bound sources are ready")
    print(f"Wang replay tree: {WANG_TREE}")
    print(f"Pinned Bazelisk: {BAZELISK_PATH}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
