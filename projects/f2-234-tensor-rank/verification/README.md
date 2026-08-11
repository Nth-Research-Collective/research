# Exact F2 rank of the 2x3-by-3x4 matrix multiplication tensor

This package reproduces the evidence for the result

> R_{F2}(<2,3,4>) = 20,

the exact rank of the 2x3-by-3x4 matrix multiplication tensor over the field
with two elements.

## Verify

On macOS or Linux, from this directory:

```bash
pip install -r requirements.txt
python3 verify_all.py
```

The first run needs internet access to download the pinned public sources. It
also requires `bash`, `curl`, `git`, `make`, a C compiler (`cc` or `gcc`), and
[Tectonic](https://tectonic-typesetting.github.io/) on `PATH`, plus Python 3.10
or newer.

This public mirror ships without `proof.drat` (191 MB) and `proof.lrat`
(279 MB) — both exceed GitHub's per-file push limit. `verify_all.py` fetches
them automatically from the permanent Zenodo record before replaying them, and
hash-checks the fetched archive and each extracted file against the pinned
hashes below. That first fetch downloads the full ~473 MB frozen archive, so
it can take a few minutes.

`requirements.txt` pins `python-sat==1.8.dev24`. That pin is load-bearing: the
replay regenerates the profile CNF with PySAT's `CardEnc` encoding and compares
it byte for byte against the packaged CNF, so a different PySAT build can change
the clause encoding and fail the check.

The verifier:

1. checks every packaged file against `MANIFEST.sha256`;
2. downloads and hash-checks the pinned upstream sources (the AlphaTensor F2
   factorization file for the upper bound, and Wang's tensor-rank-lower-bound
   verifier source with the pinned `n324` certificate payloads);
3. fetches and builds the pinned DRAT and LRAT proof checkers from source, and
   fetches the 191 MB/279 MB DRAT/LRAT proof pair from the permanent Zenodo
   record (not packaged in this mirror — see above);
4. freshly replays the exact rank certificate, which
   - recomputes the full 252-profile census and all rank-19 profile
     exclusions in Python,
   - replays the DRAT and LRAT proof of the "at most one rank-two U factor"
     profile lemma with `drat-trim` and `lrat-check` over the fetched
     191 MB / 279 MB proof pair,
   - hash-checks the pinned Wang `n324` lower-bound certificate inputs against
     the pinned Linux acceptance log, and
   - verifies the explicit 20-term upper-bound decomposition against all 576
     tensor coefficients;
5. runs the exact upper-bound evaluator controls;
6. runs the 35 unit tests; and
7. recompiles the five-page paper from `submission/f2-234-tensor-rank/main.tex`.

A successful run ends with:

```text
PASS: F2 <2,3,4> exact-rank reproduction complete
```

## Certified artifacts

- Exact-rank certificate:
  `output/f2-234-tensor-rank/exact-rank20-certificate-v2.json`
- Profile lemma DRAT proof SHA-256:
  `55fee5806b2e7fe6f4166ae06bd9125bf3f06cc3dfa3cd7722e77091bff87343`
- Profile lemma LRAT proof SHA-256:
  `adce8ddb664eaedafa2b3599822aacddd0800d1721c3edcdf984ffbd8d4f551e`
- Profile lemma CNF SHA-256:
  `584916d170bc4372e0d114b6589f9363141d5864d5925c0f926b1ca9184db4e7`
- Paper source SHA-256:
  `236fbf02fea971662c796d23ec0368cebf4be3c5b0cbb1f60feb6a1435a78c96`
- Paper PDF SHA-256:
  `3eb9879f8ce647407659e233f42c56c1238af03ba8a3e9bb0aa86596c8ed8a07`

## Proof structure

The rank is pinned from both sides.

- **Upper bound (rank <= 20).** An explicit 20-term F2 decomposition, extracted
  and reindexed from the public AlphaTensor `factorizations_f2.npz` file and
  tracked as `knowledge/data/f2_234_rank20_alphatensor.json`. The verifier
  reconstructs it from the pinned upstream file and checks all 576 coefficients.
- **Lower bound (rank >= 20, i.e. rank 19 is impossible).** A finite exclusion
  of every legal rank-19 support profile. The 252-profile census and the
  case analysis for all four symmetry orbits are recomputed in Python; the
  structural claim that at most one U factor can have rank two is discharged by
  a machine-checkable DRAT/LRAT proof; and the residual arithmetic obstruction
  uses Wang's independently published tensor-rank lower-bound verifier.

## Provenance boundary for the Wang lower-bound input

One component of the lower bound, Wang's `n324` certificate, is a Bazel build
that runs on Linux. It is not re-executed on the replay machine. Instead this
package pins the exact certificate inputs by SHA-256 and ships the full Linux
verifier acceptance log
(`output/f2-234-tensor-rank/wang-n324-linux-full.log`). The verifier
hash-checks the pinned inputs and confirms the recorded acceptance signals.
The bootstrap fetches the certificate payloads from their pinned public commit
so the hashes can be checked against upstream. This package does not claim to
re-run the Wang Bazel build; it verifies the pinned inputs and the recorded
acceptance of that build.

## Contents

- `submission/f2-234-tensor-rank/`: manuscript source and rendered PDF
- `evaluators/`, `experiments/`: the exact evaluators and the finite exclusion
- `scripts/`: pinned-source and proof-checker bootstraps, plus
  `fetch_proof_pair.py`, which fetches and hash-checks `proof.drat`/
  `proof.lrat` from the permanent Zenodo record
- `tests/`: the 35-test replay suite
- `output/f2-234-tensor-rank/`: certificates and the profile census, plus the
  pinned Wang acceptance log; `proof.drat`/`proof.lrat` land under
  `output/f2-234-tensor-rank/profile-orbits/` once fetched
- `knowledge/data/`: the tracked 20-term upper-bound witness
- `docs/research/`: the canonical proof note and the independent referee report

Downloaded sources and built checkers are written under `tmp/` and are not part
of the archive.

## License

See `LICENSE.txt` in the archive root. Third-party inputs downloaded at replay
time (AlphaTensor, Wang's verifier, drat-trim/lrat-check) remain under their own
upstream licenses and are not redistributed in this archive.
