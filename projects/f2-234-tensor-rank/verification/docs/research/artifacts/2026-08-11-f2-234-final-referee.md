# Final independent referee — exact F₂ rank of ⟨2,3,4⟩

**Date:** 2026-08-11  
**Task:** `ses_00f667b2fffecGqpu5EZT4F2Gw`  
**Edits by referee:** none

## Verdicts

| Axis | Verdict |
|---|---|
| Openness before this result | **OPEN** |
| Correctness | **PASS** |
| Novelty | **PASS** |
| Significance | **NOTABLE** |
| Reproducibility | **PASS** |
| Publication | **RECOMMENDED** |
| Scientific objective | **COMPLETE** |
| Material remaining gate | **None** |

## Independent mathematical audit

The referee independently re-derived the row-restriction argument rather than
trusting the packet labels.

1. Every nonzero row restriction has flattening rank 12 and image
   \(B\otimes(x\otimes C)\). Distinct output row spaces intersect only at zero.
2. A tight 12-term decomposition forces both dyad-factor lists to be bases, so
   every active output factor lies in the corresponding row space.
3. For 13 active terms, the map from term coordinates to the 12-dimensional
   \(V\) space is surjective with a one-dimensional kernel. Projection outside
   the target row space therefore makes every quotient factor a scalar multiple
   of one common vector. Nonzero pure-tensor factorization is unique over
   \(\mathbb F_2\).
4. These lemmas contradict the `(7,7,5)` and `(7,6,6)` all-rank-one profiles.
   For `(6,6,6)` plus one rank-two factor, 18 required relation-support
   incidences exceed the three restrictions' total capacity of 9.

No missing quantifier, case, or counterexample was found.

## Exhaustiveness audit

- Wang's one-dimensional capacities force all 19 nonzero \(U\) factors to be
  distinct.
- The pinned profile CNF and checked DRAT/LRAT pair exclude two or more
  rank-two \(U\) factors.
- Fresh classification and enumeration reproduced 56,070 checked candidates,
  exactly 252 legal profiles, and orbit sizes `63 + 21 + 126 + 42`.
- The reviewed row-restriction packet rebuilt exactly and excluded all 252
  profiles, with none remaining.
- Symmetry transport is sound because the proof depends only on the certified
  row-multiplicity types; the code also checks every orbit image.

The referee identified the certified profile front end as the weakest trust
joint: a rank-19 construction, an omitted capacity-compatible profile, or a
failed replay of the pinned proof pair would refute the closure. None occurred.

## Reproduction

The referee reproduced these checks:

```bash
python3 -m evaluators.f2_234_tensor_rank_eval verify-controls
python3 -m evaluators.f2_234_tensor_rank_eval verify \
  --artifact knowledge/data/f2_234_rank20_alphatensor.json
python3 -m experiments.f2_234_tight_row_restriction verify \
  --artifact output/f2-234-tensor-rank/all-legal-u-profile-tight-row-exclusion-reviewed.json
python3 -m pytest tests/test_f2_234_tight_row_restriction.py \
  tests/test_f2_234_profile_orbits.py \
  tests/test_f2_234_tensor_rank_eval.py -q
```

Results: all 576 upper-witness coefficients passed; the reviewed packet
returned `VERIFIED_ALL_PROFILE_EXCLUSION` for 252 profiles; and 35 focused tests
passed. CNF regeneration was byte-identical. The Wang log contained all three
required acceptance signals, including unconstrained lower bound 19 and `OK`.

Pinned SHA-256 values matched:

- exact certificate: `89dbb5b9de7b13464a7bb7c78d6081a884c9ae933be923a7c787b84fcb5bd29b`;
- reviewed exclusion: `4e73f84c197ce9e9d475ee3742af7a84003b2b0833db057e62b22cc481211772`;
- profile packet: `82a7c6f5d0cb790ac796fa08281eb7b45acaa040f87b329883908c39acc3e122`;
- profile proof manifest: `fe8a1b87c1a3668aacdd813ed62e68c44c91adbdbaba37dbc6fb38b96fddbd5f`;
- Wang Linux log: `a30d346e94f55fc8ee9dd9d03999c8a0a626ed508e6b47975e656feb4a20304a`;
- AlphaTensor witness: `5b7193e7f9368eddc565b0b6d9b0dc8742760509d99fe9914cab8352e22b865b`.

The referee did not redundantly rerun the approximately 470 MB DRAT/LRAT pair
while shared load exceeded the material-compute gate. The bytes match the proof
pair whose prior fresh DRAT and LRAT replays both passed. A later redundant
replay is optional hygiene, not a scientific gate.

## Fresh prior-art result

A theorem-class primary-source search through 2026-08-11 found only the open
interval: Wang gives the exact-field lower bound 19, while Hopcroft--Kerr,
AlphaTensor, and the Sedoglavic catalogue give upper bound 20. Smirnov's 19 is
approximate, the Nazarov--Smirnov result is characteristic-zero approximate
rank, and adjacent formats or other fields do not settle this object. No prior
exact rank-20 determination or exact rank-19 \(\mathbb F_2\) algorithm was
found. The detailed source and scope matrix remains in
`docs/research/2026-08-10-f2-234-tensor-rank-target-charter.md`.

## Final judgment

The accepted chain is

\[
R\ge19\quad+\quad\text{all 252 rank-19 profiles excluded}
\quad+\quad R\le20
\quad\Longrightarrow\quad
R_{\mathbb F_2}(\langle2,3,4\rangle)=20.
\]

The result closes a classical named small-format interval and merits a concise
publication. It is `NOTABLE`, rather than `MAJOR`, because the mechanism is
currently specific to the three row directions available when the first matrix
dimension is two.
