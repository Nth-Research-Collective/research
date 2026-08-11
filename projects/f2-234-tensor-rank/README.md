# Exact F2 rank of 2x3-by-3x4 matrix multiplication

## Result

The paper determines the exact bilinear rank, over the field with two
elements, of the tensor for multiplying a 2x3 matrix by a 3x4 matrix:

```text
R_F2(<2,3,4>) = 20
```

Hopcroft and Kerr gave a 20-multiplication algorithm for this format in the
late 1960s and conjectured that 20 is necessary. A 2026 result by Wang proved
a machine-checked lower bound of 19, leaving the exact rank open in the set
{19, 20}. This paper closes it. Every hypothetical 19-term decomposition is
shown to have 19 pairwise distinct first factors with at most one of matrix
rank two; a checked CNF/DRAT/LRAT certificate and exhaustive enumeration
reduce all such supports to exactly 252 profiles in four symmetry orbits, and
a row-restriction argument excludes every one of them. The upper bound is the
exact 20-term F2 decomposition from the public AlphaTensor factorization file,
checked against all 576 tensor coefficients.

## Paper and verification

- [Publication and permanent archive](https://doi.org/10.5281/zenodo.21895176)
- [Exact verifier and certificates](verification/)

## Verify the result

From the repository root, run:

```bash
python3 projects/f2-234-tensor-rank/verification/verify_all.py
```

The verifier checks every packaged file's hash, fetches and hash-checks the
pinned upstream sources (the AlphaTensor factorization file, Wang's
tensor-rank-lower-bound verifier source, and the DRAT/LRAT proof checkers),
freshly replays the 252-profile rank-19 exclusion and its DRAT/LRAT proof of
the profile lemma, runs the exact upper-bound evaluator controls, runs the
35-test replay suite, and recompiles the paper. It ends with:

```text
PASS: F2 <2,3,4> exact-rank reproduction complete
```

This mirror ships without the 191 MB `proof.drat` and 279 MB `proof.lrat`
files — both exceed GitHub's per-file push limit. `verify_all.py` fetches and
hash-checks them from the permanent Zenodo record automatically; see
[`verification/README.md`](verification/README.md) for details.

Certified artifact hashes (SHA-256):

```text
55fee5806b2e7fe6f4166ae06bd9125bf3f06cc3dfa3cd7722e77091bff87343  proof.drat
adce8ddb664eaedafa2b3599822aacddd0800d1721c3edcdf984ffbd8d4f551e  proof.lrat
584916d170bc4372e0d114b6589f9363141d5864d5925c0f926b1ca9184db4e7  profile CNF
89dbb5b9de7b13464a7bb7c78d6081a884c9ae933be923a7c787b84fcb5bd29b  exact-rank certificate
```

## Proof structure

- **Upper bound (rank <= 20):** the exact 20-term F2 decomposition, extracted
  and reindexed from the public AlphaTensor `factorizations_f2.npz` file,
  checked against all 576 coefficients of the 6x12x8 tensor.
- **Lower bound (rank 19 excluded):** Wang's checked first-factor capacities
  force all 19 nonzero first factors of a hypothetical rank-19 decomposition
  to be pairwise distinct, with at most one of matrix rank two. A 62,267-
  variable CNF with a checked DRAT/LRAT proof pair plus exhaustive enumeration
  of 56,070 candidates reduces the possibilities to exactly 252 legal
  profiles in four symmetry orbits. Restricting the first matrix to a single
  row excludes all four: two orbits force surviving output factors into
  disjoint row spaces, two force a contradiction from the uniqueness of
  nonzero pure-tensor factorization over F2, and the last needs 18 support
  incidences where only 9 are available.

## Scope

The result is exact for this one small format over one field. It does not
determine the exact rank of this tensor over other fields, does not change
the asymptotic complexity of matrix multiplication, and does not produce a
faster practical algorithm — Hopcroft and Kerr's 20-multiplication algorithm
for this format already exists. The profile lemma is machine-checked with a
DRAT/LRAT certificate; the row-restriction case analysis is reviewed and
exact but not formalized in a proof assistant.

## Disclosure

Beyond, the research system operated by Nth Research Collective, materially
assisted with literature retrieval, hypothesis generation, the finite
exclusion search, exact controls, and adversarial review. Research systems
are not authors; the author made the final scientific judgments and accepts
full responsibility.
