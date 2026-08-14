# A constant-competitive algorithm for Dynamic MoE serving

## Result

This paper proves that randomized integral Dynamic Mixture-of-Experts serving
has a constant competitive ratio for any number of experts. The previous
upper bound was `O(sqrt(log k))`, where `k` is the number of replica GPUs.

The explicit bound is

```text
E[ALG] <= 10 C_PB OPT + (5 C_PB + 2) k + 16,
```

where `C_PB` is the absolute constant from positive-body chasing at resource
augmentation one and covering sparsity two.

## Paper and verification

- [Publication and permanent archive](https://doi.org/10.5281/zenodo.21918990)
- arXiv submission pending public identifier
- [Formal development, exact controls, and replay instructions](verification/)

## Verify the result

From the repository root, run:

```bash
python3 projects/dynamic-moe-serving/verification/verify_all.py
```

The first run downloads two pinned arXiv source archives, Lean 4.32.2, and
the matching Mathlib cache. It then checks the manifest, builds the Lean
development, runs 24 theorem and exact-control tests, regenerates the two
canonical evidence files, and recompiles the seven-page paper.

A successful run ends with:

```text
PASS: Dynamic MoE Serving reproduction complete
```

## Proof structure

- A finite tangent envelope converts reciprocal service costs into positive
  covering constraints with row sparsity two.
- Summable resets charge accumulated service to movement.
- A nonexpansive balanced projection removes resource augmentation while
  preserving the exact GPU budget.
- Lazy Threshold Rounding converts the fractional path into a randomized
  integral allocation.

The Lean development proves the new reduction, projection, rounding
composition, lower bound, and quantified main theorem. It uses exact formal
interfaces for the cited positive-body chasing theorem and Lazy Threshold
Rounding lemma rather than re-formalizing those source papers.

## Scope

The result determines the asymptotic randomized integral competitive ratio
under the fixed-sequence convention. It does not determine the best numerical
constant, the deterministic integral ratio, the ratio against an adaptive
adversary, or the tighter fixed-memory function.

## Disclosure

Beyond, the research system operated by Nth Research Collective, materially
assisted with literature retrieval, hypothesis generation, formalization,
executable controls, and adversarial review. Research systems are not authors;
the author made the final scientific judgments and accepts full
responsibility.
