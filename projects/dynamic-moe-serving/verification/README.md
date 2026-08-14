# Dynamic MoE Serving: Reproducibility Package

This package reproduces the formal and computational evidence for *A
Constant-Competitive Algorithm for Dynamic Mixture-of-Experts Serving*.

## Verify

On macOS or Linux, from this directory:

```bash
python3 verify_all.py
```

The first run needs internet access to download two pinned arXiv source
archives, Lean 4.32.2, and the matching Mathlib cache. It also requires `bash`,
`curl`, `git`, and [Tectonic](https://tectonic-typesetting.github.io/) on
`PATH`. Python 3.10 or newer is required; the Python checks use only the
standard library.

The verifier:

1. checks every packaged file against `MANIFEST.sha256`;
2. downloads and hash-checks the two cited theorem sources;
3. installs or selects Lean 4.32.2 and pinned Mathlib dependencies;
4. runs the 24 theorem and exact-control tests;
5. regenerates both canonical JSON evidence files byte for byte; and
6. compiles the seven-page paper from `paper/main.tex`.

A successful run ends with:

```text
PASS: Dynamic MoE Serving reproduction complete
```

## Certified outputs

- Exact control SHA-256:
  `53c7ac33689b4cef22057fd1f9c040dab4e00a8aa13c5277b6a1b6e91e041a66`
- Portable formal packet SHA-256:
  `adcb13dad31d6fc688982068396e9733cf3d6f6444285f015cd0e6e1c1fde3f4`
- Paper source SHA-256:
  `27b0bcc2ba99550b646a0a8922b02239b46dde0ccfaefbd4e3fa06495fc60895`
- Included PDF SHA-256:
  `1c55c103a7a8c8342899153502bd63d256b4a35c7062ea74abf9f08087dc695d`

The formal packet stores repository-relative proof paths and a
platform-independent Lean version string, so its hash is identical on
supported machines.

## Formal scope

The Lean development proves every new Dynamic MoE reduction, rounding
composition, lower bound, and main theorem. It treats two published results as
explicit source-level premises:

- Bhattacharya, Buchbinder, Levin, and Saranurak, *Chasing Positive Bodies*,
  arXiv:2304.01889v2, Theorem 1.1 at resource augmentation one and covering
  sparsity two.
- Huang, Lou, and Xiao, *Mixture-of-Experts Serving*, arXiv:2607.17880v1,
  Lazy Threshold Rounding and Lemma 4.4.

The bootstrap checks the exact source archives and theorem-bearing members.
The package does not claim to re-formalize either cited paper.

## Main declarations

- `DynamicMoeMain.dynamicMoe_randomized_theta_one_of_source_theorems`
- `DynamicMoeMain.dynamicMoe_explicit_constant_upper_of_source_theorems`
- `DynamicMoeSemantics.competitive_factor_lower_bound_at_least_one`

Lean reports only `propext`, `Classical.choice`, and `Quot.sound` as transitive
axioms for the audited declarations.

## Contents

- `formal/`: Lean sources, pinned project configuration, and axiom verifier
- `evaluators/`: deterministic exact controls and formal packet generator
- `tests/`: the 24-test replay suite
- `scripts/`: source and Lean bootstrap scripts
- `output/`: canonical JSON evidence
- `paper/`: manuscript source and rendered PDF

Downloaded sources and Lean build products are written under `tmp/` and
`formal/lean_project/.lake/`; neither is part of the archive.
