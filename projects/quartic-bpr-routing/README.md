# Quartic BPR routing counterexample

## Result

The paper gives an exact computer-assisted counterexample to a direct
common-degree quartic extension of the affine active-network shape theorem for
demand-dependent Price of Anarchy.

In a directed network with five vertices, six edges, and three paths, all
three paths carry positive Wardrop flow throughout the demand interval
`[17, 24]`. Nevertheless, the Price of Anarchy at demand `21` is strictly
greater than at both endpoints. Continuity therefore forces an interior local
maximum while the equilibrium active network remains constant.

## Paper and verification

- [Publication and permanent archive](https://doi.org/10.5281/zenodo.21864490)
- [Exact verifier and certificate](verification/)

## Verify the result

From the repository root, run:

```bash
python3 projects/quartic-bpr-routing/verification/verify.py
```

The verifier uses only the Python standard library. It reconstructs the exact
rational certificate in a fresh process and compares it byte-for-byte with the
published certificate.

## Scope

The result disproves the direct common-degree quartic extension described in
the paper. It does not determine the shape for parallel or series-parallel
quartic networks, bound the number of possible extrema, or establish a
minimal topology.

## Disclosure

Beyond assisted with literature search, hypothesis generation, proof critique,
code, testing, and drafting. Authorship and responsibility are stated in the
publication. Beyond is not an author.
