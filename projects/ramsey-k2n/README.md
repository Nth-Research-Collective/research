# Five exact complete-bipartite Ramsey numbers

## Result

The paper determines five ordinary two-colour Ramsey numbers:

```text
R(K2,17, K2,17) = 66
R(K2,29, K2,30) = 116
R(K2,39, K2,40) = 156
R(K2,43, K2,44) = 172
R(K2,47, K2,48) = 188
```

Each follows by combining a published conditional theorem with a later
published construction: the Exoo–Harborth–Mengersen characterization (1991)
with Gritsenko's strongly regular graph srg(65, 32, 15, 16) (2021) for the
diagonal value, and the Lortz–Mengersen theorem (2002) with symmetric
Hadamard matrices of orders 116, 156, 172, and 188 (2015–2018) for the four
asymmetric values. Together these close the family's entire surveyed range:

```text
R(K2,n-1, K2,n) = 4n-4 for every 3 <= n <= 58.
```

## Paper and verification

- [Publication and permanent archive](https://doi.org/10.5281/zenodo.21878986)
- [Exact verifier and certificates](verification/)

## Verify the result

From the repository root, run:

```bash
python3 projects/ramsey-k2n/verification/verify.py
```

The verifier uses only the Python standard library and performs no search.
It checks the complete 65-vertex diagonal certificate (symmetry, degrees,
and every pair's codegree in both colours), reconstructs all four Hadamard
matrices from the published difference families, checks every inner
product, and checks every common-neighbour condition in the resulting
Ramsey colourings.

Certificate SHA-256 digests:

```text
6015bce8548584f108e6b5c51365bd6ae7c46349176f1b0fc87924ec0377df81  gritsenko-srg65.rows
eef979c2bc99cdd299b963f7af6ba62e169b43b1aa6115cba0488c149d9f1e22  k2n-ramsey-hadamard.json
```
