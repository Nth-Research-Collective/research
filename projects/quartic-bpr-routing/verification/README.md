# Exact verification

Run from the repository root:

```bash
python3 projects/quartic-bpr-routing/verification/verify.py
```

The check uses exact rational arithmetic, rebuilds the certificate in a fresh
process, and requires byte-for-byte agreement with the published certificate.
It uses only the Python standard library.

The complete publication package remains permanently available at
[Zenodo](https://doi.org/10.5281/zenodo.21864490).
