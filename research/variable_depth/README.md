# Variable-depth sliding-puzzle routing research

Start with `VARIABLE_DEPTH_ANALYSIS.md`.

The new finite accounting theorem is a size-weighted harmonic contraction. It supports a depth-uniform conditional error account and an `n^3 + O(n^2 log n)` target under explicit recursive physical-realization assumptions.

This package does **not** prove that universal sliding-puzzle bound, does not add a Lean theorem, and does not contain a new physical-board replay. The remaining physical premise is stated in Section 5 of the analysis.

## Files

- `VARIABLE_DEPTH_ANALYSIS.md`: definitions, proofs, arbitrary-depth account, choice of `f(n)`, integer rounding, and remaining obligations.
- `verify_variable_depth.py`: exact rational recurrence checks and exact integer scalar-geometry checks; standard Python library only.
- `check_peak_credit.py`: the unchanged finite counter checker from the supplied three-level research bundle, rerun here.
- `results/checks.json`: results from the variable-depth checker.
- `results/peak_credit_checks.json`: results from the supplied counter checker.

## Reproduce the checks

```sh
python3 verify_variable_depth.py --output results/checks.json
python3 check_peak_credit.py --output results/peak_credit_checks.json
```

For a single prescribed dimension and routing depth:

```sh
python3 verify_variable_depth.py --n 1208925819614629174706176 --layers 8
```

This example uses `n=2^80`. The script only computes region dimensions, products, and cost inequalities; it does not allocate an `n`-by-`n` puzzle.

All proof-status qualifications in the analysis apply to these checks. There is no dependency on the old Lean checkout or third-party Python packages.
