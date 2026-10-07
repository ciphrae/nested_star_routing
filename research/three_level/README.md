# Three-level sliding-puzzle research

## Result

This bundle contains a working three-level, one-board replay implementation and a new proved scheduling lemma controlling the sum of historical maximum branch credits.

The associated cost analysis supports the target

\[
n^3+O(n^{7/3}),
\]

rather than the two-level error exponent `12/5`.

**A universal three-level puzzle theorem is not claimed.** The scheduling lemma and conditional cost-to-exponent calculation are established. A uniform recursive physical-realization and cost proof is still required. Finite runs, even on large boards, do not supply that proof.

The original Lean package is not modified. This bundle contains no new Lean formalization and no PDF.

## Read the mathematics

- `theory/PEAK_CREDIT_LEMMA.md` proves the new bound and its consequence for inherited child export leads.
- `theory/THREE_LEVEL_CONSTRUCTION.md` gives the actual layout, recursive exchange rule, seven-term cost account, rounded parameters, and the precise remaining proof obligation.

The essential improvement is this: if a middle scheduler has `J` branches and total credit at most `B`, then the sum of each branch's largest-ever nonnegative credit is at most `J+B H_J`. It is not necessary to allocate a separate full `B` allowance to every child.

## Implementation

`prototype/three_level_replay.py` adds a corner-rooted middle lane system between the supplied outer and local systems. It implements recursive source-first requests and propagates auxiliary-label replacements into paused descendant inventories and helper-visit tokens.

`prototype/two_level_primitives.py` is an unchanged copy of the supplied archive's `mathematics/audit_nested_execution.py`. Its source hash is recorded in `results/summary.json`. The new implementation imports its board, coordinate, lane, local-router, and outer-router primitives.

The replay has one tile array and one blank. All ordinary blank walks and the fixed 5-, 19-, and 29-slide gate operations are expanded. Three-cycles and even sorting are executed by exact endpoint permutations with conservative slide receipts from the existing local-move lemma. They are **not** expanded into every elementary slide, so this is not a complete TAS move stream or a shortest-solution solver.

Initial conditions are reachable prepared configurations produced by a blank walk and even permutations within reserved/unreserved cell sets. Replays do not re-test the arbitrary-start preparation theorem.

## Run

Python 3.10 or newer and the standard library are sufficient. Run without `-O`, since assertions perform the verification checks.

A compact three-level replay:

```sh
python prototype/three_level_replay.py --fanout 1 --ell 2 --t 10 --seed 125
```

A replay with branching at all three routing levels:

```sh
python prototype/three_level_replay.py --fanout 2 --ell 3 --t 18 --seed 2026
```

Exact finite counter checks and integer-scale checks:

```sh
python prototype/check_peak_credit.py
python prototype/check_scales.py
```

Optional local chunking for the larger replay:

```sh
python prototype/checkpoint_replay.py --checkpoint local_replay.pkl --steps 25000 --output completed_replay.json
```

Repeat the same command to continue that local test until it writes `completed_replay.json`. The checkpoint helper is optional and is not part of the mathematics. Only load pickle checkpoints created by this script yourself; pickle is not a safe interchange format for untrusted files.

## Completed checks

Four full one-board replays reached the exact target:

| Board | Large regions | Smaller regions | Final block side | Expanded adjacent slides |
|---|---:|---:|---:|---:|
| 256 x 256 | 4 | 4 | 10 | 5,204,619 |
| 324 x 324 | 4 | 4 | 18 | 13,775,241 |
| 412 x 412 | 4 | 16 | 10 | 26,789,025 |
| 548 x 548 | 4 | 16 | 18 | 79,780,587 |

These slide counts exclude expansion of local-permutation macros. The largest run also used 1,296,690 three-cycle endpoint macros and 85 even-sort endpoint macros. Those are included in its conservative charged-length receipt, not in its expanded-adjacent-slide count.

The checks include literal tile conservation, source/destination inventories, one blank, helper-token transfer, no premature full-helper return, restored external working positions, middle-to-child lead identities, harmonic bounds on historical maximum credits, and exact final target equality. The sum of productive lane costs over all three levels is checked against the cubic median allowance on each complete replay.

Additional completed checks:

- 40 exhaustive finite counter cases, covering 75,538 states and 374,921 transitions, satisfied the historical-maximum credit inequality.
- 223 exact-integer candidate scale choices satisfied the listed fit and size inequalities.

Detailed machine-readable results are under `results/`. The compact replay dimensions are deliberately not the enormous dimension range proposed for the asymptotic theorem. The integer checks do not run physical boards of those enormous sizes.

## What remains

The next step is a universal recursive realization theorem establishing the interface, descendant substitution invariants, rounded geometry, termination, and complete physical cost account on one actual board for every admissible start. The candidate seven-term account then implies `7/3` by the arithmetic in the construction note.

Until that proof is completed, the supplied two-level `12/5` theorem remains the existing universal result. This bundle is a tested implementation and a mathematical extension plan with a proved new scheduling lemma—not a replacement theorem certificate.
