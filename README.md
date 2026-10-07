# Nested star routing: God's number of the n×n sliding puzzle is n³ + O(n² log n)

A Lean 4 / mathlib proof. The main theorem is `SlidingPuzzle.NestedRouting.Central.pair_bound`
(`NestedRouting/Final.lean`):

```lean
theorem pair_bound : ∀ (n : Nat) [NeZero n], 256 ≤ n → ∀ B T : Board n, Nonempty (Path B T) →
    ∃ path : Path B T, (path.length : ℝ) ≤ n^3 + 4161*n^2*Real.log n - 12148*n^2
```

`Central.pair_bound_of` and `Central.canonical` give the bound for any parameter set `k : Corner.Consts`:
`n³ + C1 k·n²·d + C2 k·n²` for `n ≥ N0 k`, where `d = k.dep ((n-5)/2)` is the depth of the quadrant trees,
at most `log_b (n / 2Tbig) + 1` (`Consts.dep_le_log_div`). The theorem above is the instance `Corner.std`
(b = 3, H₉ ≤ 2829/1000, Tmin = 107, Tbig = 361), with `C1 = 4570`, `C2 = 10659`, `ln 3 > 1.098546` and
`ln 722 > 5.99117·ln 3` (`Central.dep_le`). The only axioms are propext, Classical.choice and Quot.sound.

The mathematics is written up in `paper/main.tex`.

## Build and audit

```
lake build                              # default target NestedRouting
lake env lean Checks/AuditNested.lean   # prints the statement and its axioms
```

Lean 4.33.1 and mathlib v4.33.1. A build from scratch takes about 24 minutes, mostly mathlib.

## The construction in one paragraph

Every tile travels from its source up through nested hubs to the board centre, then down to its destination.
A node of the tree is a **region** (`Interface/Region.lean`). It takes source-first requests: one tile goes in
through an entry pair, one tile chosen by a fixed policy comes out, and nothing else outside the region moves.
A **star node** routes requests to its b² = 256 children along export and delivery lanes through a central hub.
`Star/Region.lean` proves that a star over regions is a region, with budget `base + rate·β` in its lead
allowance β. The tree uses **corner stars** (`Corner/`), whose hubs sit at the corner nearest their parent,
down to brute-force **leaves** of bounded side (`Leaf.lean`). The **root** is a central pinwheel over four
quadrant trees (`Central/`). Twice the routing-through-centre distance sum is at most n³. Each level of the tree
adds O(n²), and there are O(log n) levels.

## Module map

All of the Lean is under `NestedRouting/` (about 12.1k lines). Namespaces are `SlidingPuzzle.*` for boards and moves,
and `SlidingPuzzle.NestedRouting.*` for the construction.

| Directory | Lines | Contents |
| --- | ---: | --- |
| `Board/` | 220 | Boards, moves, paths and reachability (`Basic`, `Paths`); the parity invariant (`OrbitParity`) |
| `Moves/` | 1890 | Puzzle moves: single moves (`Local`), relabelling, conjugation by a staging path (`Conjugation`), embedding paths of a sub-square (`Embedding`), blank walks with exact effects (`Walk`, `Routes`, including the elbow access path), `t`-cycles (one tile carried to a corner block, the block rotated, the trip undone) and a three-cycle of any three cells in ≤ 54n moves built from them (`ThreeCycle`), its local form, sorting by `t`-cycles with a two-cell buffer (`TSort`), finishing with linear cost in the residual support (`SupportedFinish`, `GoalCompletion`), marked-label gathering and residual cleanup (`MarkedCleanup`), and the reduction from canonical to arbitrary pairs (`CanonicalReduction`) |
| `Geometry/` | 170 | Placed (translated and reflected) squares, local coordinates, straight segments |
| `Interface/` | 1050 | The region interface: the counter policy (`ReservePolicy`), five tile roles (`Roles`), selected transitions (`RequestPolicy`), role update on exchange (`RoleExchange`), the direct-exchange count (`ExceptionLedger`), `Region` itself, and the top-level feedback `Driver` |
| `Leaf.lean` | 260 | Brute-force leaf region |
| `Star/` | 4500 | The generic star node over `Region` children: abstract layout, one service, the scheduling ledger (peak-credit lemma), the inner invariant, helper rounds, the request wrapper, direct exchanges, the eight request cases, the structural laws, finishing, and `StarSpec.region` |
| `Corner/` | 2380 | Concrete corner-rooted layout, proved to be a `StarLayout` and `StarSpec`, with its exchanges and final sorts by `t`-cycles at the entry (`Entry`); the recursive tree `Consts.build` (`Tree`) and its budget (`Budget`): rate ≤ Kr·T, base ≤ 2·(distance sum) + Kl·T² + K0·T²·depth |
| `Central/` | 1260 | Root pinwheel layout and spec, the root region over four quadrant trees, and its budget at lead one |
| `Final.lean` | 330 | End-to-end assembly: `Central.canonical` and `Central.pair_bound` |

`NestedRouting/STAR_DESIGN.md` is the design note for the star node.

## Other directories

- `MathlibRoots.lean`: the mathlib imports.
- `Checks/AuditNested.lean`: statement and axiom audit.
- `paper/`: the write-up.
- `research/`: the accounting notes and Python prototypes that preceded the Lean proof.
