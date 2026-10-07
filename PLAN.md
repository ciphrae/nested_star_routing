# nested_routing — status and plan

## Goal and status

**Goal:** a Lean proof that God's number (indeed the diameter of every reachability component) of the n×n sliding
puzzle is n³ + O(n² log n), by nested star routing.

**Done (2026-10-05).** `SlidingPuzzle.NestedRouting.Central.pair_bound`: for all n ≥ 614,
every mutually reachable pair B, T is joined by a path of length ≤ n³ + 96411·n²·ln n + 667231·n². Axioms: propext,
Classical.choice, Quot.sound (`Checks/AuditNested.lean`). No sorry.

**Branch `constants` (2026-10-06).** The same theorem with n ≥ 256 and n³ + 4161·n²·ln n − 12148·n²,
by spending more geometry on the constants. See "Constants branch" below.

For comparison:
- **Per-board approximation corollary (separate project):** n³ + O(n^(5/2) ln n / ln ln n).
- **Lower bound** (separate project): G(n) ≥ n³ + n² − 2n − 2.

`README.md` has the module map. `paper/main.tex` is the write-up.

## Repository history

- **Base (2026-10-04).** We started from an external, verified two-level Lean package: n³ + 3,600,002·n^(12/5)
  for n ≥ 2^40. It was a flat dump of about 245 modules at the repository root.
- **Steps 1–5 (2026-10-05).** We built, in order:
  1. the `Region` interface;
  2. the brute-force leaf;
  3. the middle-node step (a star over regions is a region);
  4. geometry at every depth: corner layout, node tree, node budget, central root;
  5. the end-to-end composition.
- **Reorganisation (2026-10-05).** Everything the nested proof does not use was removed.
  - Only 11 modules of the 12/5 package were used: the role/policy bookkeeping and some move lemmas. They now live in
    `NestedRouting/Interface/` and `NestedRouting/Moves/`.
  - The board library carried over from an earlier per-board project (`SlidingPuzzle/`, `Zhong/`) was pruned to what the proof uses; what
    remains now lives in `NestedRouting/Board/` and `NestedRouting/Moves/`.
  - Unused declarations were removed throughout. They were computed from the constant-dependency closure of
    `pair_bound`, keeping `rfl` simp lemmas about live definitions.
  - Lean went from about 63k to about 17k lines.
- **Simplification (2026-10-05).** About 12k lines remain:
  - **Counters as an invariant.** `ReservePolicy.Run`/`Step` became `Counts.Valid` with `valid_advance`.
  - **One bookkeeping structure.** `TileRoles.State` is a `Prop` over the role sets and counters, and
    `Interface.Sound` extends it.
  - **No request history.** `ExceptionTrace` is gone; the star record keeps the late core arrivals and
    `LateInvariant`.
  - **Direct three-cycle.** `Moves/ThreeCycle.lean` (≤ 104n moves) replaced the old sharp three-cycle
    (≤ 52n), which needed the Parberry/Zhong placement stack. Three-cycle-based costs doubled throughout:
    double swap 208s, finishing 104n per cell, `Corner.std` Tmin 324782.
  - **Direct blank access.** The elbow access path is now a column walk plus a row walk (`Moves/Routes.lean`).
    With it, the whole `Zhong/` library is gone.
  - **Clean build.** Lint pass; the build is warning-free.

### Design decisions worth remembering

- **Fixed branching.** Leaves have bounded side, so rounding costs only additive constants
  (`research/variable_depth` §8). The paper uses b = 16. The Lean instance `Corner.std` uses b = 4,
  H₁₆ ≤ 3381/1000, λ = 57 and Tmin = 282, chosen to make the constants small.
- **Constants (2026-10-05).** A star of side T may spend cs0 ≤ λ·T on hub overhead per service
  (cs0 ≈ 416·(3b²+9) comes from the hub double swaps). Rates still contract, at the price of λ entering `Kr`.
  A larger λ means smaller stars, hence smaller brute-force leaves.
  - Leaves are charged once (Kl·T², with Kl = 520·Tbig) and stars once per level (K0·T²).
  - The root uses 4T² ≤ n².
  - The harmonic bound is a fraction p/q ≥ H_J, kept in ℕ (`StarSpec.harm`: q·Σ⌊B/t⌋ ≤ p·B). Rates contract when
    p < q·b, with rate constant X·(qb − p) ≥ (λ+4)p + 210q. The old dyadic bound H_J ≤ mJ + 1 needed b ≥ 8; the
    exact fraction allows b = 4, which shrinks the hub (side ≈ 3b²).
  - Analysis: the reserve count drops a 6b²·T slack (the child spare cells are a constant), and the lane total is
    summed exactly over the slot grid (Σ(row + col) = b²(b−1)), so J + Σ(|X|+|Y|+2) ≤ 2b(b−1)T + O(1).
  - The three-cycle (`Moves/ThreeCycle`) costs ≤ 70n. Tiles move by diagonal pushes, 6 moves per up-left step.
  - Together these took the effective coefficient from about 1.9·10⁹·n²·ln n (C ≈ 1.08·10¹⁰ with log₁₆,
    N = 649662) to 9.6·10⁴·n²·ln n + 6.7·10⁵·n² (N = 614).
- **Where the constants come from now.** About 98% of both constants is three-cycle work.
  - Per-level term K0 = 133654:
    - direct exchanges 32%;
    - wrapper swaps 28.5% (a double swap in a square of side W + M0 + 6, because the entry is at column 0 and
      the hub at column M0);
    - children's rates 14%;
    - hub swaps 12%;
    - final sort 8%.
  - n² term: leaves (brute force) 63%, root 37%.
  - Next steps, each a geometric redesign rather than bookkeeping:
    - put the entry pair above the hub, which shrinks the wrapper square to about W + 6 (≈ −20%);
    - bring tiles to the carrier by pushes instead of double swaps;
    - a narrower spoke margin, to cut the reserve area (≈ 2M0·T own cells).
  - A cheaper three-cycle would scale everything: staging a once with two blocks sharing p, q saves a quarter of
    the transports, roughly 70n → 54n.

## Constants branch

| Commit | Change | ln-coefficient | n² coefficient | N |
| --- | --- | ---: | ---: | ---: |
| master | | 96411 | 667231 | 614 |
| Stage 1 | root budget split into n² and linear parts | 96411 | 451742 | 614 |
| Stage 2 | three-cycle in 54n: stage `a` once, then `ρ⁺ c'⁻ b'⁺ ρ⁻` | 76176 | 313129 | 548 |
| Stage 3 | every exchange is one three-cycle (no double swaps) | 43064 | 171631 | 498 |
| Stage 4 | exchanges as capabilities of `StarLayout`/`StarSpec`; corner hub, wrapper and direct exchanges by `t`-cycles | 18623 | 104901 | 292 |
| 4d | leaf requests by the entry `t`-cycle exchange | 18623 | 66957 | 292 |
| Sorts | final sorts of stars and leaves by `t`-cycles (`Moves/TSort`) | 16226 | 54715 | 292 |
| Margin | two margin columns per spoke instead of three (M0 = 2b² + 4); λ = 10, Tmin = 103 | 12960 | 48397 | 256 |
| Leaf constant | leaf requests charge 24W + 170 additively; `Tmin_dx` weakened to 24W + 170 ≤ Tbig | 12960 | 45457 | 256 |
| Weighted sort | transport costs 2(r+c) + 4·max(r,c) + 6 by position; `TSort` charges each cell its own `t`-cycle; leaves sort in (56/3)T³ + O(T²) | 12960 | 39193 | 256 |
| Reserve bound | `r_arith` keeps its −W·T: cr = 2(M0+b) + (b−1)W + 1 = 111 | 12477 | 39193 | 256 |
| Rate constant | Kr·(b − H) ≥ b·((λ+4)H + 19), using b·x ≤ T, instead of (b+1)·Xr: Kr 540 → 429 | 11901 | 39172 | 256 |
| Linear terms | the parts of a star's base that are O(T) (cmax·J, access and export walks, connector, child rates over constant lanes, the sort's six markers) cost ⌈Lin/Tbig⌉·T² instead of constants·T² | 10569 | 39172 | 256 |
| Hub at the entry | carrier K = (W+1, 1) and park cell w = (W, 2) next to the entry column: the wrapper `t`-cycle needs a 6-column frame (12W + 54 instead of 4W + 12·M0 + 38), the connector shrinks to W + 1, the hub frame runs right from K (12·M0 + 20); Tmin = 99 | 9475 | 38368 | 248 |
| No λ | stars have T ≥ Tbig, so cs0 ≤ ⌈cs0/Tbig⌉·T and 16T + 24W + 170 ≤ (16 + ⌈(24W+170)/Tbig⌉)·T; the cs0 part of the lane term moves into Lin. λ and `Tmin_dx` are gone, Tmin is free: Tmin = 47 | 8945 | 27936 | 144 |
| Lanes in the rate | a spoke's lanes are ≤ 4(b−1)·x + O(1), not 4T, so Kr·(b−H) ≥ (b·lam + 4(b−1))·H + b(dk+2) | | | |
| b = 3 | branching 3 (H₉ ≤ 2.829, ln 3 > 1.098546 from 3¹² > 2¹⁹); Tmin = 107, chosen for the ln term | 7853 | 32380 | 260 |
| Star sort by position | the star's final sort charges each reserve cell its own `t`-cycle; the reserve distance sum is computed exactly (body minus children, `resid_arith`), ≤ (3(b−1) + 2(M0−2) + W(b−2))·T² + O(T) | 7193 | 32380 | 260 |
| Per-spoke hub, rounding | the hub exchange for spoke j costs 12·a_j + 24 (position bound); the base term charges the average 26(M0−J−1) + 50, only the rate the maximum. The two roundings in the rate fold into the hub constant (2q ≤ p) | 6805 | 32373 | 260 |
| Root reserve | the root's reserve is ≤ (4m + 2W + 5)·n, using 2T ≤ n (was 4m + 4W + 20); the end-to-end O(n) terms join the root's linear part | 6805 | 26463 | 260 |
| Leaf ledger | helper exports come only after exhaustion and are at most the lead, so a leaf serves ≤ M + r + β requests (`HInv`): base rcost·(M+r), rate rcost (was 2(M+r) in the base). `Consts.Tmin_leaf`, `Kr_ge` (Kr ≥ 24) keep rcost ≤ Kr·T | 6805 | 20293 | 260 |
| Root direct exchange | `t`-cycles in four half-board frames around the entry pair (`Central/Exchange`): right of eP directly, left of it after one blank move; 16(n−c) + 260 ≤ 8n + 276 instead of 54n. The four cells beside the block use a 6×6 square | 6805 | 17687 | 260 |
| Leaf requests by position | source tiles never move in a leaf (requests park through spare cells), so each core cell exports once at its own weight `Entry.dw` (potential Φ = weights of the core cells still holding sources): (28/3)T³ instead of 16T³ | 6805 | 15279 | 260 |
| Sort in 3/2 | `TSort` loads the misplaced cell of least weight; the next `t`-cycle places the loaded tile at a cell at least as heavy, so charging 3w/2 (w when holding a buffer tile) pays every step. Sort weights ⌈3(tw+2)/4⌉: stars 18·al instead of 24·al, leaves 14T³ | 6467 | 13578 | 260 |
| Corner wrapper by position | `t_K` charged `tw` at the carrier, 12W + 34 instead of 12W + 54 | 6394 | 13578 | 260 |
| Root sort from the corner | the blank walks to (0,1), the transposed board frame's corner block holds child homes (`Built.spare_near`, new `fsort` hypothesis: R has no child homes), the `t`-sort runs on the conjugated region, the walk is undone: 12n + n/3 + 2 per cell instead of 27n | 6394 | 12737 | 260 |
| Root wrapper | `t`-cycles charged by position on both sides (`Cycle3.tdirect_at2`) in a 7×6 frame at the entry: 186 instead of 378 | 6394 | 11969 | 260 |
| Root hub exchange | `t`-cycles from the carrier K (left spokes directly, right spokes after one blank move onto K): 190 instead of 378 (`Central/Layout`, helpers in `Central/Frames`) | 6394 | 11536 | 260 |
| Depth | stars have side ≥ Tbig, so the quadrant trees have depth ≤ log₃(n/726) + 1 (`dep_le_log_div`), not log₃ n: `canonical` states the bound with the depth, and `dep_le` gives 7024·d ≤ 6394·ln n − 35091 | 6394 | −23555 | 260 |
| Exchange ledger | before core exhaustion a reserve source leaves only with a reserve arrival (case Ra), so `er = ar` there; helper exports need both kinds of source exhausted, and are then paid by the lead. `LateInvariant` now gives `er + late ≤ r + B`, so direct exchanges ≤ r + β (was 2r + β) and wrappers ≤ M + r + β (was 2(M + r)); a late request's wrapper moves into the rate (`dkr = 16 + ⌈(24W + 170 + wrapC)/Tbig⌉ = 18`). K0 7024 → 5691, root 2331 → 1725 | 5181 | −17527 | 260 |
| Exact constants | the rate's constant parts (hub overhead csl + 1, the late request's 24W + 170 + wrapC) are divided by Tbig exactly inside Kr, not rounded up one by one (Kr 548 → 533); the reserve count is r ≤ cr·T − crc with cr = 2(M0 + b − 1) + (b − 1)W = 64 (the remainder T − M0 − b·T' is at most b − 1) and crc = 1104 credited to the linear terms (`r_arith`, `S_r'`). K0 5691 → 5518 | 5024 | −16665 | 260 |
| Exact lanes | `elen + dlen + 2W + 2a_j + 4 = 2δ_j + 4c_j` (`S_lanes_eq`): the lanes start at the hub and the margin column, not at the slot corner. A service then costs 2δ_j + 24a_j + 46 + 4(b−1) − 2W per child cell (`sv` = 326 for cs0a + 4b = 374), the lane total's constant is b²(2b² + 4b + 4) = 306 (was 738), and the worst service constant `csl` is 24(M0 − 2) + 2M0 + 4b + 50 = 586 (was 650; Kr 533 → 525). K0 5518 → 5224 | 4756 | −15198 | 260 |
| Lane work by slot | services on lane tiles: cost_j·(|X_j| + |Y_j|) ≤ (2δ_j + smax)·2δ_j with δ_j = kap + (row + col)·T', summed over the slots (`S_lanework`): 4·Σ(row + col)²/b² = 22 per T² (was 16b² = 144), and the linear part 2(4kap + smax)·b(b − 1) plus the constant over Tbig (was 4b²·cs0). K0 5224 → 5070 | 4616 | −14429 | 260 |
| Weighted peak credit | the ledger ranks retired spokes (`Good.ranks`: distinct ranks above the active count, peak ≤ 1 + ⌊B/rank⌋), so Σ ρ_j·peak_j ≤ Σ ρ_j + Σ_v H(#{ρ > v})·B for any weights (`Good.weighted_peak`, `layered`). Service costs split as cb + 2T'·(row + col) + 48·(J − 1 − j) (`StarSpec.cb`, `S_cb`: cb0 = 202), so far spokes and near spokes pay their own costs: 8.002 and 16.461 instead of 4(b − 1)·H₉ = 22.6 and the hub constant at H₉. Kr 525 → 472. K0 5070 → 4842 | 4408 | −13299 | 260 |
| Band of 2b rows | a slot's band needs rows 2c, 2c + 1 for the spokes (and the child's entry pair) only, so W = 2b instead of 2b + 2: two fewer reserve rows per slot row (cr 64 → 60), and a shorter wrapper, connector and parking frame. Tbig = 361, so `dep_le` uses log₃ 722 > 5.99117; N0 = 256. K0 4842 → 4663 | 4245 | −12612 | 256 |
| Static cells | a star's `stat` cells are own cells off the lanes, the carrier and the parking cells, so no wrapper, service or child moves them (`exists_wrapped` already fixes non-foot cells; substitution fixes reserve sources). The star record keeps `fresh` (static cells still holding a reserve source) and `nf` (other reserve exchanges, only once no fresh cell is left): reserve exports take a fresh cell first, by a direct exchange charged by its position (`dXw`, `exportReserve`), and the base pays `dxCost·(r − |stat|) + Σ_stat dw`. The corner's static cells are the margin columns of the spokes of slot rows ≤ ρ in the body rows of slot row ρ, plus the four left columns (`statP`); they save `gq·T² − gl·T` with gq = 144, gl = 18528 (`S_stat_gain`, `rows_gain`). K0 4663 → 4570 | 4161 | −12148 | 256 |

- **`t`-cycles.** With the blank at `z` of a 2×2 corner block `p q / s z` of a rectangular frame, carrying the
  tile of a cell `x` to `s`, rotating the block and undoing the trip cycles `(x p q)` or `(x q p)`. It costs
  `tcost F = 2·(2(R+C) + 4·max R C) + 4` in an R×C frame (`Cycle3.tcycle`, `tcycle_s`, `tcycle_w`), so a small
  frame makes it cheap.
- **Corner exchanges** (`Corner/Star`, `Corner/Spec`, `Corner/Entry`):
  - hub: `t_{H j}` in a 3 × (M0+2) frame after a two-step blank walk, third cell `(W+2, M0)`: 12·M0 + 44;
  - wrapper: `t_K` at the entry block, third cell `(2cs, 1)` in the band: ≤ 4W + 12·M0 + 38;
  - direct exchange `(eP x p₁)`: `t_x⁺` in the whole slot conjugated by `t_{p₁}⁻` in a 6-column frame,
    parking on `(W, 0)` or `(W, 1)`: ≤ 16T + 24W + 170 ≤ 17T (`Consts.Tmin_dx`).
- **Leaves** take their request through a spare parking cell, charged by the exported cell's position
  (`LeafSpec.rX`, `rw`), and their final sort from the layout (`fX`).
- **Sorting** (`Moves/TSort`). The blank stays at `s`; `p`, `q` are a buffer. A buffer tile that belongs in R is
  placed by one `t`-cycle; an idle buffer is loaded with the misplaced tile of least weight, which the next
  `t`-cycle places. Each cell x has a weight w(x) bounding its `t`-cycle (`tw r c + 2`, from the
  position-dependent transport). Twice the potential charges a misplaced cell 3w(x), or 2w(x) while it holds a
  buffer tile; every step pays for itself, so the sort costs ≤ (3/2)·Σ_R w. Parity is settled by two free goal
  slots, and the buffer ends restored by the sign. Stars and leaves use position weights
  (6·Σ max(i,j) ≤ 4T³ over the square); the root uses the uniform 16n + 2 from the board corner.
- **Where the constants come from now** (b = 3, Tmin = 107, Tbig = 361, W = 6, M0 = 22, cr = 60;
  derived lam = 2, dk = 17, Kr = 467):
  - K0 = 4570 per log₃ n: children's rates 2·2·467 = 1868, final sort 18·52 = 936, direct exchanges 17·60 − 144 = 876,
    service overhead 330, linear terms 312 (51 of them the static cells' correction), wrapper 226, lane tiles 22;
  - n²: leaves Kl = 8778 (requests (28/3)T, sort 14T per unit area, times Tbig); root 1593 (services 394,
    wrapper 374, direct exchanges 8·cR = 200, sort 25·cR = 625, cR = 25); linear parts; cleanup 108.
  - Tmin trades the two. With the depth bound the n² coefficient is C2 − K0·(log₃(2·Tbig) − 1):
    Tmin = 140 gives 4022 / −10095 (n ≥ 322); Tmin = 203: 3878 / −6237 (n ≥ 448); Tmin = 300: 3772 / −229
    (n ≥ 642). b = 4 has the smaller ln coefficient at equal Tmin (4427 vs 4615) but is
    worse below n ≈ 2·10⁹ (larger reserve). These come from `research/constants/mirror.py`, a Python
    copy of the constant formulas; they are not checked in Lean.
  - The rate constant is amplified by b/(b − H₉) ≈ 17.5, so the rate recursion carries most of the ln term,
    and in it the late requests' exchange and wrapper (b·(16 + dc/Tbig) ≈ 53 of the 80.6 in Kr's numerator).
- **Further ideas, roughly by size:**
  - a cheap direct exchange for late requests that export helpers (only the rate's late part would drop: Kr 472 →
    about 160, K0 about −1350). It needs a helper within O(1) of the entry at every such request;
  - the bottom strip of a corner star (now M0 − W − 4 = 12 rows: 12 of cr = 60 and 18 of the 52·T² reserve
    distance sum, about 530 of K0). A staircase of slot rows does not help (slot row 0's band still needs all 2J
    lane columns beside it). Proposed fix: slot row 0's spokes run right along a new top corridor of 2b rows and
    drop straight into their band (rows 0..2c−1 at column f_c are free), the other spokes keep the margin. Row
    overhead W + 4 + 2b and margin 2b(b − 1) + 4 are then both 16, the strip disappears, T' = (T − 16)/b; estimate
    K0 4570 → about 4000. Needs a second spoke shape in `Corner/Layout`, `Star`, `Spec` and the lane and reserve
    sums in `Corner/Budget`; check the layout in Python first;
  - more static cells: the band rows beyond each lane's end (about 55 of K0 before the linear correction) and the bottom strip;
  - leaves: placing arriving tiles at home directly would remove most of the final sort, but helper inputs
    can push the leaf into chains of misplacements; the bound needs a way to break them;

## Possible further simplifications

- **`Central/` vs `Corner/`.** The central pinwheel layout (`Central/Layout`, `Central/Spec`) re-proves hub,
  lane and connector facts separately from the corner layout. A shared "hub row plus L-shaped loop" toolkit
  might shorten both. It is not yet clear by how much.
- **`MarkedCleanup` and `GoalCompletion`.** These are inherited from the 12/5 package. Both now rest on
  `exists_three_cycle`, so their parity and support bookkeeping may simplify further.

## Earlier verification (research phase, 2026-10-04)

- **Peak-credit lemma.** Σ_i P_i ≤ J + B·H_J. It is proved on paper (`research/three_level/theory/`) and now in
  `Star/Ledger.lean`.
- **Weighted recurrence.** W_{i+1} ≤ 9b·n² + (H_{b²}/b)·W_i, and the exponent 2 + 2/(L+3) for depth L. Both were
  checked with exact rationals (`research/review/`).
- **Credit cap with a reserve: ER ≥ AR.** The parent exports a reserve original for every reserve arrival while
  any remain, so Σ C_child ≤ B_parent + 1 at every depth.
- **Prototype.** `research/three_level/prototype/deep_replay.py` passes every assertion at depths 3–6. These are
  mechanics only: tiny boards, constants 270–550× n³.
