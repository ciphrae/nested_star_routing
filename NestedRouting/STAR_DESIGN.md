# Star node design

This is the spec for the middle-node step: a star router over `Region` children is itself
a `Region`. The executable reference is `research/three_level/prototype/deep_replay.py` (`Node`, `StarInner`).
Where this design deviates from the prototype, it says so.

## Frames at each level

A node P with children Q₁..Q_J (J = b², b = 16 in the main construction):

| P field | cells |
| --- | --- |
| `coreCells` | ⋃_Q (Q.coreCells ∪ Q.reserveCells): homes inside children |
| `reserveCells` | P's own lanes and hub, the children's strips and spare (marker) cells, and rounding remainders |
| `spareCells` | P's six marker cells, which hold helpers (these are the parent's reserve homes) |
| `strip` | P's entry strip, outside P.cells, containing P's entry pairs |

- **Helpers.** P's helpers are labels of its six marker cells. They are reserve sources of P's parent, and that
  parent fetches them by direct exchange (`substitute` recursion).
- **Finishing stays local.** P's finish sorts only `P.cells \ P.coreCells`, which has size O(s·b²). Any design
  that parks a node's received reserve finals deep in descendants and sorts at the node's finish costs Θ(s³),
  because total spare area over a subtree is a constant fraction of its area.

## Roles of tiles in transit

- P core sources = tiles initially in children's homes, i.e. the children's sources. They leave children only by
  child exports, travel up export lanes, and reach P's carrier.
- P reserve sources = tiles initially in P's lanes, hub, children's strips and markers. The star treats those
  in lanes as helper tokens. P exports reserve sources only by **direct exchange**: a double swap
  e_P ↔ (cell holding the tile) inside P's square. If that cell lies in a child, the child is updated by
  `substitute`, recursively.
- P core finals are pushed into their child's delivery lane immediately, and are delivered to the child as core
  or reserve arrivals according to the child's goal sets. Invariant: every P core final with home in Q is a
  Q final or lies in Q's delivery lane.
- Anything else delivered to a child is delivered as a **helper**. That includes P helpers, P reserve sources
  and P reserve finals parked as child helpers. A P helper is never delivered as a child goal: that could lock a
  P goal inside a child as a final while P still counts it as a helper.

## One service on spoke Q (deviates from the prototype: one child request per service)

Geometry for spoke Q:
- a hub cell H_Q;
- a loop start x_Q;
- an access walk from the hub park cell w to x_Q;
- the export lane E_Q, from its hub end to its child end z_Q;
- the delivery lane D_Q, from its child end e_Q to its hub end;
- `Q.Entry e_Q z_Q`.

Each service runs:

1. Double swap carrier cell K ↔ H_Q, together with parity cells u ↔ v, inside the hub square.
2. Walk w → x_Q. Walk x_Q → along E_Q → z_Q.
   - If allowed, call child request(input = tile at e_Q, role as above). Otherwise skip: the idle turnaround.
   - Continue the walk z_Q → e_Q → along D_Q → H_Q → x_Q. Then walk back x_Q → w.
     - Cells of the access walk must avoid the loop, except x_Q.
     - Restoration is by `Path.exists_conjugated`.
3. Double swap K ↔ H_Q, u ↔ v again. u and v are restored because they are swapped twice.

Net effect of one service:
- the carrier enters the delivery tail, and the delivery lane shifts toward the child;
- the delivery head enters the child, or turns around into the export tail;
- the child's output enters the export tail, the export lane shifts toward the hub, and the export head becomes
  the carrier;
- H_Q holds a helper before and after.

Its cost is loop length + 2·walk + 2·208·hub side + the child's request cost.

Why one request per service suffices: every child request exchanges one in for one out. Delivering the head,
whether a final or a token, returns the child's next export, which is a source while any remain. That is
source-first. A token head with a retired child turns around (idle).

Delimiter fact: while the child Q still has sources in P's view (S_Q < population_Q), every token reaching the
export head is an initial export-lane tile. Child helper outputs and turnarounds enter behind all of Q's sources.
So helper returns while active ≤ |E_Q|.

## Request protocol for P (the prototype `Node.request`; the policy of `Interface/ReservePolicy.lean`)

A wrapper means:
1. walk z_P → w;
2. double swap e_P ↔ K (with u ↔ v);
3. the inner run;
4. double swap back;
5. walk back.

The inner run is one service on the goal's spoke for a core input, or else on the minimum-credit active spoke.
Then, while an original is needed and the carrier is not a P core source, run another service on the
minimum-credit active spoke.

| Arrival | Condition | Action |
| --- | --- | --- |
| core | ec < M | wrapper(real, need original) |
| core | ec = M | wrapper(real, single service); then a correction (direct exchange with a reserve source) or a rescue (direct exchange with a helper, when the output is a reserve final) |
| helper | ec < M | wrapper(helper, need original) |
| reserve | er = r, ec < M | reserve staging: direct exchange with a helper, then wrapper(helper, need original) |
| any other | | direct exchange with a reserve source if any remain, else with a helper |

There is one direct exchange per request at most. `LateInvariant`
(`Interface/ExceptionLedger.lean`) bounds their count by r + lead: before core exhaustion a reserve source
leaves only with a reserve arrival, so the staging case never occurs, and helper exports come only once both
kinds of source are exhausted, when the lead pays for them.

## Cost targets (per node, excluding children's own work)

- **Productive:** Σ_Q |goals of Q| · (lane pair length of Q). This telescopes across levels to ≤ n³.
- **Overhead:** A·(s²·b² + s·(β+1)·H_J), where β is P's lead allowance and A does not depend on depth.
  This covers the hub per request, drain ≤ Σ_Q |lane|², helper rounds, direct exchanges ≤ dcost·(r + β), and
  the finish sort.
- **Child leads:** Σ_Q (β_Q + 1) ≤ J(4s+5) + (β+1)·H_J, by the peak-credit lemma
  (`research/three_level/theory/PEAK_CREDIT_LEMMA.md`).
  - Child lead = credit + delivery-lane accepted + export-lane live ≤ credit + lane lengths + 2.
- **Region budget:** base = productive + A·s²b² + Σ_Q base_Q + Σ_Q rate_Q·(lane terms);
  rate = A·s·H_J + max_Q rate_Q·H_J. This needs the lowest-credit schedule.

## The root

The root is also a `StarSpec` region: a central pinwheel over four quadrant trees (`Central/`). It is run by
the generic feedback driver `Region.drive` (`Interface/Driver.lean`) at lead one: one helper request, then
every exported source goes straight back in as a goal arrival, then finish. `Final.lean` wraps this with the
blank walks, marker gathering and residual cleanup.

## Lean files (`NestedRouting/Star/`, in dependency order)

1. `Layout`: abstract geometry of a star (hub square, K, w, u, v, per-spoke H, x, access walk, lanes, child
   entries) with only incidence and adjacency conditions. Walk effects come from `Moves/Walk.lean` (`formPerm`).
2. `Service`: `exists_service`, one service with exact board effect and FIFO list equations
   `C K :: exportQ.map C = exportQ.map B ++ [out]` and `B e :: deliveryQ.map C = deliveryQ.map B ++ [B K]`.
3. `Ledger`: the scheduling ledger as arithmetic: `Good.step`, `peak_sum`, `harmonic_dyadic`, `services_le`.
4. `Spec`, `Inner`, `InnerService`: the static data, the inner invariant, and one service preserving it.
5. `Rounds`: helper rounds.
6. `Congr`: relabelling and changing the carrier.
7. `Wrap`: the request wrapper.
8. `Direct`: direct exchanges, with child substitution.
9. `Node`: records and `Holds`.
10. `Request`, `RequestCases`: the eight policy cases.
11. `Laws`: relax, transport, substitute and init.
12. `Finish`: drain, children's finishes, final sort and the budget.
13. `Region`: `StarSpec.region`.

## Refinements made during the formalisation

- **Protected cells are not needed** in this design:
  - u and v are swapped in pairs by services and by the wrapper;
  - K's seed and H_j are restored;
  - direct exchanges pick two of three hub parity cells {u, v, u2} that differ from the target.
- **The node's entry is a single pair** (e_P, z_P). The node's strip is {e_P, z_P}.
- **The mid-request inner invariant** uses a role classifier r, effective counts (ecNow, acNow) and a carrier
  kind (real, token or source) instead of `Sound`. `Sound.exchange` restores `Sound` at request end.
- **Ledger cap is B = β** (P's lead allowance). Before every service, Σ credit = ecNow − acNow ≤ ec − ac ≤ lead ≤ β.
- **Child allowance:** β_j = peak_j.toNat + |E_j| + |D_j| + 2. This holds because child lead = credit_j + liveE_j + accD_j.
- **Rates contract with depth:** rate_P ≈ c·s_P + 9·rate_Q (for J = 2⁸); with rate_Q ∝ s_P/16 the ratio is 9/16 < 1.
- **Ledger refinement.** `idle` counts token services on retired spokes, which happen only in the drain. `Holds`
  records `idle = 0` before finishing.
