import NestedRouting.Interface.Region
import NestedRouting.Moves.Walk
import NestedRouting.Moves.LocalThreeCycle

/-! The abstract geometry of a star router: a hub square with the carrier
cell `K`, two parity cells `u v` and the park cell `w`; for each spoke a hub
cell `H j`, an access walk from `w` to the loop start `x j`, an export lane
ending at the child's blank cell `z j`, and a delivery lane starting at the
child's input cell `e j`. Only incidence and adjacency are recorded here;
concrete layouts prove these fields. -/
namespace SlidingPuzzle.NestedRouting.Interface
open Finset

variable {n : Nat} [NeZero n]

/-- A three-cycle of three cells of an embedded square with the blank on a
fourth cell of it: the default implementation of the exchanges. -/
theorem square_cycle {m : Nat} (ι : Cell m ↪ Cell n)
    (hι : ∀ a b, gridDistance a b=1 → gridDistance (ι a) (ι b)=1) (hm : 6≤m)
    {w a b c : Cell m} (hab : a≠b) (hac : a≠c) (hbc : b≠c) (hwa : w≠a) (hwb : w≠b) (hwc : w≠c)
    (B : Board n) (hB : blank B=ι w) :
    ∃ C : Board n, ∃ p : Path B C, p.length≤54*m ∧ blank C=ι w ∧
      Cycle3.IsCycle B C (ι a) (ι b) (ι c) := by
  have : NeZero m := ⟨by omega⟩
  have nz {x : Cell m} (hx : w≠x) : B (ι x)≠0 :=
    fun hz => hx (ι.injective ((B.symm_apply_eq.mpr hz.symm).symm.trans hB)).symm
  obtain ⟨C,p,lp,bl,s1,s2,s3,fx⟩ :=
    LocalStaging.exists_three_cycle_local ι hι B hm ⟨w,hB.symm⟩ a b c hab hac hbc (nz hwa) (nz hwb) (nz hwc)
  exact ⟨C,p,lp,bl.trans hB,s1,s2,s3,fx⟩

/-- The same, for three cells of `Cell n` in the square's range. -/
theorem range_cycle {m : Nat} (ι : Cell m ↪ Cell n)
    (hι : ∀ a b, gridDistance a b=1 → gridDistance (ι a) (ι b)=1) (hm : 6≤m)
    {x y z c : Cell n} (hx : x∈Set.range ι) (hy : y∈Set.range ι) (hz : z∈Set.range ι)
    (hc : c∈Set.range ι) (xy : x≠y) (xz : x≠z) (yz : y≠z) (cx : c≠x) (cy : c≠y) (cz : c≠z)
    (B : Board n) (hB : blank B=c) :
    ∃ C : Board n, ∃ p : Path B C, p.length≤54*m ∧ blank C=c ∧ Cycle3.IsCycle B C x y z := by
  obtain ⟨a,rfl⟩ := hx; obtain ⟨b,rfl⟩ := hy; obtain ⟨d,rfl⟩ := hz; obtain ⟨w,rfl⟩ := hc
  exact square_cycle ι hι hm (fun e => xy (congrArg ι e)) (fun e => xz (congrArg ι e))
    (fun e => yz (congrArg ι e)) (fun e => cx (congrArg ι e)) (fun e => cy (congrArg ι e))
    (fun e => cz (congrArg ι e)) B hB

/-- The cells a service on one spoke cycles through. -/
def loopOf (x : Cell n) (E : List (Cell n)) (z e : Cell n) (D : List (Cell n)) (hH : Cell n) :
    List (Cell n) :=
  x :: E++[z,e]++D++[hH]

structure StarGeom (n J : Nat) [NeZero n] (Q : Fin J → Region n) where
  h : Nat
  hub : Cell h ↪ Cell n
  hub_adj : ∀ a b, gridDistance a b=1 → gridDistance (hub a) (hub b)=1
  hub_side : 6≤h
  K : Cell h
  u : Cell h
  v : Cell h
  w : Cell h
  K_u : K≠u
  K_v : K≠v
  u_v : u≠v
  w_K : w≠K
  w_u : w≠u
  w_v : w≠v
  H : Fin J → Cell h
  H_K : ∀ j, H j≠K
  H_u : ∀ j, H j≠u
  H_v : ∀ j, H j≠v
  H_w : ∀ j, H j≠w
  H_inj : Function.Injective H
  accessTail : Fin J → List (Cell n)
  x : Fin J → Cell n
  exportLane : Fin J → List (Cell n)
  z : Fin J → Cell n
  e : Fin J → Cell n
  deliveryLane : Fin J → List (Cell n)
  access_last : ∀ j, (hub w :: accessTail j).getLast (List.cons_ne_nil _ _)=x j
  access_chain : ∀ j, Chained (hub w :: accessTail j)
  out_chain : ∀ j, Chained (x j :: (exportLane j++[z j]))
  back_chain : ∀ j, Chained (z j :: (e j :: deliveryLane j++[hub (H j),x j]))
  access_nodup : ∀ j, (hub w :: accessTail j).Nodup
  loop_nodup : ∀ j, (loopOf (x j) (exportLane j) (z j) (e j) (deliveryLane j) (hub (H j))).Nodup
  /-- The access walk meets the loop only at its end. -/
  access_loop : ∀ j c, c∈hub w :: accessTail j →
    c∈loopOf (x j) (exportLane j) (z j) (e j) (deliveryLane j) (hub (H j)) → c=x j
  /-- The carrier and parity cells lie on no access walk and no loop. -/
  hub_access : ∀ j, hub K∉hub w :: accessTail j ∧ hub u∉hub w :: accessTail j ∧
    hub v∉hub w :: accessTail j
  hub_loop : ∀ j, hub K∉loopOf (x j) (exportLane j) (z j) (e j) (deliveryLane j) (hub (H j)) ∧
    hub u∉loopOf (x j) (exportLane j) (z j) (e j) (deliveryLane j) (hub (H j)) ∧
    hub v∉loopOf (x j) (exportLane j) (z j) (e j) (deliveryLane j) (hub (H j))
  entry : ∀ j, (Q j).Entry (e j) (z j)
  /-- Loops, access walks and hub cells avoid every child. -/
  loop_child : ∀ j j' c, c∈loopOf (x j) (exportLane j) (z j) (e j) (deliveryLane j) (hub (H j)) →
    c∉(Q j').cells
  access_child : ∀ j c, c∈hub w :: accessTail j → c∉(Q j).cells
  hub_child : ∀ j, hub K∉(Q j).cells ∧ hub u∉(Q j).cells ∧ hub v∉(Q j).cells
  children_disjoint : ∀ j j', j≠j' → Disjoint (Q j).cells (Q j').cells
  loops_disjoint : ∀ j j', j≠j' → ∀ c,
    c∈loopOf (x j) (exportLane j) (z j) (e j) (deliveryLane j) (hub (H j)) →
    c∉loopOf (x j') (exportLane j') (z j') (e j') (deliveryLane j') (hub (H j'))

/-- A star geometry with its hub exchange: for spoke `j`, a cycle of `H j`, the
carrier and a third cell `hc j`, forward and back, with the blank on the park
cell. -/
structure StarLayout (n J : Nat) [NeZero n] (Q : Fin J → Region n) extends StarGeom n J Q where
  hc : Fin J → Cell n
  hcost : Fin J → Nat
  hX : ∀ (j : Fin J) (B : Board n), blank B=hub w → ∃ C : Board n, ∃ p : Path B C,
    p.length≤hcost j ∧ blank C=hub w ∧ Cycle3.IsCycle B C (hub (H j)) (hub K) (hc j)
  hX' : ∀ (j : Fin J) (B : Board n), blank B=hub w → ∃ C : Board n, ∃ p : Path B C,
    p.length≤hcost j ∧ blank C=hub w ∧ Cycle3.IsCycle B C (hub K) (hub (H j)) (hc j)
  hc_access : ∀ j, hc j∉hub w :: accessTail j
  hc_loop : ∀ j, hc j∉loopOf (x j) (exportLane j) (z j) (e j) (deliveryLane j) (hub (H j))
  hc_child : ∀ j, hc j∉(Q j).cells
  hc_K : ∀ j, hc j≠hub K

/-- The default hub exchange: three-cycles in the hub square, with `u` as the
third cell. -/
def StarGeom.square {J : Nat} {Q : Fin J → Region n} (G : StarGeom n J Q) : StarLayout n J Q :=
  { G with
    hc := fun _ => G.hub G.u
    hcost := fun _ => 54*G.h
    hX := fun j B hB => square_cycle G.hub G.hub_adj G.hub_side (G.H_K j) (G.H_u j) G.K_u
      (G.H_w j).symm G.w_K G.w_u B hB
    hX' := fun j B hB => square_cycle G.hub G.hub_adj G.hub_side (fun h => G.H_K j h.symm) G.K_u
      (G.H_u j) G.w_K (G.H_w j).symm G.w_u B hB
    hc_access := fun j => (G.hub_access j).2.1
    hc_loop := fun j => (G.hub_loop j).2.1
    hc_child := fun j => (G.hub_child j).2.1
    hc_K := fun _ h => G.K_u (G.hub.injective h).symm }

namespace StarLayout
variable {J : Nat} {Q : Fin J → Region n} (L : StarLayout n J Q)

def access (j : Fin J) : List (Cell n) := L.hub L.w :: L.accessTail j
def loop (j : Fin J) : List (Cell n) :=
  loopOf (L.x j) (L.exportLane j) (L.z j) (L.e j) (L.deliveryLane j) (L.hub (L.H j))
/-- Export queue, head (hub side) first; the child's last output sits at `z`. -/
def exportQ (j : Fin J) : List (Cell n) := L.exportLane j++[L.z j]
/-- Delivery queue, head (child side) first. -/
def deliveryQ (j : Fin J) : List (Cell n) := L.e j :: L.deliveryLane j

theorem mem_loop_of_exportQ {j : Fin J} {c : Cell n} (hc : c∈L.exportQ j) : c∈L.loop j := by
  simp only [exportQ,List.mem_append,List.mem_singleton] at hc
  simp only [loop,loopOf,List.mem_cons,List.mem_append]
  tauto

theorem mem_loop_of_deliveryQ {j : Fin J} {c : Cell n} (hc : c∈L.deliveryQ j) : c∈L.loop j := by
  simp only [deliveryQ,List.mem_cons] at hc
  simp only [loop,loopOf,List.mem_cons,List.mem_append]
  tauto

theorem x_mem_loop (j : Fin J) : L.x j∈L.loop j := by simp [loop,loopOf]
theorem H_mem_loop (j : Fin J) : L.hub (L.H j)∈L.loop j := by simp [loop,loopOf]
theorem e_mem_deliveryQ (j : Fin J) : L.e j∈L.deliveryQ j := by simp [deliveryQ]

theorem x_notMem_exportQ (j : Fin J) : L.x j∉L.exportQ j := by
  have h := L.loop_nodup j
  simp only [loopOf,List.cons_append,List.nodup_cons,List.mem_append] at h
  intro hx
  apply h.1
  simp only [exportQ,List.mem_append,List.mem_singleton] at hx
  simp only [List.mem_cons]
  tauto

end StarLayout
end SlidingPuzzle.NestedRouting.Interface
