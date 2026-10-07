import NestedRouting.Interface.RoleExchange
import NestedRouting.Board.Paths

/-! The abstract region interface for nested star routing. A region is a
paused set of cells together with a strip of outside cells where callers
deliver tiles: an entry is an input cell and a blank cell in the strip.
Every node of the hierarchy, leaf or star router, is meant to implement
`Region`; a parent uses only these fields.

A request exchanges one external tile for the policy-selected occupant;
the blank returns, and every cell outside the region and the input is
restored. Finishing may also permute the strip (parity repair).
Records are indexed by a lead allowance `β` that may only grow, so a
parent can raise a child's allowance to its historical peak credit; the
budget is affine in `β`, so peak-credit sums bound summed budgets. -/
namespace SlidingPuzzle.NestedRouting.Interface
open Finset TileRoles
open SlidingPuzzle.NestedRouting.ReservePolicy

variable {n : Nat} [NeZero n]

/-- Static data. The goal board names each final tile by its home cell;
core and reserve cells are homes, spare cells end with helpers. -/
structure Frame (n : Nat) [NeZero n] where
  goal : Board n
  coreCells : Finset (Cell n)
  reserveCells : Finset (Cell n)
  spareCells : Finset (Cell n)
  strip : Finset (Cell n)
  /-- Admissible calls: input cell and blank cell. -/
  Entry : Cell n → Cell n → Prop
  core_reserve : Disjoint coreCells reserveCells
  core_spare : Disjoint coreCells spareCells
  reserve_spare : Disjoint reserveCells spareCells
  strip_out : Disjoint strip (coreCells∪reserveCells∪spareCells)
  entry_strip : ∀ e z, Entry e z → e∈strip ∧ z∈strip ∧ e≠z
  goal_nonzero : ∀ x∈coreCells∪reserveCells, goal x≠0

namespace Frame
variable (F : Frame n)

def cells : Finset (Cell n) := F.coreCells∪F.reserveCells∪F.spareCells
def M : Nat := F.coreCells.card
def r : Nat := F.reserveCells.card
def g : Nat := F.spareCells.card
def coreGoals : Finset (Tile n) := F.coreCells.image F.goal
def reserveGoals : Finset (Tile n) := F.reserveCells.image F.goal

/-- What the caller must certify about an arrival of the given role. A
helper may carry any label, even one of this region's own goals: a parent's
unexported reserve source can return as a token (seen in the prototype). -/
def Label : Arrival → Tile n → Prop
  | .core, t => t∈F.coreGoals
  | .reserve, t => t∈F.reserveGoals
  | .helper, t => t≠0

theorem cells_card : F.cells.card=F.M+F.r+F.g := by
  unfold cells M r g
  rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨F.core_spare,F.reserve_spare⟩),
    card_union_of_disjoint F.core_reserve]

theorem coreGoals_card : F.coreGoals.card=F.M :=
  card_image_of_injective _ F.goal.injective

theorem reserveGoals_card : F.reserveGoals.card=F.r :=
  card_image_of_injective _ F.goal.injective

/-- Initial roles are assigned by cell: the occupants of core, reserve and
spare cells are core sources, reserve sources and helpers. -/
def cellRoles (B : Board n) : Roles n := fun i =>
  match i with
  | .coreSource => F.coreCells.image B
  | .reserveSource => F.reserveCells.image B
  | .helper => F.spareCells.image B
  | .coreFinal => ∅
  | .reserveFinal => ∅

theorem strip_notMem {x : Cell n} (hx : x∈F.strip) : x∉F.cells :=
  disjoint_left.mp F.strip_out hx

theorem entry_input {e z : Cell n} (h : F.Entry e z) : e∉F.cells :=
  F.strip_notMem (F.entry_strip e z h).1

theorem entry_blank {e z : Cell n} (h : F.Entry e z) : z∉F.cells :=
  F.strip_notMem (F.entry_strip e z h).2.1

end Frame

/-- What every record guarantees about the literal region contents: the
exact five-role inventory, the policy counters, and label semantics. -/
structure Sound (F : Frame n) (B : Board n) (p : Roles n) (c : Counts) : Prop
    extends State F.cells B F.M F.r F.g p c where
  coreFinal_goal : p .coreFinal⊆F.coreGoals
  reserveFinal_goal : p .reserveFinal⊆F.reserveGoals
  helper_nonzero : (0 : Tile n)∉p .helper
  coreSource_nonzero : (0 : Tile n)∉p .coreSource
  reserveSource_nonzero : (0 : Tile n)∉p .reserveSource

def Lead (β : Nat) (c : Counts) : Prop := c.ec+c.er≤c.ac+c.ar+β

/-- An ancestor may replace helpers inside a paused region. It must fix
every other occupant and the blank label. -/
structure Substitution (p : Roles n) (π : Equiv.Perm (Tile n)) : Prop where
  fixes : ∀ i, i≠Role.helper → ∀ t∈p i, π t=t
  zero : π 0=0

def substRoles (p : Roles n) (π : Equiv.Perm (Tile n)) : Roles n :=
  fun i => if i=Role.helper then (p i).image π else p i

/-- The data of a region, before its laws. -/
structure Core (n : Nat) [NeZero n] extends Frame n where
  Rec : Type
  Holds : Nat → Rec → Board n → Prop
  roles : Rec → Roles n
  counts : Rec → Counts
  /-- Cumulative length of all paths this region has run, children included. -/
  work : Rec → Nat
  /-- Total work, finishing included, is at most `base+rate*β`. -/
  base : Nat
  rate : Nat
  Prepared : Board n → Prop

def Core.budget (Q : Core n) (β : Nat) : Nat := Q.base+Q.rate*β

/-- A completed source-first request. -/
structure Response (Q : Core n) (β : Nat) (s : Q.Rec) (B : Board n) (input : Arrival)
    (e : Cell n) where
  board : Board n
  path : Path B board
  next : Q.Rec
  holds : Q.Holds β next board
  blank : blank board=blank B
  fixed : ∀ x, x∉Q.cells → x≠e → board x=B x
  exported : board e∈Q.roles s (select Q.M Q.r (Q.counts s) input).role
  roles : Q.roles next=updateRoles (Q.roles s) (board e) (B e) input.role
  counts : Q.counts next=advance (Q.counts s) input (select Q.M Q.r (Q.counts s) input)
  work : Q.work s+path.length≤Q.work next

/-- Finishing after every goal has arrived: goals reach their homes. The
strip may be permuted; spare cells and strip keep their contents as a set. -/
structure Finish (Q : Core n) (β : Nat) (s : Q.Rec) (B : Board n) where
  board : Board n
  path : Path B board
  blank : blank board=blank B
  fixed : ∀ x, x∉Q.cells → x∉Q.strip → board x=B x
  placed : ∀ x∈Q.coreCells∪Q.reserveCells, board x=Q.goal x
  cost : Q.work s+path.length≤Q.budget β

structure Region (n : Nat) [NeZero n] extends Core n where
  sound : ∀ {β s B}, Holds β s B → Sound toFrame B (roles s) (counts s)
  relax : ∀ {β β' s B}, Holds β s B → β≤β' → Holds β' s B
  /-- Paused records depend only on the region's own cells. The path is the
  other work done meanwhile; it is supplied because concrete records may log
  the literal board history. It is not charged to `work`. -/
  transport : ∀ {β s B C}, Holds β s B → Path B C → (∀ x∈toFrame.cells, C x=B x) → Holds β s C
  prepared_local : ∀ {B C : Board n}, Prepared B → (∀ x∈toFrame.cells, C x=B x) → Prepared C
  init : ∀ {B}, Prepared B →
    ∃ s, Holds 0 s B ∧ roles s=toFrame.cellRoles B ∧ counts s=⟨0,0,0,0⟩ ∧ work s=0
  substitute : ∀ {β s B C} (π : Equiv.Perm (Tile n)), Holds β s B → Path B C →
    Substitution (roles s) π → (∀ x∈toFrame.cells, C x=π (B x)) →
    ∃ s', Holds β s' C ∧ roles s'=substRoles (roles s) π ∧ counts s'=counts s ∧ work s'=work s
  request : ∀ {β s B} (input : Arrival) {e z : Cell n}, Holds β s B →
    toFrame.Entry e z → blank B=z → toFrame.Label input (B e) →
    RequestGuard toFrame.M toFrame.r (counts s) input →
    Lead β (advance (counts s) input (select toFrame.M toFrame.r (counts s) input)) →
    Nonempty (Response toCore β s B input e)
  finish : ∀ {β s B} {e z : Cell n}, Holds β s B → toFrame.Entry e z → blank B=z →
    (counts s).ac=toFrame.M → (counts s).ar=toFrame.r → Nonempty (Finish toCore β s B)

namespace Sound
variable {F : Frame n} {B : Board n} {p : Roles n} {c : Counts}

theorem nonzero_role (h : Sound F B p c) (i : Role) : (0 : Tile n)∉p i := by
  intro hz
  cases i with
  | coreSource => exact h.coreSource_nonzero hz
  | reserveSource => exact h.reserveSource_nonzero hz
  | helper => exact h.helper_nonzero hz
  | coreFinal =>
    obtain ⟨x,hx,hgx⟩ := mem_image.mp (h.coreFinal_goal hz)
    exact F.goal_nonzero x (mem_union_left _ hx) hgx
  | reserveFinal =>
    obtain ⟨x,hx,hgx⟩ := mem_image.mp (h.reserveFinal_goal hz)
    exact F.goal_nonzero x (mem_union_right _ hx) hgx

/-- A paused region holds no blank. -/
theorem nonzero (h : Sound F B p c) {x : Cell n} (hx : x∈F.cells) : B x≠0 := by
  intro hz
  have hm : B x∈contents p := by
    rw [←h.inventory.exact]
    exact mem_image_of_mem B hx
  obtain ⟨i,_,hi⟩ := mem_biUnion.mp hm
  exact h.nonzero_role i (hz ▸ hi)

/-- A core-goal label on an outside input supplies the core guard. -/
theorem guard_core (h : Sound F B p c) {e : Cell n} (he : e∉F.cells)
    (label : F.Label .core (B e)) : RequestGuard F.M F.r c .core :=
  h.toState.fresh_core F.coreGoals h.coreFinal_goal F.coreGoals_card.le e he label

theorem guard_reserve (h : Sound F B p c) {e : Cell n} (he : e∉F.cells)
    (label : F.Label .reserve (B e)) : RequestGuard F.M F.r c .reserve :=
  h.toState.fresh_reserve F.reserveGoals h.reserveFinal_goal F.reserveGoals_card.le e he label

theorem coreFinal_complete (h : Sound F B p c) (done : c.ac=F.M) :
    p .coreFinal=F.coreGoals :=
  eq_of_subset_of_card_le h.coreFinal_goal (by rw [F.coreGoals_card,h.coreFinals,done])

theorem reserveFinal_complete (h : Sound F B p c) (done : c.ar=F.r) :
    p .reserveFinal=F.reserveGoals :=
  eq_of_subset_of_card_le h.reserveFinal_goal (by rw [F.reserveGoals_card,h.reserveFinals,done])

/-- After every goal has arrived, every source has been exported. -/
theorem sources_done (h : Sound F B p c) (core : c.ac=F.M) (reserve : c.ar=F.r) :
    c.ec=F.M ∧ c.er=F.r := by
  have v := h.valid
  simp only [Counts.Valid] at v
  omega

omit [NeZero n] in
theorem contents_eq (p : Roles n) :
    contents p=p .coreSource∪p .reserveSource∪p .helper∪p .coreFinal∪p .reserveFinal := by
  have enum : (univ : Finset Role)={.coreSource,.reserveSource,.helper,.coreFinal,.reserveFinal} := by
    decide
  show (univ : Finset Role).biUnion (fun i => (p i : Finset (Tile n)))=_
  rw [enum]
  simp only [biUnion_insert,singleton_biUnion,union_assoc]

/-- The prepared state: roles by cell, no blank inside, zero counters. -/
theorem initial (F : Frame n) (B : Board n) (nonzero : ∀ x∈F.cells, B x≠0) :
    Sound F B (F.cellRoles B) ⟨0,0,0,0⟩ := by
  have zero (S : Finset (Cell n)) (sub : S⊆F.cells) : (0 : Tile n)∉S.image B := by
    intro hz
    obtain ⟨x,hx,h0⟩ := mem_image.mp hz
    exact nonzero x (sub hx) h0
  have sCore : F.coreCells⊆F.cells := fun x hx => by simp [Frame.cells,hx]
  have sReserve : F.reserveCells⊆F.cells := fun x hx => by simp [Frame.cells,hx]
  have sSpare : F.spareCells⊆F.cells := fun x hx => by simp [Frame.cells,hx]
  have img (S T : Finset (Cell n)) (d : Disjoint S T) : Disjoint (S.image B) (T.image B) :=
    disjoint_image B.injective |>.mpr d
  refine ⟨⟨⟨?_,?_⟩,F.cells_card,?_,?_,rfl,rfl,Counts.Valid.zero⟩,by simp [Frame.cellRoles],
    by simp [Frame.cellRoles],zero _ sSpare,zero _ sCore,zero _ sReserve⟩
  · intro i j hij
    have cr := (disjoint_image B.injective).mpr F.core_reserve
    have cs := (disjoint_image B.injective).mpr F.core_spare
    have rs := (disjoint_image B.injective).mpr F.reserve_spare
    cases i <;> cases j <;>
      first
        | exact absurd rfl hij
        | exact disjoint_empty_left _
        | exact disjoint_empty_right _
        | exact cr
        | exact cr.symm
        | exact cs
        | exact cs.symm
        | exact rs
        | exact rs.symm
  · rw [contents_eq]
    simp [Frame.cellRoles,Frame.cells,image_union]
  · simp [Frame.cellRoles,Frame.M,card_image_of_injective _ B.injective]
  · simp [Frame.cellRoles,Frame.r,card_image_of_injective _ B.injective]

/-- One tile enters, the policy-selected occupant leaves. This is the role
and counter update of every completed request, at every depth. -/
theorem exchange (h : Sound F B p c) {C : Board n} (input : Arrival)
    (guard : RequestGuard F.M F.r c input) {old fresh : Tile n}
    (oldmem : old∈p (select F.M F.r c input).role)
    (outside : ∀ i, fresh∉p i) (label : F.Label input fresh)
    (physical : F.cells.image C=insert fresh ((F.cells.image B).erase old)) :
    Sound F C (updateRoles p old fresh input.role) (advance c input (select F.M F.r c input)) := by
  refine ⟨h.toState.after_exchange input guard old fresh oldmem outside physical,
    ?_,?_,?_,?_,?_⟩
  · intro t ht
    rcases (mem_updateRoles _ _ _ _ _ _).mp ht with ⟨hr,rfl⟩ | ⟨_,ht⟩
    · cases input <;> simp only [Arrival.role,reduceCtorEq] at hr
      exact label
    · exact h.coreFinal_goal ht
  · intro t ht
    rcases (mem_updateRoles _ _ _ _ _ _).mp ht with ⟨hr,rfl⟩ | ⟨_,ht⟩
    · cases input <;> simp only [Arrival.role,reduceCtorEq] at hr
      exact label
    · exact h.reserveFinal_goal ht
  · intro hz
    rcases (mem_updateRoles _ _ _ _ _ _).mp hz with ⟨hr,h0⟩ | ⟨_,hz⟩
    · cases input <;> simp only [Arrival.role,reduceCtorEq] at hr
      exact label h0.symm
    · exact h.helper_nonzero hz
  · intro hz
    rcases (mem_updateRoles _ _ _ _ _ _).mp hz with ⟨hr,_⟩ | ⟨_,hz⟩
    · cases input <;> simp only [Arrival.role,reduceCtorEq] at hr
    · exact h.coreSource_nonzero hz
  · intro hz
    rcases (mem_updateRoles _ _ _ _ _ _).mp hz with ⟨hr,_⟩ | ⟨_,hz⟩
    · cases input <;> simp only [Arrival.role,reduceCtorEq] at hr
    · exact h.reserveSource_nonzero hz

/-- Soundness depends only on the region's own cells. -/
theorem transport (h : Sound F B p c) {C : Board n} (same : ∀ x∈F.cells, C x=B x) :
    Sound F C p c :=
  { h with inventory := ⟨h.inventory.disjoint,(image_congr same).trans h.inventory.exact⟩ }

/-- Soundness survives an ancestor's helper substitution. -/
theorem substitute (h : Sound F B p c) {π : Equiv.Perm (Tile n)} (sub : Substitution p π)
    {C : Board n} (phys : ∀ x∈F.cells, C x=π (B x)) : Sound F C (substRoles p π) c := by
  have keep (i : Role) (hi : i≠Role.helper) : substRoles p π i=p i := by simp [substRoles,hi]
  have hel : substRoles p π .helper=(p .helper).image π := by simp [substRoles]
  have fixImg (i : Role) (hi : i≠Role.helper) : (p i).image π=p i := by
    conv_rhs => rw [←image_id (s:=p i)]
    exact image_congr (fun t ht => sub.fixes i hi t ht)
  have cross (j : Role) (hj : j≠Role.helper) : Disjoint ((p .helper).image π) (p j) := by
    apply disjoint_left.mpr
    intro t ht tj
    obtain ⟨a,ha,rfl⟩ := mem_image.mp ht
    have same : a=π a := π.injective (sub.fixes j hj _ tj).symm
    exact disjoint_left.mp (h.inventory.disjoint _ _ (Ne.symm hj)) ha (same ▸ tj)
  refine ⟨⟨⟨?_,?_⟩,F.cells_card,?_,?_,?_,?_,h.valid⟩,?_,?_,?_,?_,?_⟩
  · intro i j hij
    by_cases hi : i=Role.helper
    · subst hi
      rw [hel,keep j (Ne.symm hij)]
      exact cross j (Ne.symm hij)
    · by_cases hj : j=Role.helper
      · subst hj
        rw [hel,keep i hi]
        exact (cross i hi).symm
      · rw [keep i hi,keep j hj]
        exact h.inventory.disjoint i j hij
  · have hB : F.cells.image C=(F.cells.image B).image π := by
      rw [image_image]
      exact image_congr (fun x hx => phys x hx)
    rw [hB,h.inventory.exact,contents_eq,contents_eq]
    simp only [image_union,fixImg Role.coreSource (by decide),fixImg Role.reserveSource (by decide),
      fixImg Role.coreFinal (by decide),fixImg Role.reserveFinal (by decide),hel,
      keep Role.coreSource (by decide),keep Role.reserveSource (by decide),
      keep Role.coreFinal (by decide),keep Role.reserveFinal (by decide)]
  · rw [keep _ (by decide)]; exact h.coreSources
  · rw [keep _ (by decide)]; exact h.reserveSources
  · rw [keep _ (by decide)]; exact h.coreFinals
  · rw [keep _ (by decide)]; exact h.reserveFinals
  · rw [keep _ (by decide)]; exact h.coreFinal_goal
  · rw [keep _ (by decide)]; exact h.reserveFinal_goal
  · rw [hel]
    intro hz
    obtain ⟨a,ha,h0⟩ := mem_image.mp hz
    have a0 : a=0 := π.injective (h0.trans sub.zero.symm)
    exact h.helper_nonzero (a0 ▸ ha)
  · rw [keep _ (by decide)]; exact h.coreSource_nonzero
  · rw [keep _ (by decide)]; exact h.reserveSource_nonzero

end Sound

/-! ### Satisfiability check

A region made only of spare cells. Its policy admits no request, so this
only shows that the laws above are jointly consistent. -/
section Spare
variable (goal : Board n) (S T : Finset (Cell n)) (apart : Disjoint T S)

end Spare

end SlidingPuzzle.NestedRouting.Interface
