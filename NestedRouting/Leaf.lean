import NestedRouting.Interface.Region
import NestedRouting.Geometry.Placement
import NestedRouting.Moves.ThreeCycle

/-! A brute-force leaf. The region and its strip fill a placed square of
side `m`. Every request is one three-cycle `(e, q, u)`: the input in, the
selected occupant out, and a spare cell `u` holding the input, at most
`rw q ≤ rcost` slides. Finishing sorts the region's cells, at most `fcost`
slides. Both moves are supplied by the layout.

Source tiles never move: a request changes only `q` (which receives `u`'s
tile, never a source) and the spare cell `u`. So each core cell exports its
source once, and the core exports cost at most `Σ_core rw`, by the potential
`Φ`, the weights of the core cells that still hold sources. The other
exports, reserve and helper, are at most `r + β`, at `rcost` each. -/
namespace SlidingPuzzle.NestedRouting.Interface
open Finset TileRoles
open SlidingPuzzle.NestedRouting.ReservePolicy

variable {n : Nat} [NeZero n]

/-- Local data: core, reserve and spare cells of the square; the rest of
the square is the strip. -/
structure LeafSpec (n : Nat) [NeZero n] where
  m : Nat
  place : Placement m n
  goal : Board n
  core : Finset (Cell m)
  reserve : Finset (Cell m)
  spare : Finset (Cell m)
  core_reserve : Disjoint core reserve
  core_spare : Disjoint core spare
  reserve_spare : Disjoint reserve spare
  side : 6≤m
  six : 6≤spare.card
  goal_nonzero : ∀ x∈core∪reserve, goal (place.embed x)≠0
  /-- The entry pairs, in local cells of the strip. -/
  entry : Cell m → Cell m → Prop
  entry_strip : ∀ e z, entry e z → e∉core∪reserve∪spare ∧ z∉core∪reserve∪spare ∧ e≠z
  /-- The request exchange `(e, x, u)` for any cell `x`, through a spare cell `u`,
  at most `rw x ≤ rcost` slides. -/
  rcost : Nat
  rw : Cell m → Nat
  rw_le : ∀ x, rw x≤rcost
  rX : ∀ e z, entry e z → ∀ B : Board n, blank B=place.embed z → ∀ x∈core∪reserve∪spare,
    ∃ C : Board n, ∃ path : Path B C, ∃ u∈spare, u≠x ∧ blank C=place.embed z ∧
      Cycle3.IsCycle B C (place.embed e) (place.embed x) (place.embed u) ∧ path.length≤rw x
  /-- The final sort of the region's cells. -/
  fcost : Nat
  fX : ∀ e z, entry e z → ∀ B : Board n, blank B=place.embed z →
    (∀ x∈core∪reserve, ∃ y∈core∪reserve∪spare, B (place.embed y)=goal (place.embed x)) →
    ∃ C : Board n, ∃ path : Path B C, path.length≤fcost ∧ blank C=blank B ∧
      (∀ x, x∉(core∪reserve∪spare).map place.embed → C x=B x) ∧
      ∀ x∈core∪reserve, C (place.embed x)=goal (place.embed x)

namespace LeafSpec
variable (L : LeafSpec n)

def ι : Cell L.m ↪ Cell n := L.place.embed

def stripLocal : Finset (Cell L.m) := univ \ (L.core∪L.reserve∪L.spare)

theorem adjacent (x y : Cell L.m) (h : gridDistance x y=1) : gridDistance (L.ι x) (L.ι y)=1 := by
  rw [ι,L.place.distance]
  exact h

def frame : Frame n where
  goal := L.goal
  coreCells := L.core.map L.ι
  reserveCells := L.reserve.map L.ι
  spareCells := L.spare.map L.ι
  strip := L.stripLocal.map L.ι
  Entry e z := ∃ e' z', L.entry e' z' ∧ L.ι e'=e ∧ L.ι z'=z
  core_reserve := disjoint_map _ |>.mpr L.core_reserve
  core_spare := disjoint_map _ |>.mpr L.core_spare
  reserve_spare := disjoint_map _ |>.mpr L.reserve_spare
  strip_out := by
    rw [←map_union,←map_union]
    exact disjoint_map _ |>.mpr (sdiff_disjoint)
  entry_strip := by
    rintro _ _ ⟨e',z',h,rfl,rfl⟩
    obtain ⟨he,hz,ne⟩ := L.entry_strip e' z' h
    exact ⟨mem_map_of_mem _ (mem_sdiff.mpr ⟨mem_univ _,he⟩),mem_map_of_mem _ (mem_sdiff.mpr ⟨mem_univ _,hz⟩),
      fun h => ne (L.ι.injective h)⟩
  goal_nonzero := by
    intro x hx
    rw [←map_union] at hx
    obtain ⟨y,hy,rfl⟩ := mem_map.mp hx
    exact L.goal_nonzero y hy

theorem cells_eq : L.frame.cells=(L.core∪L.reserve∪L.spare).map L.ι := by
  simp [Frame.cells,frame,map_union]

theorem square_cover (x : Cell L.m) : L.ι x∈L.frame.cells ∨ L.ι x∈L.frame.strip := by
  rw [cells_eq]
  by_cases hx : x∈L.core∪L.reserve∪L.spare
  · exact Or.inl (mem_map_of_mem _ hx)
  · exact Or.inr (mem_map_of_mem _ (mem_sdiff.mpr ⟨mem_univ _,hx⟩))

theorem M_eq : L.frame.M=L.core.card := card_map _
theorem r_eq : L.frame.r=L.reserve.card := card_map _
theorem g_eq : L.frame.g=L.spare.card := card_map _

/-- Helper exports come only after every core and reserve tile has left;
there are at most `β` of them. -/
def hstep (M r : Nat) (c : Counts) (input : Arrival) : Nat :=
  if select M r c input=.helper then 1 else 0

/-- The lead holds now, and `h` helper exports have happened, all after exhaustion. -/
def HInv (M r β : Nat) (c : Counts) (h : Nat) : Prop :=
  Lead β c ∧ (h=0 ∨ (c.ec=M ∧ c.er=r ∧ h+M+r≤c.ac+c.ar+β))

theorem HInv.zero {M r : Nat} : HInv M r 0 ⟨0,0,0,0⟩ 0 := ⟨by simp [Lead],Or.inl rfl⟩

theorem HInv.relax {M r β β' : Nat} {c : Counts} {h : Nat} (hi : HInv M r β c h) (hb : β≤β') :
    HInv M r β' c h := by
  obtain ⟨l,d⟩ := hi
  refine ⟨by unfold Lead at *; omega,?_⟩
  rcases d with d | ⟨d1,d2,d3⟩
  · exact Or.inl d
  · exact Or.inr ⟨d1,d2,by omega⟩

theorem select_helper {M r : Nat} {c : Counts} {input : Arrival} (guard : RequestGuard M r c input)
    (h : select M r c input=.helper) : M≤c.ec ∧ r≤c.er ∧ input≠.helper := by
  cases input <;> simp only [RequestGuard] at guard <;> simp only [select] at h <;> split_ifs at h <;>
    refine ⟨by omega,by omega,by simp⟩

theorem advance_out (c : Counts) (input : Arrival) (e : Export) :
    (advance c input e).ec+(advance c input e).er=c.ec+c.er+(if e=.helper then 0 else 1) ∧
      (advance c input e).ac+(advance c input e).ar=c.ac+c.ar+(if input=.helper then 0 else 1) := by
  cases input <;> cases e <;> simp [advance] <;> omega

theorem HInv.step {M r β : Nat} {c : Counts} {h : Nat} (v : c.Valid M r) (input : Arrival)
    (guard : RequestGuard M r c input) (hi : HInv M r β c h)
    (lead : Lead β (advance c input (select M r c input))) :
    HInv M r β (advance c input (select M r c input)) (h+hstep M r c input) ∧
      (advance c input (select M r c input)).ec+(advance c input (select M r c input)).er+
        (h+hstep M r c input)=c.ec+c.er+h+1 := by
  obtain ⟨l,d⟩ := hi
  have va := valid_advance v input guard
  unfold hstep
  by_cases hs : select M r c input=.helper
  · obtain ⟨s1,s2,s3⟩ := select_helper guard hs
    obtain ⟨h1,h2,_⟩ := v
    rw [hs] at lead ⊢
    simp only [if_true]
    unfold HInv
    unfold Lead at l lead ⊢
    cases input
    · exact absurd rfl s3
    all_goals simp only [advance,reduceCtorEq,if_false,if_true] at lead ⊢
    all_goals refine ⟨⟨by omega,Or.inr ⟨by omega,by omega,?_⟩⟩,by omega⟩
    all_goals rcases d with d | ⟨_,_,d3⟩ <;> omega
  · have e0 : h=0 := by
      rcases d with d | ⟨d1,d2,_⟩
      · exact d
      · exfalso; apply hs
        cases input <;> simp only [RequestGuard] at guard <;> simp only [select] <;> split_ifs <;> first | rfl | omega
    obtain ⟨o1,_⟩ := advance_out c input (select M r c input)
    simp only [hs,if_false] at o1 ⊢
    exact ⟨⟨lead,Or.inl e0⟩,by omega⟩

theorem HInv.final_other {M r β : Nat} {c : Counts} {h : Nat} (v : c.Valid M r) (hi : HInv M r β c h)
    (core : c.ac=M) (reserve : c.ar=r) : c.er+h≤r+β := by
  obtain ⟨_,d⟩ := hi
  obtain ⟨_,h2,_⟩ := v
  rcases d with d | ⟨_,_,d3⟩ <;> omega

theorem HInv.final {M r β : Nat} {c : Counts} {h : Nat} (v : c.Valid M r) (hi : HInv M r β c h)
    (core : c.ac=M) (reserve : c.ar=r) : c.ec+c.er+h≤M+r+β := by
  obtain ⟨_,d⟩ := hi
  obtain ⟨h1,h2,_⟩ := v
  rcases d with d | ⟨_,_,d3⟩ <;> omega

def budgetBase : Nat := ∑ x∈L.core, L.rw x+L.rcost*L.reserve.card+L.fcost

open Classical in
/-- The weights of the core cells that still hold source tiles. -/
noncomputable def phi (B : Board n) (p : Roles n) : Nat :=
  ∑ x∈L.core, if B (L.ι x)∈p .coreSource then L.rw x else 0

/-- Non-core cells hold no source tiles. -/
def NoSrc (B : Board n) (p : Roles n) : Prop := ∀ y∈L.reserve∪L.spare, B (L.ι y)∉p .coreSource

theorem phi_le (B : Board n) (p : Roles n) : L.phi B p≤∑ x∈L.core, L.rw x := by
  classical
  unfold phi; apply sum_le_sum; intro x _; split_ifs <;> omega

/-- A potential that agrees off `x` and vanishes at `x` drops by `x`'s term. -/
theorem phi_drop {B C : Board n} {p p' : Roles n} (x : Cell L.m)
    (same : ∀ y∈L.core, y≠x → (C (L.ι y)∈p' .coreSource ↔ B (L.ι y)∈p .coreSource))
    (gone : C (L.ι x)∉p' .coreSource) :
    L.phi C p'+(if x∈L.core ∧ B (L.ι x)∈p .coreSource then L.rw x else 0)≤L.phi B p := by
  classical
  unfold phi
  by_cases hx : x∈L.core
  · rw [←add_sum_erase _ _ hx,←add_sum_erase _ _ hx,if_neg gone]
    have : ∑ y∈L.core.erase x, (if C (L.ι y)∈p' .coreSource then L.rw y else 0)=
        ∑ y∈L.core.erase x, (if B (L.ι y)∈p .coreSource then L.rw y else 0) := by
      apply sum_congr rfl; intro y hy
      rw [if_congr (same y (mem_erase.mp hy).2 (mem_erase.mp hy).1) rfl rfl]
    rw [this]
    by_cases h2 : B (L.ι x)∈p .coreSource
    · rw [if_pos ⟨hx,h2⟩,if_pos h2]; omega
    · rw [if_neg (fun h => h2 h.2),if_neg h2]; omega
  · rw [if_neg (by tauto)]
    apply le_of_eq
    apply sum_congr rfl; intro y hy
    rw [if_congr (same y hy (fun e => hx (e ▸ hy))) rfl rfl]

/-- Reserve and helper exports, counted together. -/
theorem other_step (M r : Nat) (c : Counts) (input : Arrival) (h : Nat) :
    (advance c input (select M r c input)).er+(h+hstep M r c input)=
      c.er+h+(if select M r c input=.core then 0 else 1) := by
  unfold hstep
  cases select M r c input <;> simp [advance] <;> omega

def core' : Core n :=
  { L.frame with
    Rec := Roles n × Counts × Nat × Nat
    Holds := fun β s B => Sound L.frame B s.1 s.2.1 ∧ HInv L.frame.M L.frame.r β s.2.1 s.2.2.2 ∧
      L.NoSrc B s.1 ∧ s.2.2.1+L.phi B s.1≤∑ x∈L.core, L.rw x+L.rcost*(s.2.1.er+s.2.2.2)
    roles := fun s => s.1
    counts := fun s => s.2.1
    work := fun s => s.2.2.1
    base := L.budgetBase
    rate := L.rcost
    Prepared := fun B => ∀ x∈L.frame.cells, B x≠0 }

theorem strip_preimage {e : Cell n} (he : e∈L.frame.strip) : ∃ e', L.ι e'=e := by
  obtain ⟨e',_,rfl⟩ := mem_map.mp he
  exact ⟨e',rfl⟩

theorem cell_preimage {x : Cell n} (hx : x∈L.frame.cells) : ∃ x', L.ι x'=x := by
  rw [cells_eq] at hx
  obtain ⟨x',_,rfl⟩ := mem_map.mp hx
  exact ⟨x',rfl⟩

/-- One request: a three-cycle inside the square (input in, the selected tile out, a helper moved). -/
theorem request {β : Nat} {s : L.core'.Rec} {B : Board n} (input : Arrival) {e z : Cell n}
    (hs : L.core'.Holds β s B) (entry : L.frame.Entry e z) (atZ : blank B=z)
    (label : L.frame.Label input (B e))
    (guard : RequestGuard L.frame.M L.frame.r s.2.1 input)
    (lead : Lead β (advance s.2.1 input (select L.frame.M L.frame.r s.2.1 input))) :
    Nonempty (Response L.core' β s B input e) := by
  have : NeZero L.m := ⟨by have := L.side; omega⟩
  rcases s with ⟨p,c,w,k⟩
  obtain ⟨h,hi,ns,hw⟩ := hs
  dsimp only at h hi ns hw guard lead
  have hg : 6≤L.frame.g := L.g_eq ▸ L.six
  let st := h.toState
  obtain ⟨q,hq,hsel,_⟩ := st.selected_cell hg input guard ∅ (by simp)
  have he := L.frame.entry_input entry
  obtain ⟨e',z',hent,rfl,rfl⟩ := entry
  obtain ⟨q',rfl⟩ := L.cell_preimage hq
  have hq' : q'∈L.core∪L.reserve∪L.spare := by
    rw [cells_eq] at hq; exact (mem_map' _).mp hq
  obtain ⟨C,path,u',hu',hqu,blankC,cyc,cost⟩ := L.rX e' z' hent B atZ q' hq'
  have hu : L.ι u'∈L.frame.cells := by rw [cells_eq]; exact mem_map_of_mem _ (mem_union_right _ hu')
  have hqu' : L.ι q'≠L.ι u' := fun e => hqu (L.ι.injective e).symm
  obtain ⟨load,store,storeU,fixed⟩ := cyc
  change C (L.ι e')=B (L.ι q') at load
  change C (L.ι q')=B (L.ι u') at store
  change C (L.ι u')=B (L.ι e') at storeU
  change ∀ y, y≠L.ι e' → y≠L.ι q' → y≠L.ι u' → C y=B y at fixed
  have physical := cycle_parent_contents L.frame.cells B C (L.ι e') (L.ι q') (L.ι u')
    he hq hu hqu' store storeU fixed
  have next := h.exchange (C:=C) input guard hsel (outside_fresh st.inventory he) label physical
  have st2 := hi.step h.valid input guard lead
  -- the roles after the exchange: no new source, the exported one gone
  set p' := updateRoles p (C (L.ι e')) (B (L.ι e')) input.role with hp'
  have notSrc : input.role≠.coreSource := by cases input <;> decide
  have mem' (t : Tile n) : t∈p' .coreSource ↔ t≠B (L.ι q') ∧ t∈p .coreSource := by
    rw [hp',mem_updateRoles,load]
    constructor
    · rintro (⟨h1,_⟩ | h2)
      · exact absurd h1.symm notSrc
      · exact h2
    · exact Or.inr
  have fresh := outside_fresh st.inventory he
  have uNo : B (L.ι u')∉p .coreSource := ns u' (mem_union_right _ hu')
  have eNo : B (L.ι e')∉p .coreSource := fresh _
  have eCells : ∀ y : Cell L.m, y∈L.core∪L.reserve∪L.spare → L.ι y≠L.ι e' := by
    intro y hy e; apply he; rw [←e,cells_eq]; exact mem_map_of_mem _ hy
  have ns' : L.NoSrc C p' := by
    intro y hy
    rw [mem']; rintro ⟨_,hm⟩
    by_cases yq : y=q'
    · subst yq; rw [store] at hm; exact uNo hm
    by_cases yu : y=u'
    · subst yu; rw [storeU] at hm; exact eNo hm
    rw [fixed _ (eCells y (by rw [union_assoc]; exact mem_union_right _ hy))
      (fun e => yq (L.ι.injective e)) (fun e => yu (L.ι.injective e))] at hm
    exact ns y hy hm
  have drop := L.phi_drop (B:=B) (C:=C) (p:=p) (p':=p') q'
    (by
      intro y hy yq
      have yu : y≠u' := fun e => disjoint_left.mp L.core_spare hy (e ▸ hu')
      rw [fixed _ (eCells y (mem_union_left _ (mem_union_left _ hy))) (fun e => yq (L.ι.injective e))
        (fun e => yu (L.ι.injective e)),mem']
      exact ⟨fun h => h.2,fun h => ⟨fun e => yq (L.ι.injective (B.injective e)),h⟩⟩)
    (by rw [mem',store]; exact fun h => uNo h.2)
  have oth := other_step L.frame.M L.frame.r c input k
  refine ⟨⟨C,path,⟨p',advance c input (select L.frame.M L.frame.r c input),w+path.length,
    k+hstep L.frame.M L.frame.r c input⟩,⟨?_,st2.1,ns',?_⟩,blankC.trans atZ.symm,?_,?_,rfl,rfl,le_rfl⟩⟩
  · show Sound L.frame C p' _; rw [hp',load]; exact next
  · show w+path.length+L.phi C p'≤∑ x∈L.core, L.rw x+L.rcost*((advance c input
      (select L.frame.M L.frame.r c input)).er+(k+hstep L.frame.M L.frame.r c input))
    rw [oth]
    by_cases sc : select L.frame.M L.frame.r c input=.core
    · rw [if_pos sc,Nat.add_zero]
      have src : B (L.ι q')∈p .coreSource := by rw [sc] at hsel; exact hsel
      have qc : q'∈L.core := by
        rcases mem_union.mp hq' with h1 | h1
        · rcases mem_union.mp h1 with h2 | h2
          · exact h2
          · exact absurd src (ns q' (mem_union_left _ h2))
        · exact absurd src (ns q' (mem_union_right _ h1))
      rw [if_pos ⟨qc,src⟩] at drop
      omega
    · rw [if_neg sc,Nat.mul_add,Nat.mul_one]
      have := L.rw_le q'
      omega
  · intro x hx hxe
    apply fixed x hxe
    all_goals rintro rfl
    exacts [hx hq,hx hu]
  · show C (L.ι e')∈p (select L.frame.M L.frame.r c input).role
    rw [load]; exact hsel

/-- Finishing sorts the region's cells. -/
theorem finish {β : Nat} {s : L.core'.Rec} {B : Board n} {e z : Cell n}
    (hs : L.core'.Holds β s B) (entry : L.frame.Entry e z) (atZ : blank B=z)
    (core : s.2.1.ac=L.frame.M) (reserve : s.2.1.ar=L.frame.r) :
    Nonempty (Finish L.core' β s B) := by
  rcases s with ⟨p,c,w,k⟩
  obtain ⟨h,hi,_,hw⟩ := hs
  dsimp only at h hi hw core reserve
  obtain ⟨e',z',hent,rfl,rfl⟩ := entry
  have coreDone := h.coreFinal_complete core
  have reserveDone := h.reserveFinal_complete reserve
  have present (x : Cell L.m) (hx : x∈L.core∪L.reserve) :
      ∃ y∈L.core∪L.reserve∪L.spare, B (L.ι y)=L.goal (L.ι x) := by
    have goalMem : L.goal (L.ι x)∈contents p := by
      rw [Sound.contents_eq]
      rcases mem_union.mp hx with hc | hr
      · have : L.goal (L.ι x)∈p .coreFinal := by
          rw [coreDone]; exact mem_image_of_mem _ (mem_map_of_mem _ hc)
        simp [this]
      · have : L.goal (L.ι x)∈p .reserveFinal := by
          rw [reserveDone]; exact mem_image_of_mem _ (mem_map_of_mem _ hr)
        simp [this]
    rw [←h.inventory.exact] at goalMem
    obtain ⟨y,hy,hgy⟩ := mem_image.mp goalMem
    rw [cells_eq] at hy
    obtain ⟨y',hy',rfl⟩ := mem_map.mp hy
    exact ⟨y',hy',hgy⟩
  obtain ⟨C,path,cost,blankC,outside,placed⟩ := L.fX e' z' hent B atZ present
  refine ⟨⟨C,path,blankC,?_,?_,?_⟩⟩
  · intro x hx _
    apply outside x
    change x∉(L.core∪L.reserve∪L.spare).map L.ι
    rw [←cells_eq]; exact hx
  · intro x hx
    change x∈L.core.map L.ι∪L.reserve.map L.ι at hx
    rw [←map_union] at hx
    obtain ⟨x',hx',rfl⟩ := mem_map.mp hx
    exact placed x' hx'
  · have hr := L.r_eq
    have fin := hi.final_other h.valid core reserve
    rw [hr] at fin
    have hw' := Nat.mul_le_mul_left L.rcost fin
    have e : L.rcost*(L.reserve.card+β)=L.rcost*L.reserve.card+L.rcost*β := Nat.mul_add _ _ _
    show w+path.length≤L.budgetBase+L.rcost*β
    unfold budgetBase
    omega

def region : Region n :=
  { L.core' with
    sound := fun hs => hs.1
    relax := fun hs hb => ⟨hs.1,hs.2.1.relax hb,hs.2.2.1,hs.2.2.2⟩
    transport := by
      intro _ s B C hs _ same
      have cell (y : Cell L.m) (hy : y∈L.core∪L.reserve∪L.spare) : C (L.ι y)=B (L.ι y) :=
        same _ (by show L.ι y∈L.frame.cells; rw [cells_eq]; exact mem_map_of_mem _ hy)
      refine ⟨hs.1.transport same,hs.2.1,fun y hy => ?_,?_⟩
      · rw [cell y (by rw [union_assoc]; exact mem_union_right _ hy)]; exact hs.2.2.1 y hy
      · have : L.phi C s.1=L.phi B s.1 := by
          unfold phi; apply sum_congr rfl; intro y hy
          rw [cell y (mem_union_left _ (mem_union_left _ hy))]
        rw [this]; exact hs.2.2.2
    prepared_local := by
      intro B C hB same x hx
      rw [same x hx]
      exact hB x hx
    init := by
      intro B hB
      refine ⟨⟨L.frame.cellRoles B,⟨0,0,0,0⟩,0,0⟩,⟨Sound.initial L.frame B hB,HInv.zero,?_,?_⟩,
        rfl,rfl,rfl⟩
      · intro y hy hm
        change B (L.ι y)∈L.frame.coreCells.image B at hm
        obtain ⟨x,hx,e⟩ := mem_image.mp hm
        rw [B.injective e] at hx
        have hx' : y∈L.core := (mem_map' L.ι).mp hx
        rcases mem_union.mp hy with h | h
        · exact disjoint_left.mp L.core_reserve hx' h
        · exact disjoint_left.mp L.core_spare hx' h
      · have := L.phi_le B (L.frame.cellRoles B)
        simp only [Nat.zero_add,Nat.add_zero,Nat.mul_zero]; exact this
    substitute := by
      intro _ s B C π hs _ sub phys
      have cell (y : Cell L.m) (hy : y∈L.core∪L.reserve∪L.spare) : C (L.ι y)=π (B (L.ι y)) :=
        phys _ (by show L.ι y∈L.frame.cells; rw [cells_eq]; exact mem_map_of_mem _ hy)
      have src (t : Tile n) : π t∈substRoles s.1 π .coreSource ↔ t∈s.1 .coreSource := by
        change π t∈(if Role.coreSource=Role.helper then _ else s.1 .coreSource) ↔ _
        rw [if_neg (by decide)]
        constructor
        · intro hm
          have fx := sub.fixes .coreSource (by decide) _ hm
          have : π t=t := π.injective fx
          rw [this] at hm; exact hm
        · intro hm; rw [sub.fixes .coreSource (by decide) t hm]; exact hm
      refine ⟨⟨substRoles s.1 π,s.2.1,s.2.2⟩,⟨hs.1.substitute sub phys,hs.2.1,fun y hy => ?_,?_⟩,rfl,rfl,rfl⟩
      · rw [cell y (by rw [union_assoc]; exact mem_union_right _ hy),src]; exact hs.2.2.1 y hy
      · have : L.phi C (substRoles s.1 π)=L.phi B s.1 := by
          unfold phi; apply sum_congr rfl; intro y hy
          rw [cell y (mem_union_left _ (mem_union_left _ hy))]
          simp only [src]
        rw [this]; exact hs.2.2.2
    request := by
      intro _ _ _ input _ _ hs entry atZ label guard lead
      exact L.request input hs entry atZ label guard lead
    finish := by
      intro _ _ _ _ _ hs entry atZ core reserve
      exact L.finish hs entry atZ core reserve }

end LeafSpec
end SlidingPuzzle.NestedRouting.Interface
