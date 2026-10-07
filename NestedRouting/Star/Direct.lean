import NestedRouting.Star.Wrap

/-! A direct exchange of the tile at `eP` with the tile at any cell `q` of
P, by the node's exchange `(eP q p₁)`: `q`'s tile leaves, the parking cell
`p₁ ≠ q` gives its token to `q` and takes the input. When `q` lies in a child, the child is updated by its own
substitution law. -/
namespace SlidingPuzzle.NestedRouting.Interface
open Finset TileRoles
open SlidingPuzzle.NestedRouting.ReservePolicy

variable {n : Nat} [NeZero n] {J : Nat}

namespace StarSpec
variable (P : StarSpec n J)

theorem park_not_foot {c : Cell n} (hc : P.park c) : ¬P.foot c :=
  P.not_foot (P.park_loop c hc) (P.park_child c hc) (P.park_K c hc)

theorem park_cells {c : Cell n} (hc : P.park c) : c∈P.frame.cells :=
  P.own_sub_cells (P.park_own c hc)

theorem exists_direct {B : Board n} (atZ : blank B=P.zP) {q : Cell n} (hq : q∈P.frame.cells) :
    ∃ C : Board n, ∃ path : Path B C, ∃ p1 : Cell n,
      P.park p1 ∧ p1≠q ∧ blank C=P.zP ∧
      C P.eP=B q ∧ C q=B p1 ∧ C p1=B P.eP ∧
      (∀ y, y≠P.eP → y≠q → y≠p1 → C y=B y) ∧ path.length≤P.dcost := by
  rw [frame_cells] at hq
  simp only [childCells,mem_union,mem_biUnion,mem_univ,true_and] at hq
  exact P.dX B q atZ (by tauto)

namespace Inner
variable {P} {B : Board n} {r : Roles n} {led : Fin J → Ledger.Counter}
  {ch : (j : Fin J) → (P.Q j).Rec} {cap ecNow acNow : Nat}

/-- A direct exchange keeps the inner invariant: the token at `q` leaves,
the parking cell's token takes its place, the input is parked. A child
holding `q` is updated by substitution. -/
theorem direct (h : P.Inner B r led ch cap ecNow acNow false false) {C : Board n} (path : Path B C)
    {q p1 : Cell n} (hq : q∈P.frame.cells) (h1 : P.park p1) (n1 : p1≠q)
    (atZ : blank B=P.zP)
    (se : C P.eP=B q) (sq : C q=B p1) (_s1 : C p1=B P.eP)
    (fix : ∀ y, y≠P.eP → y≠q → y≠p1 → C y=B y)
    (qtok : B q∉r .coreSource ∧ B q∉r .coreFinal) :
    ∃ ch' : (j : Fin J) → (P.Q j).Rec, P.Inner C r led ch' cap ecNow acNow false false ∧
      ∀ j, (P.Q j).work (ch' j)=(P.Q j).work (ch j) := by
  classical
  -- the parking cell holds a token: core tiles sit in children and export queues
  have pNotChild (j : Fin J) : p1∉(P.Q j).cells :=
    fun hj => P.park_not_foot h1 (Or.inl ⟨j,Or.inr (Or.inr hj)⟩)
  have ptok : B p1∉r .coreSource ∧ B p1∉r .coreFinal := by
    constructor
    · intro hm
      rcases h.src_loc _ hm with ⟨j,hj⟩ | ⟨j,hj⟩ | ⟨hc,_⟩
      · obtain ⟨x,hx,hxB⟩ := h.mem_childSrc_cell hj
        exact pNotChild j (B.injective hxB ▸ hx)
      · obtain ⟨c,hc,hcB⟩ := Inner.cell_of_ce hj
        exact P.park_not_foot h1 (B.injective hcB ▸ Or.inl ⟨j,Or.inl hc⟩)
      · cases hc
    · intro hm
      rcases h.fin_loc _ hm with ⟨j,hj⟩ | ⟨j,hj⟩ | ⟨hc,_⟩
      · obtain ⟨x,hx,hxB⟩ := h.mem_childFin_cell hj
        exact pNotChild j (B.injective hxB ▸ hx)
      · obtain ⟨c,hc,hcB⟩ := Inner.cell_of_cd hj
        exact P.park_not_foot h1 (B.injective hcB ▸ Or.inl ⟨j,Or.inr (Or.inl hc)⟩)
      · cases hc
  set π := Equiv.swap (B q) (B p1) with hπ
  have eq' : P.eP≠q := fun e => P.eP_cells (e ▸ hq)
  have nzq : B q≠0 := StarLayout.ne_zero_of_ne_blank (by rw [atZ]; rintro rfl; exact P.zP_cells hq)
  have nzp : B p1≠0 := StarLayout.ne_zero_of_ne_blank
    (by rw [atZ]; rintro rfl; exact P.zP_cells (P.park_cells h1))
  have πzero : π 0=0 := Equiv.swap_apply_of_ne_of_ne nzq.symm nzp.symm
  -- cells other than `eP` and the parking cell: `C = π ∘ B`
  have onCell (x : Cell n) (hx1 : x≠p1) (hxe : x≠P.eP) : C x=π (B x) := by
    by_cases hxq : x=q
    · subst hxq; rw [sq,hπ,Equiv.swap_apply_left]
    · rw [fix x hxe hxq hx1,hπ,Equiv.swap_apply_of_ne_of_ne (fun e => hxq (B.injective e))
        (fun e => hx1 (B.injective e))]
  have footCell {x : Cell n} (hx : P.foot x) : C x=π (B x) :=
    onCell x (fun e => P.park_not_foot h1 (e ▸ hx)) (P.foot_ne_eP hx)
  -- children
  have childSub (j : Fin J) (hqj : q∈(P.Q j).cells) :
      ∃ s', (P.Q j).Holds (P.childBeta led j) s' C ∧ (P.Q j).roles s'=substRoles ((P.Q j).roles (ch j)) π ∧
        (P.Q j).counts s'=(P.Q j).counts (ch j) ∧ (P.Q j).work s'=(P.Q j).work (ch j) := by
    have hs := (P.Q j).sound (h.child j)
    apply (P.Q j).substitute π (h.child j) path
    · refine ⟨?_,πzero⟩
      intro i hi t ht
      -- `t` lies in the child and is not its helper `B q`
      have tCell : t∈(P.Q j).cells.image B := by
        rw [hs.inventory.exact]; exact mem_biUnion.mpr ⟨i,mem_univ _,ht⟩
      obtain ⟨x,hx,rfl⟩ := mem_image.mp tCell
      have hxq : x≠q := by
        rintro rfl
        have hsrc : B x∉P.childSrc j (ch j) := fun hh => qtok.1 ((h.src_iff_child j hx).mpr hh)
        have hfin : B x∉P.childFin j (ch j) := fun hh => qtok.2 ((h.fin_iff_child j hx).mpr hh)
        cases i <;> simp_all [childSrc,childFin]
      have hxp : x≠p1 := fun e => pNotChild j (e ▸ hx)
      exact Equiv.swap_apply_of_ne_of_ne (fun e => hxq (B.injective e)) (fun e => hxp (B.injective e))
    · intro x hx
      exact onCell x (fun e => P.park_not_foot h1 (e ▸ Or.inl ⟨j,Or.inr (Or.inr hx)⟩))
        (fun e => P.eP_child j (e ▸ hx))
  let ch' : (j : Fin J) → (P.Q j).Rec := fun j =>
    if hqj : q∈(P.Q j).cells then Classical.choose (childSub j hqj) else ch j
  have ch'spec (j : Fin J) : (P.Q j).Holds (P.childBeta led j) (ch' j) C ∧
      P.childSrc j (ch' j)=P.childSrc j (ch j) ∧ P.childFin j (ch' j)=P.childFin j (ch j) ∧
      (P.Q j).counts (ch' j)=(P.Q j).counts (ch j) ∧ (P.Q j).work (ch' j)=(P.Q j).work (ch j) := by
    by_cases hqj : q∈(P.Q j).cells
    · have spec := Classical.choose_spec (childSub j hqj)
      simp only [ch',dif_pos hqj]
      obtain ⟨hh,hr,hc,hw⟩ := spec
      refine ⟨hh,?_,?_,hc,hw⟩ <;> simp [childSrc,childFin,hr,substRoles]
    · have e : ch' j=ch j := dif_neg hqj
      rw [e]
      refine ⟨?_,rfl,rfl,rfl,rfl⟩
      apply (P.Q j).transport (h.child j) path
      intro x hx
      have hxq : x≠q := fun e => hqj (e ▸ hx)
      exact fix x (fun e => P.eP_child j (e ▸ hx)) hxq (fun e => pNotChild j (e ▸ hx))
  have fixSet {S : Finset (Tile n)} (hS : ∀ t∈S, t≠B q ∧ t≠B p1) : ∀ t∈S, π t=t :=
    fun t ht => Equiv.swap_apply_of_ne_of_ne (hS t ht).1 (hS t ht).2
  refine ⟨ch',h.congr π (fixSet (fun t ht => ⟨fun e => qtok.1 (e ▸ ht),fun e => ptok.1 (e ▸ ht)⟩))
    (fixSet (fun t ht => ⟨fun e => qtok.2 (e ▸ ht),fun e => ptok.2 (e ▸ ht)⟩)) rfl rfl h.disjoint
    ?_ ?_ ?_ (fun j => (ch'spec j).1) (fun j => (ch'spec j).2.2.2.1) (fun j => (ch'spec j).2.1)
    (fun j => (ch'spec j).2.2.1),fun j => (ch'spec j).2.2.2.2⟩
  · intro j
    simp only [ce,List.map_map]
    exact List.map_congr_left (fun x hx => footCell (Or.inl ⟨j,Or.inl hx⟩))
  · intro j
    simp only [cd,List.map_map]
    exact List.map_congr_left (fun x hx => footCell (Or.inl ⟨j,Or.inr (Or.inl hx)⟩))
  · exact footCell (Or.inr rfl)

end Inner

end StarSpec
end SlidingPuzzle.NestedRouting.Interface
