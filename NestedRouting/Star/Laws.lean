import NestedRouting.Star.RequestCases

/-! The structural laws of a star node: raising the allowance, paused
transport, ancestor substitution (passed down to the children) and the
prepared start. -/
namespace SlidingPuzzle.NestedRouting.Interface
open Finset TileRoles
open SlidingPuzzle.NestedRouting.ReservePolicy

variable {n : Nat} [NeZero n] {J : Nat}

namespace StarSpec
variable {P : StarSpec n J}

theorem Holds.relax {β β' : Nat} {s : P.StarRec} {B : Board n} (h : P.Holds β s B) (hβ : β≤β') :
    P.Holds β' s B := by
  refine ⟨h.sound,{ h.inner with ledger := h.inner.ledger.relax hβ },?_,h.lateInv.relax hβ,
    h.ndx_le,h.statInv,h.nreq_le,h.work_le,h.idle0⟩
  have := h.lead; unfold Lead at this ⊢; omega

theorem Holds.transport {β : Nat} {s : P.StarRec} {B C : Board n} (h : P.Holds β s B) (path : Path B C)
    (same : ∀ x∈P.frame.cells, C x=B x) : P.Holds β s C := by
  have laneSame {j : Fin J} {c : Cell n} (hc : c∈P.L.loop j) : C c=B c :=
    same c (P.own_sub_cells (P.loop_own j c hc))
  obtain ⟨st1,st2,st3,st4⟩ := h.statInv
  have stC : P.StatInv s C := ⟨st1,fun x hx => by
    rw [same x (P.own_sub_cells (P.stat_own x (st1 hx)))]; exact st2 x hx,st3,st4⟩
  refine ⟨h.sound.transport same,?_,h.lead,h.lateInv,h.ndx_le,stC,h.nreq_le,h.work_le,h.idle0⟩
  apply h.inner.congr (Equiv.refl _) (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl h.inner.disjoint
  · intro j; simp only [ce,Equiv.coe_refl,List.map_id]
    exact List.map_congr_left (fun c hc => laneSame (P.L.mem_loop_of_exportQ hc))
  · intro j; simp only [cd,Equiv.coe_refl,List.map_id]
    exact List.map_congr_left (fun c hc => laneSame (P.L.mem_loop_of_deliveryQ hc))
  · simpa using same _ (P.own_sub_cells P.K_own)
  · intro j
    exact (P.Q j).transport (h.inner.child j) path (fun x hx => same x (P.child_sub_cells j hx))
  · exact fun _ => rfl
  · exact fun _ => rfl
  · exact fun _ => rfl

theorem Holds.substitute {β : Nat} {s : P.StarRec} {B C : Board n} (h : P.Holds β s B)
    (path : Path B C) {π : Equiv.Perm (Tile n)} (sub : Substitution s.roles π)
    (phys : ∀ x∈P.frame.cells, C x=π (B x)) :
    ∃ s' : P.StarRec, P.Holds β s' C ∧ s'.roles=substRoles s.roles π ∧ s'.counts=s.counts ∧
      s'.work=s.work := by
  classical
  have fixS : ∀ t∈s.roles .coreSource, π t=t := sub.fixes _ (by decide)
  have fixF : ∀ t∈s.roles .coreFinal, π t=t := sub.fixes _ (by decide)
  have childSub (j : Fin J) : ∃ s', (P.Q j).Holds (P.childBeta s.led j) s' C ∧
      (P.Q j).roles s'=substRoles ((P.Q j).roles (s.ch j)) π ∧
      (P.Q j).counts s'=(P.Q j).counts (s.ch j) ∧ (P.Q j).work s'=(P.Q j).work (s.ch j) := by
    apply (P.Q j).substitute π (h.inner.child j) path
    · refine ⟨?_,sub.zero⟩
      intro i hi t ht
      cases i with
      | helper => exact absurd rfl hi
      | coreSource => exact fixS t (h.inner.src_child j (by simp [childSrc,ht]))
      | reserveSource => exact fixS t (h.inner.src_child j (by simp [childSrc,ht]))
      | coreFinal => exact fixF t (h.inner.fin_child j (by simp [childFin,ht]))
      | reserveFinal => exact fixF t (h.inner.fin_child j (by simp [childFin,ht]))
    · exact fun x hx => phys x (P.child_sub_cells j hx)
  let ch' : (j : Fin J) → (P.Q j).Rec := fun j => Classical.choose (childSub j)
  have spec (j : Fin J) := Classical.choose_spec (childSub j)
  have sound' := h.sound.substitute sub phys
  have lane {c : Cell n} (hc : ∃ j, c∈P.L.loop j) : C c=π (B c) := by
    obtain ⟨j,hc⟩ := hc
    exact phys c (P.own_sub_cells (P.loop_own j c hc))
  refine ⟨{ s with roles := substRoles s.roles π, ch := ch' },?_,rfl,rfl,rfl⟩
  obtain ⟨st1,st2,st3,st4⟩ := h.statInv
  refine ⟨sound',?_,h.lead,h.lateInv,h.ndx_le,⟨st1,?_,st3,st4⟩,h.nreq_le,?_,h.idle0⟩
  · apply h.inner.congr π fixS fixF (by simp [substRoles]) (by simp [substRoles])
      sound'.inventory.disjoint
    · intro j; simp only [ce,List.map_map]
      exact List.map_congr_left (fun c hc => lane ⟨j,P.L.mem_loop_of_exportQ hc⟩)
    · intro j; simp only [cd,List.map_map]
      exact List.map_congr_left (fun c hc => lane ⟨j,P.L.mem_loop_of_deliveryQ hc⟩)
    · exact phys _ (P.own_sub_cells P.K_own)
    · exact fun j => (spec j).1
    · exact fun j => (spec j).2.2.1
    · intro j
      show P.childSrc j (Classical.choose (childSub j))=_
      simp [childSrc,(spec j).2.1,substRoles]
    · intro j
      show P.childFin j (Classical.choose (childSub j))=_
      simp [childFin,(spec j).2.1,substRoles]
  · intro x hx
    have hRS := st2 x hx
    change C x∈substRoles s.roles π .reserveSource
    simp only [substRoles,reduceCtorEq,if_false]
    rw [phys x (P.own_sub_cells (P.stat_own x (st1 hx))),sub.fixes _ (by decide) _ hRS]
    exact hRS
  · have : P.totalWork ch'=P.totalWork s.ch := by
      unfold totalWork; exact sum_congr rfl (fun j _ => (spec j).2.2.2)
    simp only
    rw [this]; exact h.work_le

def Prepared (P : StarSpec n J) (B : Board n) : Prop :=
  (∀ x∈P.frame.cells, B x≠0) ∧ ∀ j, (P.Q j).Prepared B

theorem prepared_local {B C : Board n} (h : P.Prepared B) (same : ∀ x∈P.frame.cells, C x=B x) :
    P.Prepared C := by
  refine ⟨fun x hx => by rw [same x hx]; exact h.1 x hx,fun j => ?_⟩
  exact (P.Q j).prepared_local (h.2 j) (fun x hx => same x (P.child_sub_cells j hx))

theorem init {B : Board n} (h : P.Prepared B) :
    ∃ s : P.StarRec, P.Holds 0 s B ∧ s.roles=P.frame.cellRoles B ∧ s.counts=⟨0,0,0,0⟩ ∧ s.work=0 := by
  classical
  have childInit (j : Fin J) := (P.Q j).init (h.2 j)
  let ch0 : (j : Fin J) → (P.Q j).Rec := fun j => Classical.choose (childInit j)
  have spec (j : Fin J) := Classical.choose_spec (childInit j)
  have sound0 := Sound.initial P.frame B h.1
  have homeSrc : P.frame.cellRoles B .coreSource=P.homeCells.image B := rfl
  have finEmpty : P.frame.cellRoles B .coreFinal=∅ := rfl
  have childSrc0 (j : Fin J) : P.childSrc j (ch0 j)=((P.Q j).coreCells∪(P.Q j).reserveCells).image B := by
    show P.childSrc j (Classical.choose (childInit j))=_
    rw [childSrc,(spec j).2.1,image_union]; rfl
  have childFin0 (j : Fin J) : P.childFin j (ch0 j)=∅ := by
    show P.childFin j (Classical.choose (childInit j))=_
    rw [childFin,(spec j).2.1]; rfl
  have counts0 (j : Fin J) : (P.Q j).counts (ch0 j)=⟨0,0,0,0⟩ := (spec j).2.2.1
  -- lane tiles are not core sources
  have laneNot {j : Fin J} {c : Cell n} (hc : c∈P.L.loop j) : B c∉P.frame.cellRoles B .coreSource := by
    rw [homeSrc]
    intro hm
    obtain ⟨x,hx,eq⟩ := mem_image.mp hm
    have := B.injective eq
    subst this
    exact disjoint_left.mp P.disjoint_own_childCells (P.loop_own j x hc) (P.homeCells_sub hx)
  have noSrc (j : Fin J) : (P.ce B j).countP (fun t => t∈P.frame.cellRoles B .coreSource)=0 := by
    rw [List.countP_eq_zero]
    intro t ht
    obtain ⟨c,hc,rfl⟩ := Inner.cell_of_ce ht
    simpa using laneNot (P.L.mem_loop_of_exportQ hc)
  have stat0 : ∀ x∈P.stat, B x∈P.frame.cellRoles B .reserveSource := by
    intro x hx
    exact mem_image_of_mem B (mem_union_left _ (P.stat_own x hx))
  refine ⟨⟨P.frame.cellRoles B,⟨0,0,0,0⟩,0,fun _ => Ledger.Counter.zero,ch0,0,0,0,P.stat,0⟩,
    ⟨sound0,?_,by simp [Lead],LateInvariant.zero,le_refl _,⟨subset_rfl,stat0,by simp,fun _ => rfl⟩,
      le_refl _,by simp,fun _ => rfl⟩,rfl,rfl,rfl⟩
  refine ⟨sound0.inventory.disjoint,?_,Ledger.good_zero _ _ _,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals dsimp only
  · intro j
    exact (P.Q j).relax (spec j).1 (Nat.zero_le _)
  · intro j; rw [counts0,noSrc]; rfl
  · intro j; rw [counts0]; simp [finEmpty,Ledger.Counter.zero]
  · intro j t ht
    rw [childSrc0] at ht; rw [homeSrc]
    obtain ⟨x,hx,rfl⟩ := mem_image.mp ht
    exact mem_image_of_mem B (by simp only [homeCells,mem_biUnion,mem_univ,true_and]; exact ⟨j,hx⟩)
  · intro j; rw [childFin0]; exact empty_subset _
  · intro t ht
    rw [homeSrc] at ht
    obtain ⟨x,hx,rfl⟩ := mem_image.mp ht
    simp only [homeCells,mem_biUnion,mem_univ,true_and] at hx
    obtain ⟨j,hj⟩ := hx
    exact Or.inl ⟨j,by rw [childSrc0]; exact mem_image_of_mem B hj⟩
  · intro t ht; rw [finEmpty] at ht; simp at ht
  · intro j t _ htf; rw [finEmpty] at htf; simp at htf
  · intro j t ht
    obtain ⟨c,hc,rfl⟩ := Inner.cell_of_cd ht
    exact laneNot (P.L.mem_loop_of_deliveryQ hc)
  · intro j t _; rw [finEmpty]; simp
  · intro j i hi hlen; simp [Ledger.Counter.zero] at hlen; omega
  · simp [Ledger.Counter.zero]
  · simp [Ledger.Counter.zero]

end StarSpec
end SlidingPuzzle.NestedRouting.Interface
