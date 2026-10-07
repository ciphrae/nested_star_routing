import NestedRouting.Interface.RequestPolicy

/-! A one-out, one-in exchange preserves the five-role inventory and
produces the next policy state. -/
namespace SlidingPuzzle.NestedRouting.TileRoles
open Finset
open SlidingPuzzle.NestedRouting.ReservePolicy
variable {n : Nat}

def updateRoles (p : Roles n) (old fresh : Tile n) (dest : Role) : Roles n :=
  fun i => if i=dest then insert fresh ((p i).erase old) else (p i).erase old

theorem mem_updateRoles (p : Roles n) (old fresh : Tile n) (dest i : Role) (t : Tile n) :
    t∈updateRoles p old fresh dest i ↔
      (i=dest ∧ t=fresh) ∨ (t≠old ∧ t∈p i) := by
  by_cases hi : i=dest <;> simp [updateRoles,hi]

theorem Inventory.update {R S : Finset (Cell n)} {B C : Board n} {p : Roles n}
    (h : Inventory R B p) (old fresh : Tile n) (dest : Role)
    (freshness : ∀ i, fresh∉p i)
    (physical : S.image C=insert fresh ((R.image B).erase old)) :
    Inventory S C (updateRoles p old fresh dest) := by
  refine ⟨?_,?_⟩
  · intro i j hij
    apply disjoint_left.mpr
    intro t hi hj
    rw [mem_updateRoles] at hi hj
    rcases hi with ⟨hid,rfl⟩ | ⟨_,hi⟩
    · rcases hj with ⟨hjd,_⟩ | ⟨_,hj⟩
      · exact hij (hid.trans hjd.symm)
      · exact freshness j hj
    · rcases hj with ⟨_,rfl⟩ | ⟨_,hj⟩
      · exact freshness i hi
      · exact disjoint_left.mp (h.disjoint i j hij) hi hj
  · rw [physical,h.exact]
    ext t
    constructor
    · intro ht
      rcases mem_insert.mp ht with rfl | ht
      · exact mem_biUnion.mpr ⟨dest,mem_univ _,(mem_updateRoles _ _ _ _ _ _).mpr (Or.inl ⟨rfl,rfl⟩)⟩
      · obtain ⟨hne,ht⟩ := mem_erase.mp ht
        obtain ⟨i,_,hi⟩ := mem_biUnion.mp ht
        exact mem_biUnion.mpr ⟨i,mem_univ _,(mem_updateRoles _ _ _ _ _ _).mpr (Or.inr ⟨hne,hi⟩)⟩
    · intro ht
      obtain ⟨i,_,hi⟩ := mem_biUnion.mp ht
      rcases (mem_updateRoles _ _ _ _ _ _).mp hi with ⟨_,rfl⟩ | ⟨hne,hi⟩
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_erase.mpr ⟨hne,mem_biUnion.mpr ⟨i,mem_univ _,hi⟩⟩)

theorem updated_card {R : Finset (Cell n)} {B : Board n} {p : Roles n}
    (h : Inventory R B p) (out : Role) (old fresh : Tile n) (dest i : Role)
    (oldmem : old∈p out) (freshness : ∀ j, fresh∉p j) :
    (updateRoles p old fresh dest i).card+(if i=out then 1 else 0)=
      (p i).card+(if i=dest then 1 else 0) := by
  have hnf : fresh∉(p i).erase old := fun ht => freshness i (mem_of_mem_erase ht)
  by_cases hio : i=out
  · subst i
    have positive : 0<(p out).card := card_pos.mpr ⟨old,oldmem⟩
    by_cases hid : out=dest
    · simp only [updateRoles,if_pos hid,ite_true,card_insert_of_notMem hnf,
        card_erase_of_mem oldmem]
      omega
    · simp only [updateRoles,if_neg hid,ite_true,card_erase_of_mem oldmem]
      omega
  · have absent : old∉p i := fun hi => disjoint_left.mp (h.disjoint i out hio) hi oldmem
    by_cases hid : i=dest
    · simp only [updateRoles,if_pos hid,if_neg hio,erase_eq_of_notMem absent,
        card_insert_of_notMem (freshness i)]
    · simp only [updateRoles,if_neg hid,if_neg hio,erase_eq_of_notMem absent]

/-- The next state after an exact physical exchange: the selected occupant
`old` leaves, the input `fresh` arrives. -/
theorem State.after_exchange {R : Finset (Cell n)} {B C : Board n} {M r g : Nat} {p : Roles n}
    {c : Counts} (st : State R B M r g p c) (input : Arrival) (guard : RequestGuard M r c input)
    (old fresh : Tile n) (oldmem : old∈p (select M r c input).role)
    (freshness : ∀ i, fresh∉p i)
    (physical : R.image C=insert fresh ((R.image B).erase old)) :
    State R C M r g (updateRoles p old fresh input.role) (advance c input (select M r c input)) := by
  let out := select M r c input
  have cards (i : Role) := updated_card st.inventory out.role old fresh input.role i oldmem freshness
  refine ⟨st.inventory.update old fresh input.role freshness physical,st.size,?_,?_,?_,?_,
    valid_advance st.valid input guard⟩
  · have h := cards Role.coreSource
    have hc := st.coreSources
    change (updateRoles p old fresh input.role .coreSource).card+(advance c input out).ec=M
    cases input <;> cases ho : out <;> simp only [ho,advance,Arrival.role,Export.role] at h ⊢ <;>
      simp at h ⊢ <;> omega
  · have h := cards Role.reserveSource
    have hc := st.reserveSources
    change (updateRoles p old fresh input.role .reserveSource).card+(advance c input out).er=r
    cases input <;> cases ho : out <;> simp only [ho,advance,Arrival.role,Export.role] at h ⊢ <;>
      simp at h ⊢ <;> omega
  · have h := cards Role.coreFinal
    have hc := st.coreFinals
    change (updateRoles p old fresh input.role .coreFinal).card=(advance c input out).ac
    cases input <;> cases ho : out <;> simp only [ho,advance,Arrival.role,Export.role] at h ⊢ <;>
      simp at h ⊢ <;> omega
  · have h := cards Role.reserveFinal
    have hc := st.reserveFinals
    change (updateRoles p old fresh input.role .reserveFinal).card=(advance c input out).ar
    cases input <;> cases ho : out <;> simp only [ho,advance,Arrival.role,Export.role] at h ⊢ <;>
      simp at h ⊢ <;> omega

end SlidingPuzzle.NestedRouting.TileRoles
