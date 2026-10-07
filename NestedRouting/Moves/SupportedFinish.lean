import NestedRouting.Moves.MarkedCleanup

/-! Finishing costs linear in the residual support, with two helper slots
absorbing parity. The actual goal board and its support bound remain explicit.
Embedded finishing fixes every cell outside the embedded residual set at the
endpoint, even when that cell lies inside the local square. -/
namespace SlidingPuzzle.MarkedCleanup
open Finset
variable {n : Nat} [NeZero n]

omit [NeZero n] in
theorem relativeSupport_subset_iff (A G : Board n) (R : Finset (Cell n)) :
    relativeSupport A G⊆R ↔ ∀ x, x∉R → A x=G x := by
  classical
  constructor
  · intro support x outside
    by_contra different
    exact outside (support ((mem_relativeSupport A G x).mpr different))
  · intro fixed x member
    by_contra outside
    exact (mem_relativeSupport A G x).mp member (fixed x outside)

omit [NeZero n] in
theorem adjusted_relativeSupport_subset (A G C : Board n) (R : Finset (Cell n))
    (support : relativeSupport A G⊆R) (a b : Cell n) (ha : a∈R) (hb : b∈R)
    (adjusted : ∀ x, x≠a → x≠b → C x=G x) : relativeSupport A C⊆R := by
  apply (relativeSupport_subset_iff A C R).mpr
  intro x outside
  have xa : x≠a := fun equal => outside (equal.symm ▸ ha)
  have xb : x≠b := fun equal => outside (equal.symm ▸ hb)
  exact ((relativeSupport_subset_iff A G R).mp support x outside).trans (adjusted x xa xb).symm

theorem exists_supported_finish_with_two_helpers (A G : Board n) (hn : 6≤n)
    (hblank : blank A=blank G) (R : Finset (Cell n))
    (support : relativeSupport A G⊆R) (a b : Cell n)
    (haR : a∈R) (hbR : b∈R) (hab : a≠b) (ha : G a≠0) (hb : G b≠0) :
    ∃ C : Board n, ∃ path : Path A C,
      path.length≤54*n*R.card ∧ blank C=blank A ∧
      (C=G ∨ C=swapCells G a b) ∧
      (∀ x, x≠a → x≠b → C x=G x) ∧
      (∀ x, x∉R → C x=A x) := by
  obtain ⟨C,choice,blank,sign,adjusted⟩ := exists_even_goal_adjustment A G a b hab ha hb
  have confined := adjusted_relativeSupport_subset A G C R support a b haR hbR adjusted
  obtain ⟨path,length⟩ := exists_relative_cleanup A C hn sign (hblank.trans blank.symm)
  refine ⟨C,path,length.trans (Nat.mul_le_mul_left (54*n) (card_le_card confined)),
    blank.trans hblank.symm,choice,adjusted,?_⟩
  intro x outside
  exact ((relativeSupport_subset_iff A C R).mp confined x outside).symm

end SlidingPuzzle.MarkedCleanup
