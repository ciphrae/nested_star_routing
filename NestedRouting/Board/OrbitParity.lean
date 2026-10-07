import NestedRouting.Board.Paths

/-! A parity obstruction for the actual legal-move relation.

The results here prove only a necessary condition for reachability.  They do not claim that this
condition is sufficient to construct a path to the target. -/
namespace SlidingPuzzle

variable {n : ℕ} [NeZero n]

/-- The sign of the board permutation relative to the standard target. -/
def boardSign (B : Board n) : ℤˣ :=
  Equiv.Perm.sign (B.trans (target n).symm)

/-- The checkerboard colour of a cell, represented as a sign. -/
def colorSign (c : Cell n) : ℤˣ := (-1 : ℤˣ) ^ (c.1.val + c.2.val)

/-- The product whose two factors both change sign under a legal blank move. -/
def parityInvariant (B : Board n) : ℤˣ := boardSign B * colorSign (blank B)

omit [NeZero n] in
private theorem gridDistance_one_ne {a b : Cell n} (h : gridDistance a b = 1) : a ≠ b := by
  intro hab
  subst b
  simp at h

omit [NeZero n] in
private theorem gridDistance_one_colorSign {a b : Cell n}
    (h : gridDistance a b = 1) : colorSign b = -colorSign a := by
  unfold colorSign
  rw [show (-1 : ℤˣ) ^ (b.1.val + b.2.val) =
      if Even (b.1.val + b.2.val) then 1 else -1 by
        rw [neg_one_pow_eq_ite],
    show (-1 : ℤˣ) ^ (a.1.val + a.2.val) =
      if Even (a.1.val + a.2.val) then 1 else -1 by
        rw [neg_one_pow_eq_ite]]
  have hmod : (a.1.val + a.2.val) % 2 + (b.1.val + b.2.val) % 2 = 1 := by
    simp only [gridDistance, Nat.dist] at h
    omega
  have ha_bound : (a.1.val + a.2.val) % 2 < 2 := Nat.mod_lt _ (by omega)
  have hb_bound : (b.1.val + b.2.val) % 2 < 2 := Nat.mod_lt _ (by omega)
  interval_cases ha : (a.1.val + a.2.val) % 2 <;>
    interval_cases hb : (b.1.val + b.2.val) % 2
  · exfalso
    omega
  · have hea : Even (a.1.val + a.2.val) :=
      even_iff_two_dvd.mpr (Nat.dvd_iff_mod_eq_zero.mpr ha)
    have hnb : ¬ Even (b.1.val + b.2.val) :=
      Nat.not_even_iff_odd.mpr (Nat.odd_iff.mpr hb)
    simp [hea, hnb]
  · have hna : ¬ Even (a.1.val + a.2.val) :=
      Nat.not_even_iff_odd.mpr (Nat.odd_iff.mpr ha)
    have heb : Even (b.1.val + b.2.val) :=
      even_iff_two_dvd.mpr (Nat.dvd_iff_mod_eq_zero.mpr hb)
    simp [hna, heb]
  · exfalso
    omega

omit [NeZero n] in
theorem boardSign_swapCells (B : Board n) {a b : Cell n} (hab : a ≠ b) :
    boardSign (swapCells B a b) = -boardSign B := by
  simp [boardSign, swapCells, Equiv.Perm.sign_swap hab, Equiv.trans_assoc]

theorem Step.parityInvariant {B C : Board n} (h : Step B C) :
    parityInvariant C = parityInvariant B := by
  obtain ⟨c, hc, rfl⟩ := h
  have hne : blank B ≠ c := gridDistance_one_ne hc
  change SlidingPuzzle.parityInvariant (swapCells B (blank B) c) =
    SlidingPuzzle.parityInvariant B
  change boardSign (swapCells B (blank B) c) * colorSign (blank (swapCells B (blank B) c)) =
    boardSign B * colorSign (blank B)
  rw [blank_swapCells, boardSign_swapCells B hne,
    gridDistance_one_colorSign hc]
  simp

@[simp] theorem parityInvariant_target (n : ℕ) [NeZero n] :
    parityInvariant (target n) = colorSign (blank (target n)) := by
  simp [parityInvariant, boardSign]

namespace Path

variable {A B : Board n}

/-- The parity invariant is preserved by every finite legal path. -/
theorem parityInvariant (p : Path A B) : parityInvariant B = parityInvariant A := by
  induction p with
  | nil => rfl
  | cons h p ih => exact ih.trans h.parityInvariant

end Path

/-- Every reachable board satisfies the parity condition of the target.
This is a necessary condition only; no converse reachability statement is asserted here. -/
theorem reachable_parityInvariant (B : Board n) (h : Reachable B) :
    parityInvariant B = colorSign (blank (target n)) := by
  obtain ⟨p⟩ := h
  exact p.parityInvariant.trans (parityInvariant_target n)

end SlidingPuzzle
