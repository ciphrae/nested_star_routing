import NestedRouting.Interface.RequestPolicy

/-! The direct-exchange budget of a region. A request is charged one
exchange when it exports a reserve source (counted by `er`), and one when it
exports a helper or is a reserve arrival exporting a core (counted by `late`).
Before core exhaustion reserve exports come only with reserve arrivals, so
`er = ar` there; the late charges come only once both kinds of source are
exhausted, and are then paid by the lead. Hence `er + late ≤ r + B`. -/
namespace SlidingPuzzle.NestedRouting.TileRoles
open SlidingPuzzle.NestedRouting.ReservePolicy

/-- The charge not counted by `er`: a helper export, or a reserve arrival
exporting a core. -/
def lateCharge (M r : Nat) (c : Counts) (input : Arrival) : Nat :=
  if select M r c input=.helper ∨ (input=.reserve ∧ select M r c input=.core) then 1 else 0

/-- Direct exchanges charged to one request: a reserve export, a helper
export, and a reserve arrival exporting a core. -/
def exceptionCharge (M r : Nat) (c : Counts) (input : Arrival) : Nat :=
  (if select M r c input=.reserve then 1 else 0)+lateCharge M r c input

/-- Before core exhaustion reserve exports match reserve arrivals; late
charges need both kinds of source exhausted, and are then paid by the lead. -/
def LateInvariant (M r B : Nat) (c : Counts) (L : Nat) : Prop :=
  (c.ec<M → c.er≤c.ar) ∧ (c.ec<M ∨ c.er<r → L=0) ∧
    (c.ec=M → c.er=r → L+(M-c.ac)+(r-c.ar)≤B)

theorem late_invariant_step {M r B : Nat} {c : Counts} {L : Nat}
    (policy : c.Valid M r) (input : Arrival) (guard : RequestGuard M r c input)
    (old : LateInvariant M r B c L)
    (lead : (advance c input (select M r c input)).ec+
      (advance c input (select M r c input)).er≤
      (advance c input (select M r c input)).ac+
      (advance c input (select M r c input)).ar+B) :
    LateInvariant M r B (advance c input (select M r c input)) (L+lateCharge M r c input) := by
  have after := valid_advance policy input guard
  obtain ⟨i1,i2,i3⟩ := old
  simp only [Counts.Valid] at policy after
  unfold LateInvariant lateCharge
  cases input <;> simp only [RequestGuard] at guard <;> simp only [select] at after lead ⊢ <;>
    split_ifs at after lead ⊢ <;> simp_all [advance] <;> omega

theorem LateInvariant.zero {M r B : Nat} : LateInvariant M r B ⟨0,0,0,0⟩ 0 := by
  simp [LateInvariant]; omega

theorem LateInvariant.relax {M r B B' : Nat} {c : Counts} {L : Nat} (h : LateInvariant M r B c L)
    (hB : B≤B') : LateInvariant M r B' c L :=
  ⟨h.1,h.2.1,fun e e' => (h.2.2 e e').trans hB⟩

/-- Reserve exports and late charges number at most `r+B`. -/
theorem exception_bound {M r B : Nat} {c : Counts} {L : Nat} (valid : c.Valid M r)
    (invariant : LateInvariant M r B c L) : c.er+L≤r+B := by
  obtain ⟨_,i2,i3⟩ := invariant
  rcases valid with ⟨h1,h2,_,_,_,_⟩
  by_cases e : c.ec=M ∧ c.er=r
  · have := i3 e.1 e.2; omega
  · have := i2 (by omega); omega

end SlidingPuzzle.NestedRouting.TileRoles
