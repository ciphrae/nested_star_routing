import Std

/-! The counters of the source-first policy: core and reserve exports
`ec er` and arrivals `ac ar` of a region with `M` core and `r` reserve
homes, and the invariant every request preserves (`valid_advance` in
`RequestPolicy`). -/
namespace SlidingPuzzle.NestedRouting.ReservePolicy

structure Counts where
  ec : Nat
  er : Nat
  ac : Nat
  ar : Nat
  deriving DecidableEq, Repr

def Counts.Valid (M r : Nat) (c : Counts) : Prop :=
  c.ec ≤ M ∧ c.er ≤ r ∧ c.ac ≤ M ∧ c.ar ≤ r ∧
  c.ar ≤ c.er ∧ c.ac+c.ar ≤ c.ec+c.er

theorem Counts.Valid.zero {M r : Nat} : (⟨0,0,0,0⟩ : Counts).Valid M r := by
  simp [Counts.Valid]

theorem core_lead {M r B : Nat} {c : Counts} (h : c.Valid M r)
    (lead : c.ec+c.er ≤ c.ac+c.ar+B) : c.ec ≤ c.ac+B := by
  simp only [Counts.Valid] at h
  omega

/-- At core exhaustion there are at most B not-yet-accepted core goals.
This is the count that pays for the late received-final rescue operations. -/
theorem late_core_bound {M r B : Nat} {c : Counts} (h : c.Valid M r)
    (lead : c.ec+c.er ≤ c.ac+c.ar+B) (done : c.ec=M) :
    M-c.ac ≤ B := by
  have hc := core_lead h lead
  omega

/-- A paused parent's exact helper population cannot fall below its initial
population. Four protected helpers therefore leave at least two others
when the initial population is at least six. -/
theorem helpers_available {M r : Nat} {c : Counts} (h : c.Valid M r)
    (g helpers : Nat) (hg : 6≤g)
    (mass : helpers+c.ac+c.ar = g+c.ec+c.er) : 6≤helpers := by
  simp only [Counts.Valid] at h
  omega

end SlidingPuzzle.NestedRouting.ReservePolicy
