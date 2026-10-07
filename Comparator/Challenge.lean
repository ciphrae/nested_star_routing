import Mathlib.Data.Nat.Dist
import Mathlib.Logic.Equiv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Comparator challenge: the statement of `pair_bound`, with every project definition it uses
restated here verbatim. It imports only Mathlib. `comparator.json` checks that the definitions in
`NestedRouting` are identical to these, and that `pair_bound` is proved there. -/

namespace SlidingPuzzle

abbrev Cell (n : ℕ) := Fin n × Fin n
abbrev Tile (n : ℕ) := Fin (n * n)
abbrev Board (n : ℕ) := Cell n ≃ Tile n

/-- Grid distance measured in unit horizontal and vertical moves. -/
def gridDistance {n : ℕ} (a b : Cell n) : ℕ :=
  a.1.val.dist b.1.val + a.2.val.dist b.2.val

def position {n : ℕ} (B : Board n) (t : Tile n) : Cell n := B.symm t

def blank {n : ℕ} [NeZero n] (B : Board n) : Cell n := position B 0

/-- Swap two cell contents, leaving every other cell fixed. -/
def swapCells {n : ℕ} (B : Board n) (a b : Cell n) : Board n :=
  (Equiv.swap a b).trans B

/-- A legal blank move to an adjacent cell. -/
def Step {n : ℕ} [NeZero n] (B C : Board n) : Prop :=
  ∃ c : Cell n, gridDistance (blank B) c = 1 ∧ C = swapCells B (blank B) c

variable {n : ℕ} [NeZero n]

/-- A finite legal walk, with endpoints in its type. -/
inductive Path : Board n → Board n → Type
  | nil (B : Board n) : Path B B
  | cons {A B C : Board n} (step : Step A B) (tail : Path B C) : Path A C

namespace Path

def length {A B : Board n} : Path A B → ℕ
  | .nil _ => 0
  | .cons _ p => p.length + 1

end Path

namespace NestedRouting.Central

/-- God's number of the n×n puzzle is at most n³ + 4161 n² ln n − 12148 n² for n ≥ 256. -/
theorem pair_bound : ∀ (n : Nat) [NeZero n], 256 ≤ n → ∀ B T : Board n, Nonempty (Path B T) →
    ∃ path : Path B T, (path.length : ℝ) ≤ n^3 + 4161*n^2*Real.log n - 12148*n^2 := by
  sorry

end NestedRouting.Central

end SlidingPuzzle
