import NestedRouting.Board.Paths

/-! Single moves as paths, and `Executes`: an explicit list of blank
destinations with its legality, length, and preservation of unvisited cells. -/

namespace SlidingPuzzle

variable {n : ℕ} [NeZero n]

/-- A single legal move as a path with exactly one edge. -/
def Step.toPath {B C : Board n} (h : Step B C) : Path B C := .cons h (.nil _)

@[simp] theorem Step.toPath_length {B C : Board n} (h : Step B C) :
    h.toPath.length = 1 := rfl

/-- Move the blank to the specified adjacent cell. -/
def movePath (B : Board n) (c : Cell n) (h : gridDistance (blank B) c = 1) :
    Path B (swapCells B (blank B) c) :=
  Step.toPath ⟨c, h, rfl⟩

@[simp] theorem movePath_length (B : Board n) (c : Cell n)
    (h : gridDistance (blank B) c = 1) : (movePath B c h).length = 1 := rfl

omit [NeZero n] in
theorem swapCells_preserves (B : Board n) {a b c : Cell n}
    (ha : c ≠ a) (hb : c ≠ b) : swapCells B a b c = B c := by
  simp [Equiv.swap_apply_of_ne_of_ne ha hb]

namespace Executes

end Executes

end SlidingPuzzle
