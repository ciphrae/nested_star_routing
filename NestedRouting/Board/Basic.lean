import MathlibRoots

/-! Concrete square boards. Coordinates increase downwards and to the right.
A move is specified by the destination of the blank (opposite to the paper's tile direction).
The target lists 1, …, n²-1, 0 in row-major order. -/
namespace SlidingPuzzle

abbrev Cell (n : ℕ) := Fin n × Fin n
abbrev Tile (n : ℕ) := Fin (n * n)
abbrev Board (n : ℕ) := Cell n ≃ Tile n

/-- The standard row-major target, with the zero tile in the final cell. -/
def target (n : ℕ) : Board n := finProdFinEquiv.trans (finRotate (n * n))

/-- Grid distance measured in unit horizontal and vertical moves. -/
def gridDistance {n : ℕ} (a b : Cell n) : ℕ :=
  a.1.val.dist b.1.val + a.2.val.dist b.2.val

@[simp] theorem gridDistance_self {n : ℕ} (a : Cell n) : gridDistance a a = 0 := by
  simp [gridDistance]

theorem gridDistance_comm {n : ℕ} (a b : Cell n) :
    gridDistance a b = gridDistance b a := by
  simp [gridDistance, Nat.dist_comm]

def position {n : ℕ} (B : Board n) (t : Tile n) : Cell n := B.symm t

def blank {n : ℕ} [NeZero n] (B : Board n) : Cell n := position B 0

/-- Swap two cell contents, leaving every other cell fixed. -/
def swapCells {n : ℕ} (B : Board n) (a b : Cell n) : Board n :=
  (Equiv.swap a b).trans B

@[simp] theorem swapCells_apply {n : ℕ} (B : Board n) (a b c : Cell n) :
    swapCells B a b c = B (Equiv.swap a b c) := rfl

@[simp] theorem swapCells_swapCells {n : ℕ} (B : Board n) (a b : Cell n) :
    swapCells (swapCells B a b) a b = B := by
  ext c
  simp

theorem swapCells_comm {n : ℕ} (B : Board n) (a b : Cell n) :
    swapCells B a b = swapCells B b a := by
  simp only [swapCells, Equiv.swap_comm]

@[simp] theorem position_swapCells {n : ℕ} (B : Board n) (a b : Cell n) (t : Tile n) :
    position (swapCells B a b) t = Equiv.swap a b (position B t) := by
  simp [position, swapCells]

@[simp] theorem blank_swapCells {n : ℕ} [NeZero n] (B : Board n) (c : Cell n) :
    blank (swapCells B (blank B) c) = c := by
  simp [blank]

/-- A legal blank move to an adjacent cell. -/
def Step {n : ℕ} [NeZero n] (B C : Board n) : Prop :=
  ∃ c : Cell n, gridDistance (blank B) c = 1 ∧ C = swapCells B (blank B) c

theorem Step.symm {n : ℕ} [NeZero n] {B C : Board n} (h : Step B C) : Step C B := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨blank B, ?_, ?_⟩
  · simpa [gridDistance_comm] using hc
  · simp only [blank_swapCells]
    rw [swapCells_comm (swapCells B (blank B) c) c (blank B)]
    simp

end SlidingPuzzle
