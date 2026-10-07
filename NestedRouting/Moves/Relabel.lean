import NestedRouting.Board.Paths

/-! Relabeling tile names by a permutation which fixes the blank. -/
namespace SlidingPuzzle

variable {n : ℕ} [NeZero n]

/-- Rename every tile on a board. -/
def relabel (B : Board n) (e : Equiv.Perm (Tile n)) : Board n := B.trans e

omit [NeZero n] in
@[simp] theorem relabel_apply (B : Board n) (e : Equiv.Perm (Tile n)) (c : Cell n) :
    relabel B e c = e (B c) := rfl

omit [NeZero n] in
theorem relabel_swapCells (B : Board n) (e : Equiv.Perm (Tile n)) (a b : Cell n) :
    relabel (swapCells B a b) e = swapCells (relabel B e) a b := by
  ext c
  rfl

theorem blank_relabel (B : Board n) (e : Equiv.Perm (Tile n)) (he : e 0 = 0) :
    blank (relabel B e) = blank B := by
  have hesymm : e.symm 0 = 0 := by
    apply e.injective
    simp [he]
  simp [blank, position, relabel, hesymm]

theorem Step.relabel {B C : Board n} (e : Equiv.Perm (Tile n)) (he : e 0 = 0)
    (h : Step B C) : Step (relabel B e) (relabel C e) := by
  obtain ⟨c, hc, hC⟩ := h
  refine ⟨c, ?_, ?_⟩
  · simpa [blank_relabel B e he] using hc
  · rw [hC, relabel_swapCells]
    simp [blank_relabel B e he]

def Path.relabel {B C : Board n} : (p : Path B C) → (e : Equiv.Perm (Tile n)) → (he : e 0 = 0) →
    Path (_root_.SlidingPuzzle.relabel B e) (_root_.SlidingPuzzle.relabel C e)
  | .nil B, e, _ => .nil (_root_.SlidingPuzzle.relabel B e)
  | .cons h p, e, he => .cons (h.relabel e he) (p.relabel e he)

@[simp] theorem Path.length_relabel {B C : Board n} (p : Path B C)
    (e : Equiv.Perm (Tile n)) (he : e 0 = 0) : (p.relabel e he).length = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [Path.relabel, ih]

omit [NeZero n] in
theorem relabel_relabel_symm (B : Board n) (e : Equiv.Perm (Tile n)) :
    relabel (relabel B e) e.symm = B := by
  ext c
  simp [relabel]

end SlidingPuzzle
