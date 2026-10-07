import NestedRouting.Moves.Relabel
import NestedRouting.Board.Paths

/-! Access, a local blank-returning operation, and reversed access. -/
namespace SlidingPuzzle
variable {n : ℕ} [NeZero n]

/-- Undo arbitrary staging after a blank-returning local operation. The resulting
effect is transported back to the original positions of the staged tiles. -/
theorem Path.exists_unstaged {B C D : Board n} (p : Path B C) (q : Path C D)
    (hblank : blank D = blank C) :
    ∃ E : Board n, ∃ r : Path B E,
      r.length = 2*p.length + q.length ∧ blank E = blank B ∧
      ∀ x, E x = D (C.symm (B x)) := by
  let e : Equiv.Perm (Tile n) := C.symm.trans D
  have he : e 0 = 0 := by
    change D (blank C) = 0
    rw [← hblank]
    simp [blank, position]
  have hC : SlidingPuzzle.relabel C e = D := by
    ext x
    simp [SlidingPuzzle.relabel, e]
  have hret : ∃ s : Path D (SlidingPuzzle.relabel B e), s.length = p.length := by
    have h : ∃ s : Path (SlidingPuzzle.relabel C e) (SlidingPuzzle.relabel B e),
        s.length = p.length := ⟨p.reverse.relabel e he, by simp⟩
    rwa [hC] at h
  obtain ⟨s, hs⟩ := hret
  refine ⟨SlidingPuzzle.relabel B e, (p.append q).append s, ?_,
    blank_relabel B e he, fun _ => rfl⟩
  simp only [Path.length_append, hs]
  omega

end SlidingPuzzle
