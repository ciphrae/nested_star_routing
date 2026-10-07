import NestedRouting.Moves.Local

/-! Lifting local puzzle paths into a larger board without changing outside cells. -/
namespace SlidingPuzzle
variable {m n : ℕ} [NeZero m] [NeZero n]

omit [NeZero m] [NeZero n] in
private theorem swap_embedding (ι : Cell m ↪ Cell n) (a b c : Cell m) :
    Equiv.swap (ι a) (ι b) (ι c)=ι (Equiv.swap a b c) := by
  by_cases ha : c=a
  · subst c; simp
  by_cases hb : c=b
  · subst c; simp
  rw [Equiv.swap_apply_of_ne_of_ne (fun h => ha (ι.injective h))
    (fun h => hb (ι.injective h)), Equiv.swap_apply_of_ne_of_ne ha hb]

/-- Agreement on an embedded subboard identifies the global blank. -/
theorem blank_of_embedded_board (ι : Cell m ↪ Cell n) (η : Tile m ↪ Tile n)
    (hη : η 0=0) (A : Board m) (B : Board n)
    (h : ∀ c, B (ι c)=η (A c)) : blank B=ι (blank A) := by
  apply B.injective
  rw [h]
  simpa [blank,position] using hη.symm

/-- Every local path lifts with exactly the same length, and all cells outside
its embedded board remain fixed. -/
theorem Path.exists_embedded {A D : Board m} (p : Path A D)
    (ι : Cell m ↪ Cell n) (hι : ∀ a b, gridDistance a b=1 → gridDistance (ι a) (ι b)=1)
    (η : Tile m ↪ Tile n) (hη : η 0=0) (B : Board n)
    (hB : ∀ c, B (ι c)=η (A c)) :
    ∃ C : Board n, ∃ q : Path B C, q.length=p.length ∧
      (∀ c, C (ι c)=η (D c)) ∧
      (∀ c : Cell n, c ∉ Set.range ι → C c=B c) := by
  induction p generalizing B with
  | nil A => exact ⟨B,Path.nil B,rfl,hB,fun _ _ => rfl⟩
  | @cons A A' D hstep p ih =>
      obtain ⟨c,hc,rfl⟩ := hstep
      have hb := blank_of_embedded_board ι η hη A B hB
      let B' := swapCells B (ι (blank A)) (ι c)
      have hB' (x : Cell m) : B' (ι x)=η (swapCells A (blank A) c x) := by
        simp only [B',swapCells_apply,swap_embedding,hB]
      obtain ⟨C,q,hq,hC,hfix⟩ := ih B' hB'
      have hstep : Step B B' := ⟨ι c,by rw [hb]; exact hι _ _ hc,by rw [hb]⟩
      refine ⟨C,Path.cons hstep q,?_,hC,?_⟩
      · simp [Path.length,hq]
      · intro x hx
        rw [hfix x hx]
        exact swapCells_preserves B
          (fun h => hx ⟨blank A,h.symm⟩) (fun h => hx ⟨c,h.symm⟩)
end SlidingPuzzle
