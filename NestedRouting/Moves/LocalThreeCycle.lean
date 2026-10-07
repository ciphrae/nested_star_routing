import NestedRouting.Moves.ThreeCycle
import NestedRouting.Moves.Embedding

/-! Sharp local staging inside an embedded square, with genuine ambient paths. -/
namespace SlidingPuzzle.LocalStaging
variable {m n : Nat} [NeZero m] [NeZero n]

/-- Every actual embedded square containing the blank admits local labels.
No assumption is made about which nonblank ambient labels occupy the square. -/
theorem exists_local_model (ι : Cell m ↪ Cell n) (B : Board n)
    (hblank : blank B ∈ Set.range ι) :
    ∃ A : Board m, ∃ η : Tile m ↪ Tile n,
      η 0 = 0 ∧ ∀ x, B (ι x) = η (A x) := by
  classical
  obtain ⟨p,hp⟩ := hblank
  let A : Board m := swapCells (target m) (blank (target m)) p
  have hbA : blank A = p := blank_swapCells (target m) p
  let η : Tile m ↪ Tile n := A.symm.toEmbedding.trans (ι.trans B.toEmbedding)
  refine ⟨A,η,?_,?_⟩
  · change B (ι (blank A)) = 0
    rw [hbA,hp]
    exact B.apply_symm_apply 0
  · intro x
    simp [η]

/-- Exact three-cycle inside an m-by-m block; cost depends on m, not n.
The blank and every other ambient cell are restored. -/
theorem exists_three_cycle_local (ι : Cell m ↪ Cell n)
    (hι : ∀ a b, gridDistance a b=1 → gridDistance (ι a) (ι b)=1)
    (B : Board n) (hm : 6 ≤ m) (hblank : blank B ∈ Set.range ι)
    (a b c : Cell m) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : B (ι a) ≠ 0) (hb : B (ι b) ≠ 0) (hc : B (ι c) ≠ 0) :
    ∃ C : Board n, ∃ q : Path B C,
      q.length ≤ 54*m ∧ blank C=blank B ∧
      C (ι a)=B (ι b) ∧ C (ι b)=B (ι c) ∧ C (ι c)=B (ι a) ∧
      ∀ x, x ≠ ι a → x ≠ ι b → x ≠ ι c → C x=B x := by
  obtain ⟨A,η,hη,hB⟩ := exists_local_model ι B hblank
  have hnonzero (x : Cell m) (hx : B (ι x) ≠ 0) : A x ≠ 0 := by
    intro hz
    apply hx
    rw [hB,hz,hη]
  obtain ⟨D,q,hq,hbD,hDa,hDb,hDc,hfixD⟩ :=
    exists_three_cycle A hm a b c hab hac hbc
      (hnonzero a ha) (hnonzero b hb) (hnonzero c hc)
  obtain ⟨C,s,hs,hC,hfixC⟩ := Path.exists_embedded q ι hι η hη B hB
  refine ⟨C,s,by omega,?_,?_,?_,?_,?_⟩
  · rw [blank_of_embedded_board ι η hη D C hC,hbD,← blank_of_embedded_board ι η hη A B hB]
  · rw [hC,hDa,← hB]
  · rw [hC,hDb,← hB]
  · rw [hC,hDc,← hB]
  · intro x hxa hxb hxc
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨y,rfl⟩ := hx
      rw [hC,hfixD y (fun h => hxa (congrArg ι h))
        (fun h => hxb (congrArg ι h)) (fun h => hxc (congrArg ι h)),← hB]
    · exact hfixC x hx

end SlidingPuzzle.LocalStaging
