import NestedRouting.Moves.SupportedFinish
import NestedRouting.Moves.LocalThreeCycle

/-! Construct supported goals from actual requested labels, then finish them
at cost linear in the residual set. The complete goal permutation, parity
choice, and local label model are all constructed internally. -/
namespace SlidingPuzzle.LocalBlockFinish
open Finset
variable {m n : Nat} [NeZero m] [NeZero n]

omit [NeZero n] in
theorem exists_supported_goal (A : Board m) (R F : Finset (Cell m))
    (inside : F⊆R) (free : blank A∉F) (desired : Cell m → Tile m)
    (unique : Set.InjOn desired (F : Set (Cell m)))
    (nonzero : ∀ x∈F, desired x≠0)
    (present : ∀ x∈F, ∃ y∈R, A y=desired x) :
    ∃ G : Board m, blank G=blank A ∧
      (∀ x∈F, G x=desired x) ∧ MarkedCleanup.relativeSupport A G⊆R := by
  classical
  let f : Cell m → Tile m := fun x => if x∈F then desired x else A x
  let S : Finset (Cell m) := insert (blank A) (F∪(univ\R))
  have f_goal (x : Cell m) (hx : x∈F) : f x=desired x := by simp [f,hx]
  have f_fixed (x : Cell m) (hx : x∉F) : f x=A x := by simp [f,hx]
  have f_blank : f (blank A)=0 := by
    rw [f_fixed _ free]
    exact A.apply_symm_apply 0
  have inj : Set.InjOn f (S : Set (Cell m)) := by
    intro x hx y hy eq
    by_cases xF : x∈F
    · by_cases yF : y∈F
      · exact unique xF yF (by simpa only [f_goal x xF,f_goal y yF] using eq)
      · have yrest : y=blank A ∨ y∉R := by
          rcases mem_insert.mp hy with blank | member
          · exact Or.inl blank
          · rcases mem_union.mp member with member | member
            · exact False.elim (yF member)
            · exact Or.inr (mem_sdiff.mp member).2
        rcases yrest with rfl | outside
        · have zero : desired x=0 := by rwa [f_goal x xF,f_blank] at eq
          exact False.elim (nonzero x xF zero)
        · obtain ⟨z,hz,label⟩ := present x xF
          have same : z=y := A.injective (label.trans (by rwa [f_goal x xF,f_fixed y yF] at eq))
          exact False.elim (outside (same ▸ hz))
    · by_cases yF : y∈F
      · have xrest : x=blank A ∨ x∉R := by
          rcases mem_insert.mp hx with blank | member
          · exact Or.inl blank
          · rcases mem_union.mp member with member | member
            · exact False.elim (xF member)
            · exact Or.inr (mem_sdiff.mp member).2
        rcases xrest with rfl | outside
        · have zero : desired y=0 := by symm; rwa [f_blank,f_goal y yF] at eq
          exact False.elim (nonzero y yF zero)
        · obtain ⟨z,hz,label⟩ := present y yF
          have same : z=x := A.injective (label.trans (by symm; rwa [f_fixed x xF,f_goal y yF] at eq))
          exact False.elim (outside (same ▸ hz))
      · exact A.injective (by rwa [f_fixed x xF,f_fixed y yF] at eq)
  obtain ⟨g,hg⟩ := exists_equiv_extend_of_card_eq
    (t:=(univ : Finset (Tile m))) (s:=S) (f:=f)
    (by simp) (fun _ _ => mem_univ _) inj
  let forget : (univ : Finset (Tile m)) ≃ Tile m :=
    ⟨Subtype.val,fun t => ⟨t,mem_univ t⟩,fun t => Subtype.ext rfl,fun _ => rfl⟩
  let G : Board m := g.trans forget
  have agrees (x : Cell m) (hx : x∈S) : G x=f x := hg x hx
  have blankGoal : G (blank A)=0 := (agrees _ (mem_insert_self _ _)).trans f_blank
  refine ⟨G,?_,?_,?_⟩
  · apply G.injective
    change G (G.symm 0)=G (blank A)
    rw [G.apply_symm_apply,blankGoal]
  · intro x hx
    exact (agrees x (mem_insert_of_mem (mem_union_left _ hx))).trans (f_goal x hx)
  · apply (MarkedCleanup.relativeSupport_subset_iff A G R).mpr
    intro x outside
    have xF : x∉F := fun member => outside (inside member)
    have xS : x∈S := mem_insert_of_mem (mem_union_right _ (mem_sdiff.mpr ⟨mem_univ _,outside⟩))
    exact ((agrees x xS).trans (f_fixed x xF)).symm

omit [NeZero n] in
theorem exists_supported_requested_finish (A : Board m) (hm : 6≤m)
    (R F : Finset (Cell m)) (inside : F⊆R) (free : blank A∉F)
    (desired : Cell m → Tile m) (unique : Set.InjOn desired (F : Set (Cell m)))
    (nonzero : ∀ x∈F, desired x≠0) (present : ∀ x∈F, ∃ y∈R, A y=desired x)
    (a b : Cell m) (haR : a∈R) (hbR : b∈R) (hab : a≠b)
    (haF : a∉F) (hbF : b∉F) (haB : a≠blank A) (hbB : b≠blank A) :
    ∃ C : Board m, ∃ path : Path A C,
      path.length≤54*m*R.card ∧ blank C=blank A ∧
      (∀ x, x∉R → C x=A x) ∧ ∀ x∈F, C x=desired x := by
  obtain ⟨G,blankG,goals,support⟩ := exists_supported_goal A R F inside free desired unique nonzero present
  have nonblank (x : Cell m) (hx : x≠blank A) : G x≠0 := by
    intro zero
    apply hx
    rw [←blankG]
    apply G.injective
    simpa [blank,position] using zero
  obtain ⟨C,path,cost,blankC,_,done,fixed⟩ := MarkedCleanup.exists_supported_finish_with_two_helpers
    A G hm blankG.symm R support a b haR hbR hab (nonblank a haB) (nonblank b hbB)
  refine ⟨C,path,cost,blankC,fixed,?_⟩
  intro x hx
  exact (done x (fun eq => haF (eq ▸ hx)) (fun eq => hbF (eq ▸ hx))).trans (goals x hx)

omit [NeZero n] in
theorem exists_two_free_slots_in (A : Board m) (R F : Finset (Cell m))
    (room : F.card+3≤R.card) :
    ∃ a b : Cell m, a∈R ∧ b∈R ∧ a≠b ∧ a∉F ∧ b∉F ∧ a≠blank A ∧ b≠blank A := by
  classical
  let free := R\insert (blank A) F
  have many : 1<free.card := by
    have diff := card_le_card_sdiff_add_card (s:=R) (t:=insert (blank A) F)
    have insertBound := card_insert_le (blank A) F
    dsimp [free]
    omega
  obtain ⟨a,ha,b,hb,different⟩ := one_lt_card.mp many
  have aR := (mem_sdiff.mp ha).1
  have bR := (mem_sdiff.mp hb).1
  have aoff := (mem_sdiff.mp ha).2
  have boff := (mem_sdiff.mp hb).2
  exact ⟨a,b,aR,bR,different,
    fun member => aoff (mem_insert_of_mem member),fun member => boff (mem_insert_of_mem member),
    fun eq => aoff (eq.symm ▸ mem_insert_self (blank A) F),
    fun eq => boff (eq.symm ▸ mem_insert_self (blank A) F)⟩

theorem exists_finish_supported_real_goals (ι : Cell m ↪ Cell n)
    (hι : ∀ x y, gridDistance x y=1 → gridDistance (ι x) (ι y)=1)
    (B T : Board n) (hm : 6≤m) (hblank : blank B∈Set.range ι)
    (R F : Finset (Cell m)) (inside : F⊆R)
    (hfree : ∀ x∈F, ι x≠blank B) (hnonzero : ∀ x∈F, T (ι x)≠0)
    (hpresent : ∀ x∈F, ∃ y∈R, B (ι y)=T (ι x)) (room : F.card+3≤R.card) :
    ∃ C : Board n, ∃ path : Path B C,
      path.length≤54*m*R.card ∧ blank C=blank B ∧
      (∀ x : Cell n, x∉R.map ι → C x=B x) ∧ ∀ x∈F, C (ι x)=T (ι x) := by
  classical
  obtain ⟨A,η,hη,hB⟩ := LocalStaging.exists_local_model ι B hblank
  have blankA : blank B=ι (blank A) := blank_of_embedded_board ι η hη A B hB
  have free : blank A∉F := fun hx => hfree _ hx blankA.symm
  let desired : Cell m → Tile m := fun x =>
    if hx : x∈F then A (hpresent x hx).choose else A x
  have label (x : Cell m) (hx : x∈F) : η (desired x)=T (ι x) := by
    simp only [desired,dif_pos hx]
    rw [←hB]
    exact (hpresent x hx).choose_spec.2
  have present (x : Cell m) (hx : x∈F) : ∃ y∈R, A y=desired x := by
    exact ⟨(hpresent x hx).choose,(hpresent x hx).choose_spec.1,by simp [desired,hx]⟩
  have unique : Set.InjOn desired (F : Set (Cell m)) := by
    intro x hx y hy eq
    apply ι.injective
    apply T.injective
    rw [←label x hx,←label y hy,eq]
  have nonzero (x : Cell m) (hx : x∈F) : desired x≠0 := by
    intro zero
    have eq := label x hx
    rw [zero,hη] at eq
    exact hnonzero x hx eq.symm
  obtain ⟨a,b,haR,hbR,hab,haF,hbF,haB,hbB⟩ := exists_two_free_slots_in A R F room
  obtain ⟨D,localPath,cost,blankD,fixed,done⟩ := exists_supported_requested_finish A hm R F
    inside free desired unique nonzero present a b haR hbR hab haF hbF haB hbB
  obtain ⟨C,path,length,localBoard,outside⟩ := localPath.exists_embedded ι hι η hη B hB
  refine ⟨C,path,by omega,?_,?_,?_⟩
  · rw [blank_of_embedded_board ι η hη D C localBoard,blankD,blankA]
  · intro x hx
    by_cases inSquare : x∈Set.range ι
    · obtain ⟨y,rfl⟩ := inSquare
      have hy : y∉R := fun member => hx (mem_map.mpr ⟨y,member,rfl⟩)
      rw [localBoard,fixed y hy,hB]
    · exact outside x inSquare
  · intro x hx
    rw [localBoard,done x hx,label x hx]

end SlidingPuzzle.LocalBlockFinish
