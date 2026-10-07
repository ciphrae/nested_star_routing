import NestedRouting.Moves.ThreeCycle
import NestedRouting.Board.OrbitParity
import NestedRouting.Moves.Embedding

/-!
# Marked-label preprocessing by actual puzzle paths

This file is independent of the proposed routing construction. It gathers a
prescribed set of marked labels into an equally large reserve, preserving a
blank that is already in that reserve. Each reduction uses the upstream
`exists_three_cycle`, so the result constructs `SlidingPuzzle.Path`,
not an abstract permutation or an assumed physical primitive.
-/

namespace SlidingPuzzle.MarkedCleanup

open Finset

variable {n : ℕ} [NeZero n]

/-- Cells currently occupied by one of the marked labels. -/
def markedCells (B : Board n) (M : Finset (Tile n)) : Finset (Cell n) :=
  M.image B.symm

omit [NeZero n] in
@[simp] theorem mem_markedCells (B : Board n) (M : Finset (Tile n)) (x : Cell n) :
    x ∈ markedCells B M ↔ B x ∈ M := by
  constructor
  · intro hx
    obtain ⟨a, ha, heq⟩ := mem_image.mp hx
    rw [← heq]
    simpa using ha
  · intro hx
    exact mem_image.mpr ⟨B x, hx, B.symm_apply_apply x⟩

omit [NeZero n] in
@[simp] theorem card_markedCells (B : Board n) (M : Finset (Tile n)) :
    (markedCells B M).card = M.card :=
  card_image_of_injective M B.symm.injective

/-- Marked labels outside the reserve. -/
def misplacedMarked (B : Board n) (M : Finset (Tile n)) (R : Finset (Cell n)) :
    Finset (Cell n) := markedCells B M \ R

omit [NeZero n] in
@[simp] theorem mem_misplacedMarked (B : Board n) (M : Finset (Tile n))
    (R : Finset (Cell n)) (x : Cell n) :
    x ∈ misplacedMarked B M R ↔ B x ∈ M ∧ x ∉ R := by
  simp [misplacedMarked]

omit [NeZero n] in
/-- Equal capacities force an unmarked tile inside whenever a marked tile is outside. -/
theorem exists_unmarked_inside (B : Board n) (M : Finset (Tile n))
    (R : Finset (Cell n)) (hcard : M.card = R.card)
    (a : Cell n) (haM : B a ∈ M) (haR : a ∉ R) :
    ∃ b ∈ R, B b ∉ M := by
  classical
  by_contra! hno
  have hsub : R ⊆ markedCells B M := by
    intro b hb
    exact (mem_markedCells B M b).mpr (hno b hb)
  have heq : R = markedCells B M := eq_of_subset_of_card_le hsub (by simp [hcard])
  exact haR (heq.symm ▸ (mem_markedCells B M a).mpr haM)

omit [NeZero n] in
/-- If the reserve occupies less than half the board, an unmarked outside site exists. -/
theorem exists_unmarked_outside (B : Board n) (M : Finset (Tile n))
    (R : Finset (Cell n)) (hcard : M.card = R.card)
    (hsmall : 2 * R.card < n * n) :
    ∃ c, c ∉ R ∧ B c ∉ M := by
  classical
  by_contra! hno
  have hcover : univ ⊆ R ∪ markedCells B M := by
    intro c _
    by_cases hc : c ∈ R
    · exact mem_union_left _ hc
    · exact mem_union_right _ ((mem_markedCells B M c).mpr (hno c hc))
  have h1 := card_le_card hcover
  have h2 := card_union_le R (markedCells B M)
  simp only [card_univ, Fintype.card_prod, Fintype.card_fin, card_markedCells,
    hcard] at h1 h2
  omega

/-- A single exact three-cycle decreases the number of marked tiles outside. -/
theorem gather_step (B : Board n) (hn : 6 ≤ n) (M : Finset (Tile n))
    (R : Finset (Cell n)) (hcard : M.card = R.card)
    (hzero : (0 : Tile n) ∈ M) (hb : blank B ∈ R)
    (hsmall : 2 * R.card < n * n)
    (hpos : 0 < (misplacedMarked B M R).card) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 54 * n ∧ blank C = blank B ∧
      (misplacedMarked C M R).card + 1 ≤ (misplacedMarked B M R).card := by
  classical
  obtain ⟨a, ha⟩ := card_pos.mp hpos
  obtain ⟨haM, haR⟩ := (mem_misplacedMarked B M R a).mp ha
  obtain ⟨b, hbR, hbM⟩ := exists_unmarked_inside B M R hcard a haM haR
  obtain ⟨c, hcR, hcM⟩ := exists_unmarked_outside B M R hcard hsmall
  have hba : b ≠ a := fun e => haR (e ▸ hbR)
  have hbc : b ≠ c := fun e => hcR (e ▸ hbR)
  have hac : a ≠ c := fun e => hcM (e ▸ haM)
  have ha0 : B a ≠ 0 := by
    intro h
    have heq : a = blank B := B.injective (by simpa [blank, position] using h)
    exact haR (heq.symm ▸ hb)
  have hb0 : B b ≠ 0 := fun h => hbM (h.symm ▸ hzero)
  have hc0 : B c ≠ 0 := fun h => hcM (h.symm ▸ hzero)
  obtain ⟨C, p, hp, hbC, hCb, hCa, hCc, hfix⟩ :=
    exists_three_cycle B hn b a c hba hbc hac hb0 ha0 hc0
  refine ⟨C, p, hp, hbC, ?_⟩
  have hsub : misplacedMarked C M R ⊆ (misplacedMarked B M R).erase a := by
    intro x hx
    obtain ⟨hxM, hxR⟩ := (mem_misplacedMarked C M R x).mp hx
    have hxa : x ≠ a := by
      rintro rfl
      rw [hCa] at hxM
      exact hcM hxM
    have hxb : x ≠ b := by
      rintro rfl
      exact hxR hbR
    have hxc : x ≠ c := by
      rintro rfl
      rw [hCc] at hxM
      exact hbM hxM
    rw [hfix x hxb hxa hxc] at hxM
    exact mem_erase.mpr ⟨hxa, (mem_misplacedMarked B M R x).mpr ⟨hxM, hxR⟩⟩
  have hle := card_le_card hsub
  rw [card_erase_of_mem ha] at hle
  omega

/-- Gather all marked labels in at most `54*n` moves per initially misplaced mark.

The blank is assumed already in the reserve. Moving it there is a separate
preliminary path; no parity assumption on the initial board is needed here.
-/
theorem exists_gather_marked (B : Board n) (hn : 6 ≤ n) (M : Finset (Tile n))
    (R : Finset (Cell n)) (hcard : M.card = R.card)
    (hzero : (0 : Tile n) ∈ M) (hb : blank B ∈ R)
    (hsmall : 2 * R.card < n * n) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 54 * n * (misplacedMarked B M R).card ∧
      blank C = blank B ∧ markedCells C M = R := by
  classical
  generalize hm : (misplacedMarked B M R).card = m
  induction m using Nat.strong_induction_on generalizing B with
  | h m ih =>
    by_cases hm0 : m = 0
    · have hsub : markedCells B M ⊆ R := by
        intro x hx
        by_contra hxR
        have hmem : x ∈ misplacedMarked B M R := mem_sdiff.mpr ⟨hx, hxR⟩
        have := card_pos.mpr ⟨x, hmem⟩
        omega
      refine ⟨B, Path.nil B, by simp, rfl, ?_⟩
      exact eq_of_subset_of_card_le hsub (by simp [hcard])
    · obtain ⟨C, p, hp, hbC, hdrop⟩ := gather_step B hn M R hcard hzero hb hsmall
        (by omega)
      have hcsmall : (misplacedMarked C M R).card < m := by omega
      obtain ⟨D, q, hq, hbD, hD⟩ := ih (misplacedMarked C M R).card hcsmall C
        (hbC.symm ▸ hb) rfl
      refine ⟨D, p.append q, ?_, hbD.trans hbC, hD⟩
      rw [Path.length_append]
      have hmul := Nat.mul_le_mul_left (54 * n) hdrop
      nlinarith

/-- Uniform preprocessing bound in terms of the reserve size alone. -/
theorem exists_gather_marked_card (B : Board n) (hn : 6 ≤ n)
    (M : Finset (Tile n)) (R : Finset (Cell n)) (hcard : M.card = R.card)
    (hzero : (0 : Tile n) ∈ M) (hb : blank B ∈ R)
    (hsmall : 2 * R.card < n * n) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 54 * n * R.card ∧ blank C = blank B ∧
      ∀ x, C x ∈ M ↔ x ∈ R := by
  obtain ⟨C, p, hp, hbC, hC⟩ := exists_gather_marked B hn M R hcard hzero hb hsmall
  refine ⟨C, p, hp.trans ?_, hbC, ?_⟩
  · apply Nat.mul_le_mul_left
    have hc := card_le_card (sdiff_subset : misplacedMarked B M R ⊆ markedCells B M)
    simpa [misplacedMarked, hcard] using hc
  · intro x
    rw [← mem_markedCells, hC]

/-- Once a reachable board's blank is at its goal, its residual cell permutation
is even. This is a consequence of actual path invariance, not a parity premise
silently imposed on the terminal configuration. -/
theorem residual_sign_eq_one (B : Board n) (hreach : Reachable B)
    (hblank : blank B = blank (target n)) : boardSign B = 1 := by
  have h := reachable_parityInvariant B hreach
  rw [parityInvariant, hblank] at h
  exact mul_right_cancel (show boardSign B * colorSign (blank (target n)) =
    1 * colorSign (blank (target n)) by simpa using h)

/-- A routing/finishing path preserves reachability for the terminal parity argument. -/
theorem reachable_after_path {B C : Board n} (hreach : Reachable B) (p : Path B C) :
    Reachable C := by
  obtain ⟨q⟩ := hreach
  exact ⟨q.append p⟩

/-- A legal path that returns the blank preserves the cell permutation sign. -/
theorem boardSign_after_closed_path {B C : Board n} (p : Path B C)
    (hblank : blank C = blank B) : boardSign C = boardSign B := by
  have h := p.parityInvariant
  rw [parityInvariant, parityInvariant, hblank] at h
  exact mul_right_cancel h

omit [NeZero n] in
/-- The exact residual support lies inside the chosen reserve when all real
positions are solved. -/
theorem residual_support_subset (B : Board n) (R : Finset (Cell n))
    (hfix : ∀ x, x ∉ R → B x = target n x) :
    Equiv.Perm.support (B.trans (target n).symm) ⊆ R := by
  classical
  intro x hx
  by_contra hxR
  apply (Equiv.Perm.mem_support.mp hx)
  change (target n).symm (B x) = x
  rw [hfix x hxR]
  exact (target n).symm_apply_apply x

/-- The actual cells on which a board differs from the target. -/
def residualSupport (B : Board n) : Finset (Cell n) :=
  Equiv.Perm.support (B.trans (target n).symm)

omit [NeZero n] in
@[simp] theorem mem_residualSupport (B : Board n) (x : Cell n) :
    x ∈ residualSupport B ↔ B x ≠ target n x := by
  rw [residualSupport, Equiv.Perm.mem_support]
  change (target n).symm (B x) ≠ x ↔ B x ≠ target n x
  constructor
  · intro h heq
    apply h
    rw [heq]
    exact (target n).symm_apply_apply x
  · intro h heq
    apply h
    apply (target n).symm.injective
    simpa using heq

omit [NeZero n] in
/-- An even nonidentity permutation has at least three support cells. -/
theorem residualSupport_three_le (B : Board n) (hsign : boardSign B = 1)
    (hpos : 0 < (residualSupport B).card) :
    3 ≤ (residualSupport B).card := by
  have h1 := Equiv.Perm.card_support_ne_one (B.trans (target n).symm)
  have h2 : (residualSupport B).card ≠ 2 := by
    intro heq
    have hswap := Equiv.Perm.card_support_eq_two.mp heq
    have hneg := hswap.sign_eq
    change boardSign B = -1 at hneg
    rw [hsign] at hneg
    norm_num at hneg
  change (residualSupport B).card ≠ 1 at h1
  omega

/-- Once the blank is at its target, every incorrectly placed tile is nonblank. -/
theorem residualSupport_nonblank (B : Board n)
    (hblank : blank B = blank (target n)) {x : Cell n}
    (hx : x ∈ residualSupport B) : B x ≠ 0 := by
  intro hx0
  have hxB : x = blank B := B.injective (by simpa [blank, position] using hx0)
  apply (mem_residualSupport B x).mp hx
  rw [hxB, hblank]
  change B (blank (target n)) = (target n) ((target n).symm 0)
  rw [← hblank]
  simp [blank, position]

/-- Fix at least one wrong cell by an exact three-cycle, preserving every
already correct cell and the goal blank. -/
theorem even_residual_cleanup_step (B : Board n) (hn : 6 ≤ n)
    (hsign : boardSign B = 1) (hblank : blank B = blank (target n))
    (hpos : 0 < (residualSupport B).card) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 54 * n ∧ blank C = blank (target n) ∧
      residualSupport C ⊆ residualSupport B ∧
      (residualSupport C).card + 1 ≤ (residualSupport B).card := by
  classical
  have hthree := residualSupport_three_le B hsign hpos
  obtain ⟨a, ha⟩ := card_pos.mp hpos
  let b := B.symm (target n a)
  have hBb : B b = target n a := B.apply_symm_apply _
  have hab : a ≠ b := by
    intro h
    exact (mem_residualSupport B a).mp ha (h ▸ hBb)
  have hb : b ∈ residualSupport B := by
    apply (mem_residualSupport B b).mpr
    intro heq
    exact hab ((target n).injective (hBb.symm.trans heq))
  obtain ⟨c, hc, hca, hcb⟩ : ∃ c ∈ residualSupport B, c ≠ a ∧ c ≠ b := by
    by_contra! hno
    have hsub : residualSupport B ⊆ {a, b} := by
      intro c hc
      by_cases hca : c = a
      · simp [hca]
      · simp [hno c hc hca]
    have hle := card_le_card hsub
    have hpair : ({a, b} : Finset (Cell n)).card ≤ 2 := by simp [hab]
    omega
  obtain ⟨C, p, hp, hbC, hCa, hCb, hCc, hfix⟩ := exists_three_cycle B hn a b c
    hab hca.symm hcb.symm (residualSupport_nonblank B hblank ha)
    (residualSupport_nonblank B hblank hb) (residualSupport_nonblank B hblank hc)
  have hsub : residualSupport C ⊆ (residualSupport B).erase a := by
    intro x hx
    have hxa : x ≠ a := by
      intro h
      apply (mem_residualSupport C x).mp hx
      rw [h, hCa, hBb]
    refine mem_erase.mpr ⟨hxa, ?_⟩
    by_cases hxb : x = b
    · exact hxb.symm ▸ hb
    by_cases hxc : x = c
    · exact hxc.symm ▸ hc
    apply (mem_residualSupport B x).mpr
    have hxne := (mem_residualSupport C x).mp hx
    rwa [hfix x hxa hxb hxc] at hxne
  refine ⟨C, p, hp, hbC.trans hblank, hsub.trans (erase_subset _ _), ?_⟩
  have hle := card_le_card hsub
  rw [card_erase_of_mem ha] at hle
  omega

/-- Any even board with its blank at goal has a legal solution at linear cost
in its residual support size. In particular, this constructs reachability;
reachability is not assumed as a prerequisite. -/
theorem exists_even_residual_cleanup (B : Board n) (hn : 6 ≤ n)
    (hsign : boardSign B = 1) (hblank : blank B = blank (target n)) :
    ∃ p : Path B (target n), p.length ≤ 54 * n * (residualSupport B).card := by
  classical
  generalize hm : (residualSupport B).card = m
  induction m using Nat.strong_induction_on generalizing B with
  | h m ih =>
    by_cases hm0 : m = 0
    · have hB : B = target n := by
        apply Equiv.ext
        intro x
        by_contra hx
        have hmem := (mem_residualSupport B x).mpr hx
        have := card_pos.mpr ⟨x, hmem⟩
        omega
      subst B
      exact ⟨Path.nil _, by simp⟩
    · obtain ⟨C, p, hp, hbC, _, hdrop⟩ := even_residual_cleanup_step B hn hsign hblank
        (by omega)
      have hcsmall : (residualSupport C).card < m := by omega
      have hsC : boardSign C = 1 :=
        (boardSign_after_closed_path p (hbC.trans hblank.symm)).trans hsign
      obtain ⟨q, hq⟩ := ih (residualSupport C).card hcsmall C
        hsC hbC rfl
      refine ⟨p.append q, ?_⟩
      rw [Path.length_append]
      have hmul := Nat.mul_le_mul_left (54 * n) hdrop
      nlinarith

/-- Reachable form of the support-linear cleanup theorem. -/
theorem exists_residual_cleanup (B : Board n) (hn : 6 ≤ n)
    (hreach : Reachable B) (hblank : blank B = blank (target n)) :
    ∃ p : Path B (target n), p.length ≤ 54 * n * (residualSupport B).card :=
  exists_even_residual_cleanup B hn (residual_sign_eq_one B hreach hblank) hblank

/-- In particular, a residual permutation confined to the marked reserve costs
at most `54*n*|R|` moves. -/
theorem exists_reserve_cleanup (B : Board n) (hn : 6 ≤ n)
    (hreach : Reachable B) (hblank : blank B = blank (target n))
    (R : Finset (Cell n)) (hfix : ∀ x, x ∉ R → B x = target n x) :
    ∃ p : Path B (target n), p.length ≤ 54 * n * R.card := by
  obtain ⟨p, hp⟩ := exists_residual_cleanup B hn hreach hblank
  refine ⟨p, hp.trans ?_⟩
  apply Nat.mul_le_mul_left
  exact card_le_card (residual_support_subset B R hfix)

def relativeSign (B G : Board n) : ℤˣ := Equiv.Perm.sign (B.trans G.symm)
omit [NeZero n] in
theorem relativeSign_eq (B G : Board n) : relativeSign B G = boardSign B * boardSign G := by
  have heq : B.trans G.symm = (B.trans (target n).symm).trans (G.trans (target n).symm).symm := by
    apply Equiv.ext
    intro x
    change G.symm (B x) = G.symm ((target n) ((target n).symm (B x)))
    simp
  rw [relativeSign, heq]
  rw [Equiv.Perm.sign_trans, Equiv.Perm.sign_symm]
  exact mul_comm _ _

/-- A closed-blank path preserves sign relative to any fixed goal board. -/
theorem relativeSign_after_closed_path (G : Board n) {B C : Board n} (p : Path B C)
    (hblank : blank C = blank B) : relativeSign C G = relativeSign B G := by
  rw [relativeSign_eq, relativeSign_eq, boardSign_after_closed_path p hblank]

/-- The actual cells on which a board differs from the target. -/
def relativeSupport (B G : Board n) : Finset (Cell n) :=
  Equiv.Perm.support (B.trans G.symm)

omit [NeZero n] in
@[simp] theorem mem_relativeSupport (B G : Board n) (x : Cell n) :
    x ∈ relativeSupport B G ↔ B x ≠ G x := by
  rw [relativeSupport, Equiv.Perm.mem_support]
  change G.symm (B x) ≠ x ↔ B x ≠ G x
  constructor
  · intro h heq
    apply h
    rw [heq]
    exact G.symm_apply_apply x
  · intro h heq
    apply h
    apply G.symm.injective
    simpa using heq

omit [NeZero n] in
/-- An even nonidentity permutation has at least three support cells. -/
theorem relativeSupport_three_le (B G : Board n) (hsign : relativeSign B G = 1)
    (hpos : 0 < (relativeSupport B G).card) :
    3 ≤ (relativeSupport B G).card := by
  have h1 := Equiv.Perm.card_support_ne_one (B.trans G.symm)
  have h2 : (relativeSupport B G).card ≠ 2 := by
    intro heq
    have hswap := Equiv.Perm.card_support_eq_two.mp heq
    have hneg := hswap.sign_eq
    change relativeSign B G = -1 at hneg
    rw [hsign] at hneg
    norm_num at hneg
  change (relativeSupport B G).card ≠ 1 at h1
  omega

/-- Once the blank is at its target, every incorrectly placed tile is nonblank. -/
theorem relativeSupport_nonblank (B G : Board n)
    (hblank : blank B = blank G) {x : Cell n}
    (hx : x ∈ relativeSupport B G) : B x ≠ 0 := by
  intro hx0
  have hxB : x = blank B := B.injective (by simpa [blank, position] using hx0)
  apply (mem_relativeSupport B G x).mp hx
  rw [hxB, hblank]
  change B (blank G) = G (G.symm 0)
  rw [← hblank]
  simp [blank, position]

/-- Fix at least one wrong cell by an exact three-cycle, preserving every
already correct cell and the goal blank. -/
theorem relative_cleanup_step (B G : Board n) (hn : 6 ≤ n)
    (hsign : relativeSign B G = 1) (hblank : blank B = blank G)
    (hpos : 0 < (relativeSupport B G).card) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 54 * n ∧ blank C = blank G ∧
      relativeSupport C G ⊆ relativeSupport B G ∧
      (relativeSupport C G).card + 1 ≤ (relativeSupport B G).card := by
  classical
  have hthree := relativeSupport_three_le B G hsign hpos
  obtain ⟨a, ha⟩ := card_pos.mp hpos
  let b := B.symm (G a)
  have hBb : B b = G a := B.apply_symm_apply _
  have hab : a ≠ b := by
    intro h
    exact (mem_relativeSupport B G a).mp ha (h ▸ hBb)
  have hb : b ∈ relativeSupport B G := by
    apply (mem_relativeSupport B G b).mpr
    intro heq
    exact hab (G.injective (hBb.symm.trans heq))
  obtain ⟨c, hc, hca, hcb⟩ : ∃ c ∈ relativeSupport B G, c ≠ a ∧ c ≠ b := by
    by_contra! hno
    have hsub : relativeSupport B G ⊆ {a, b} := by
      intro c hc
      by_cases hca : c = a
      · simp [hca]
      · simp [hno c hc hca]
    have hle := card_le_card hsub
    have hpair : ({a, b} : Finset (Cell n)).card ≤ 2 := by simp [hab]
    omega
  obtain ⟨C, p, hp, hbC, hCa, hCb, hCc, hfix⟩ := exists_three_cycle B hn a b c
    hab hca.symm hcb.symm (relativeSupport_nonblank B G hblank ha)
    (relativeSupport_nonblank B G hblank hb) (relativeSupport_nonblank B G hblank hc)
  have hsub : relativeSupport C G ⊆ (relativeSupport B G).erase a := by
    intro x hx
    have hxa : x ≠ a := by
      intro h
      apply (mem_relativeSupport C G x).mp hx
      rw [h, hCa, hBb]
    refine mem_erase.mpr ⟨hxa, ?_⟩
    by_cases hxb : x = b
    · exact hxb.symm ▸ hb
    by_cases hxc : x = c
    · exact hxc.symm ▸ hc
    apply (mem_relativeSupport B G x).mpr
    have hxne := (mem_relativeSupport C G x).mp hx
    rwa [hfix x hxa hxb hxc] at hxne
  refine ⟨C, p, hp, hbC.trans hblank, hsub.trans (erase_subset _ _), ?_⟩
  have hle := card_le_card hsub
  rw [card_erase_of_mem ha] at hle
  omega

/-- Any even board with its blank at goal has a legal solution at linear cost
in its residual support size. In particular, this constructs reachability;
reachability is not assumed as a prerequisite. -/
theorem exists_relative_cleanup (B G : Board n) (hn : 6 ≤ n)
    (hsign : relativeSign B G = 1) (hblank : blank B = blank G) :
    ∃ p : Path B G, p.length ≤ 54 * n * (relativeSupport B G).card := by
  classical
  generalize hm : (relativeSupport B G).card = m
  induction m using Nat.strong_induction_on generalizing B with
  | h m ih =>
    by_cases hm0 : m = 0
    · have hB : B = G := by
        apply Equiv.ext
        intro x
        by_contra hx
        have hmem := (mem_relativeSupport B G x).mpr hx
        have := card_pos.mpr ⟨x, hmem⟩
        omega
      subst B
      exact ⟨Path.nil _, by simp⟩
    · obtain ⟨C, p, hp, hbC, _, hdrop⟩ := relative_cleanup_step B G hn hsign hblank
        (by omega)
      have hcsmall : (relativeSupport C G).card < m := by omega
      have hsC : relativeSign C G = 1 :=
        (relativeSign_after_closed_path G p (hbC.trans hblank.symm)).trans hsign
      obtain ⟨q, hq⟩ := ih (relativeSupport C G).card hcsmall C
        hsC hbC rfl
      refine ⟨p.append q, ?_⟩
      rw [Path.length_append]
      have hmul := Nat.mul_le_mul_left (54 * n) hdrop
      nlinarith

/-- Changing the order of two nonblank helper goals leaves the goal blank fixed. -/
theorem blank_swapCells_of_nonblank (G : Board n) (a b : Cell n)
    (ha : G a ≠ 0) (hb : G b ≠ 0) : blank (swapCells G a b) = blank G := by
  unfold blank
  rw [position_swapCells]
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    apply ha
    rw [← h]
    exact G.apply_symm_apply 0
  · intro h
    apply hb
    rw [← h]
    exact G.apply_symm_apply 0

/-- Two interchangeable nonblank helper goals permit an even completion,
without changing any of the other desired positions. -/
theorem exists_even_goal_adjustment (B G : Board n) (a b : Cell n)
    (hab : a ≠ b) (ha : G a ≠ 0) (hb : G b ≠ 0) :
    ∃ C : Board n, (C = G ∨ C = swapCells G a b) ∧
      blank C = blank G ∧ relativeSign B C = 1 ∧
      ∀ x, x ≠ a → x ≠ b → C x = G x := by
  by_cases hs : relativeSign B G = 1
  · exact ⟨G, Or.inl rfl, rfl, hs, fun _ _ _ => rfl⟩
  · have hneg : relativeSign B G = -1 := (Int.units_eq_one_or _).resolve_left hs
    refine ⟨swapCells G a b, Or.inr rfl, blank_swapCells_of_nonblank G a b ha hb, ?_, ?_⟩
    · rw [relativeSign_eq, boardSign_swapCells G hab, mul_neg, ← relativeSign_eq, hneg]
      simp
    · intro x hxa hxb
      simp [Equiv.swap_apply_of_ne_of_ne hxa hxb]

end SlidingPuzzle.MarkedCleanup
