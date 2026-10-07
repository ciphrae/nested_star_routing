import MathlibRoots
import NestedRouting.Moves.Routes
import NestedRouting.Moves.Relabel

/-! Canonical-target bounds imply bounds for arbitrary mutually reachable
boards. Tile renaming fixes the blank and preserves each actual slide.
An arbitrary target is normalized with at most 2*n additional slides.
-/
namespace SlidingPuzzle
variable {n : Nat} [NeZero n]

def targetRenaming (T : Board n) : Tile n ≃ Tile n := T.symm.trans (target n)

theorem targetRenaming_zero (T : Board n) (parked : blank T=blank (target n)) :
    targetRenaming T 0=0 := by
  change target n (T.symm 0)=0
  change T.symm 0=(target n).symm 0 at parked
  rw [parked]
  exact (target n).apply_symm_apply 0

omit [NeZero n] in
@[simp] theorem relabel_targetRenaming (T : Board n) :
    relabel T (targetRenaming T)=target n := by
  ext x
  simp [relabel,targetRenaming]

/-- Apply any canonical solver to a pair whose target blank is parked.
The canonical solver's path length is preserved exactly. -/
theorem pair_bound_of_canonical_parked (bound : Real)
    (solver : ∀ A : Board n, Reachable A →
      ∃ p : Path A (target n), (p.length : Real)≤bound)
    (B T : Board n) (reachable : Nonempty (Path B T))
    (parked : blank T=blank (target n)) :
    ∃ p : Path B T, (p.length : Real)≤bound := by
  let τ := targetRenaming T
  have zero : τ 0=0 := targetRenaming_zero T parked
  obtain ⟨old⟩ := reachable
  have renamed : Nonempty (Path (relabel B τ) (target n)) := by
    simpa [τ] using (show Nonempty (Path (relabel B τ) (relabel T τ)) from ⟨old.relabel τ zero⟩)
  have scrambled : Reachable (relabel B τ) := by
    obtain ⟨p⟩ := renamed
    exact ⟨p.reverse⟩
  obtain ⟨p,hp⟩ := solver (relabel B τ) scrambled
  have inverse : τ.symm 0=0 := (τ.symm_apply_eq).mpr zero.symm
  have endBoard : relabel (target n) τ.symm=T := by
    rw [←relabel_targetRenaming T]
    exact relabel_relabel_symm T τ
  let q := p.relabel τ.symm inverse
  have qlength : q.length=p.length := Path.length_relabel p τ.symm inverse
  have result : ∃ q : Path (relabel (relabel B τ) τ.symm) (relabel (target n) τ.symm),
      (q.length : Real)≤bound := ⟨q,by rw [qlength]; exact hp⟩
  rw [relabel_relabel_symm,endBoard] at result
  exact result

theorem pair_bound_of_canonical (bound : Real)
    (solver : ∀ A : Board n, Reachable A →
      ∃ p : Path A (target n), (p.length : Real)≤bound)
    (B T : Board n) (reachable : Nonempty (Path B T)) :
    ∃ p : Path B T, (p.length : Real)≤bound+2*(n : Real) := by
  obtain ⟨U,access,parked,length,_⟩ := exists_blank_access_path_elbow T (blank (target n))
  obtain ⟨old⟩ := reachable
  obtain ⟨p,hp⟩ := pair_bound_of_canonical_parked bound solver B U
    ⟨old.append access⟩ parked
  refine ⟨p.append access.reverse,?_⟩
  have accessR : (access.length : Real)≤2*(n : Real) := by exact_mod_cast length
  simp only [Path.length_append,Path.length_reverse,Nat.cast_add]
  linarith

end SlidingPuzzle
