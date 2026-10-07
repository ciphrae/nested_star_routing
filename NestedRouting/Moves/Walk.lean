import NestedRouting.Moves.Local
import MathlibRoots

/-! Blank walks along lists of cells with their exact effect. Walking the
blank from the head of `l` through every later cell permutes the board by
`l.formPerm`: the tile at each cell moves one step back along the list and
the blank ends on the last cell. Lanes are lists of cells, so queue shifts
are read directly from this permutation. -/
namespace SlidingPuzzle.NestedRouting
variable {n : Nat}

/-- Consecutive cells are adjacent. -/
def Chained (l : List (Cell n)) : Prop := l.IsChain (fun a b => gridDistance a b=1)

theorem Chained.tail {a : Cell n} {l : List (Cell n)} (h : Chained (a :: l)) : Chained l := by
  cases l with
  | nil => exact List.isChain_nil
  | cons b l => exact (List.isChain_cons_cons.mp h).2

theorem blank_swapCells [NeZero n] (B : Board n) (b : Cell n) :
    blank (swapCells B (blank B) b)=b := by
  apply (swapCells B (blank B) b).symm_apply_eq.mpr
  simp [blank,position]

variable [NeZero n]

/-- Walk the blank along `a :: rest`. -/
theorem exists_walk (a : Cell n) (rest : List (Cell n)) (chain : Chained (a :: rest))
    (B : Board n) (atStart : blank B=a) :
    ∃ C : Board n, ∃ path : Path B C,
      path.length=rest.length ∧ ∀ x, C x=B ((a :: rest).formPerm x) := by
  induction rest generalizing a B with
  | nil => exact ⟨B,.nil B,rfl,fun x => by simp⟩
  | cons b rest ih =>
    have adj := (List.isChain_cons_cons.mp chain).1
    let next := swapCells B (blank B) b
    obtain ⟨C,path,length,effect⟩ := ih b chain.tail next (blank_swapCells B b)
    let step := movePath B b (by rwa [atStart])
    refine ⟨C,step.append path,?_,?_⟩
    · simp [step,length,Nat.add_comm]
    · intro x
      rw [effect x,List.formPerm_cons_cons,Equiv.Perm.mul_apply]
      simp [next,atStart]

/-- The blank ends on the last cell. -/
theorem walk_blank (a : Cell n) (rest : List (Cell n)) {B C : Board n}
    (effect : ∀ x, C x=B ((a :: rest).formPerm x)) (atStart : blank B=a) :
    blank C=(a :: rest).getLast (List.cons_ne_nil a rest) := by
  apply C.symm_apply_eq.mpr
  rw [effect,List.formPerm_apply_getLast,←atStart]
  simp [blank,position]

omit [NeZero n] in
/-- Cells off the walk are untouched. -/
theorem walk_fixed (l : List (Cell n)) {B C : Board n} (effect : ∀ x, C x=B (l.formPerm x))
    {x : Cell n} (hx : x∉l) : C x=B x := by
  rw [effect,List.formPerm_apply_of_notMem hx]

omit [NeZero n] in
/-- On a list without repeats, `formPerm` rotates it by one. -/
theorem map_formPerm_eq_rotate {α : Type*} [DecidableEq α] (l : List α) (nodup : l.Nodup) :
    l.map l.formPerm=l.rotate 1 := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map,List.getElem_rotate]
  rw [List.formPerm_apply_getElem l nodup i (by simpa using h1)]

omit [NeZero n] in
/-- A walk rotates the contents read along it: the head's tile goes last. -/
theorem walk_contents (a : Cell n) (t : List (Cell n)) (nodup : (a :: t).Nodup) {B C : Board n}
    (effect : ∀ x, C x=B ((a :: t).formPerm x)) : (a :: t).map C=t.map B++[B a] := by
  have h : (a :: t).map C=((a :: t).map (a :: t).formPerm).map B := by
    rw [List.map_map]
    exact List.map_congr_left (fun x _ => effect x)
  rw [h,map_formPerm_eq_rotate _ nodup,List.rotate_cons_succ,List.rotate_zero]
  simp

end SlidingPuzzle.NestedRouting
