import NestedRouting.Board.Basic

/-! A square of side `s` placed inside the board by a translation and
independent row and column reflections. This is the only geometry a leaf
router needs from its position. -/
namespace SlidingPuzzle.NestedRouting

structure Placement (s n : Nat) where
  row : Nat
  col : Nat
  flipRow : Bool
  flipCol : Bool
  row_fits : row+s≤n
  col_fits : col+s≤n

namespace Placement
variable {s n : Nat} (q : Placement s n)

/-- One coordinate: `base+x`, or `base+(s-1-x)` when flipped. -/
def axis (s base : Nat) (flip : Bool) (x : Nat) : Nat :=
  if flip then base+(s-1-x) else base+x

theorem axis_lt {base : Nat} (flip : Bool) (x : Fin s) (fits : base+s≤n) :
    axis s base flip x.val<n := by
  have := x.isLt
  cases flip <;> simp only [axis,Bool.false_eq_true,if_false,if_true] <;> omega

theorem axis_inj {base : Nat} (flip : Bool) (x y : Fin s)
    (equal : axis s base flip x.val=axis s base flip y.val) : x=y := by
  have := x.isLt
  have := y.isLt
  apply Fin.ext
  cases flip <;> simp only [axis,Bool.false_eq_true,if_false,if_true] at equal <;> omega

theorem axis_dist {base : Nat} (flip : Bool) (x y : Fin s) :
    Nat.dist (axis s base flip x.val) (axis s base flip y.val)=Nat.dist x.val y.val := by
  have := x.isLt
  have := y.isLt
  cases flip <;> simp only [axis,Bool.false_eq_true,if_false,if_true,Nat.dist] <;> omega

def embed : Cell s ↪ Cell n where
  toFun x := (⟨axis s q.row q.flipRow x.1.val,axis_lt q.flipRow x.1 q.row_fits⟩,
    ⟨axis s q.col q.flipCol x.2.val,axis_lt q.flipCol x.2 q.col_fits⟩)
  inj' := by
    intro x y equal
    exact Prod.ext (axis_inj q.flipRow x.1 y.1 (congrArg (fun z : Cell n => z.1.val) equal))
      (axis_inj q.flipCol x.2 y.2 (congrArg (fun z : Cell n => z.2.val) equal))

@[simp] theorem embed_row (x : Cell s) : (q.embed x).1.val=axis s q.row q.flipRow x.1.val := rfl
@[simp] theorem embed_col (x : Cell s) : (q.embed x).2.val=axis s q.col q.flipCol x.2.val := rfl

theorem distance (x y : Cell s) : gridDistance (q.embed x) (q.embed y)=gridDistance x y := by
  change Nat.dist (axis s q.row q.flipRow x.1.val) (axis s q.row q.flipRow y.1.val)+
    Nat.dist (axis s q.col q.flipCol x.2.val) (axis s q.col q.flipCol y.2.val)=_
  rw [axis_dist,axis_dist]
  rfl

end Placement
end SlidingPuzzle.NestedRouting
