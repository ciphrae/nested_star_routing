import NestedRouting.Corner.Layout

/-! Board coordinates and rectangular frames for the root: `cc r c` is the
board cell at row `r`, column `c`, and `hframe` is a rectangle with a corner
on a given row, its first axis along that row. -/
namespace SlidingPuzzle.NestedRouting.Central
open Placement Routes

set_option linter.unusedSectionVars false

variable {n : Nat} [NeZero n]

namespace CParams

/-- The whole board, for direct exchanges. -/
def boardP : Placement n n := ⟨0,0,false,false,by omega,by omega⟩

theorem boardP_range (y : Cell n) : y∈Set.range (boardP (n:=n)).embed :=
  ⟨y,by apply Prod.ext <;> apply Fin.ext <;> simp [boardP,axis]⟩

end CParams

/-- A frame with its axes exchanged. -/
def _root_.SlidingPuzzle.NestedRouting.Routes.Frame.transpose (F : Routes.Frame n) : Routes.Frame n where
  R := F.C
  C := F.R
  loc r c := F.loc c r
  inj := fun hr hc hr' hc' e => (F.inj hc hr hc' hr' e).symm
  dist := by
    intro r c r' c' hr hc hr' hc'
    rw [F.dist hc hr hc' hr']; omega

/-- The board cell at row `r`, column `c`. -/
def cc (r c : Nat) : Cell n := (CParams.boardP (n:=n)).loc r c

theorem cc_val {r c : Nat} (hr : r<n) (hc : c<n) : (cc (n:=n) r c).1.val=r ∧ (cc (n:=n) r c).2.val=c := by
  unfold cc; rw [(CParams.boardP (n:=n)).loc_eq hr hc]; simp [axis,CParams.boardP]

theorem cell_eq {x y : Cell n} (h1 : x.1.val=y.1.val) (h2 : x.2.val=y.2.val) : x=y :=
  Prod.ext (Fin.ext h1) (Fin.ext h2)

theorem cc_self (y : Cell n) : cc y.1.val y.2.val=y := by
  have := cc_val (n:=n) y.1.isLt y.2.isLt
  exact cell_eq this.1 this.2

theorem cc_ne {r c r' c' : Nat} (hr : r<n) (hc : c<n) (hr' : r'<n) (hc' : c'<n) (h : r≠r' ∨ c≠c') :
    cc (n:=n) r c≠cc r' c' := by
  intro e
  have a := cc_val (n:=n) hr hc; have b := cc_val (n:=n) hr' hc'
  rw [e] at a; omega

/-- A frame at the middle row: first axis along row `c0` from column `a`
(leftwards when `dc`), second axis up (`dr`) or down. -/
def hframe (c0 a R C : Nat) (dr dc : Bool) (hc0 : c0<n) (ha : a<n) (hR : dc=true → R≤a+1)
    (hR' : dc=false → a+R≤n) (hC : dr=true → C≤c0+1) (hC' : dr=false → c0+C≤n) : Routes.Frame n :=
  ((CParams.boardP (n:=n)).rect c0 a C R dr dc hc0 ha hC hC' hR hR').transpose

theorem hframe_loc {c0 a R C : Nat} {dr dc : Bool} {hc0 ha hR hR' hC hC'} (i j : Nat) :
    (hframe (n:=n) c0 a R C dr dc hc0 ha hR hR' hC hC').loc i j=cc (ax dr c0 j) (ax dc a i) := rfl

theorem hframe_R {c0 a R C : Nat} {dr dc : Bool} {hc0 ha hR hR' hC hC'} :
    (hframe (n:=n) c0 a R C dr dc hc0 ha hR hR' hC hC').R=R := rfl

theorem hframe_C {c0 a R C : Nat} {dr dc : Bool} {hc0 ha hR hR' hC hC'} :
    (hframe (n:=n) c0 a R C dr dc hc0 ha hR hR' hC hC').C=C := rfl

end SlidingPuzzle.NestedRouting.Central
