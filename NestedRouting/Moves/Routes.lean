import NestedRouting.Geometry.Grid
import NestedRouting.Moves.Relabel

/-! Blank routes in local coordinates of a frame (a rectangle `[0,R)×[0,C)`
placed in the board, preserving distances): walks along explicit lists,
straight segments, and the elbow access path to any cell. Each comes with the
cells it leaves fixed. -/
namespace SlidingPuzzle.NestedRouting.Routes
open Placement

variable {n : Nat} [NeZero n]

/-! ### Walks with exact effects -/

/-- Walk the blank along `a :: l`: cells off the walk keep their tiles, and
the blank ends on the last cell. If `a` is not visited again, the tile of
the next cell lands on `a`. -/
theorem route (B : Board n) (a : Cell n) (l : List (Cell n)) (chain : Chained (a :: l))
    (hb : blank B=a) :
    ∃ C : Board n, ∃ path : Path B C, path.length=l.length ∧
      blank C=(a :: l).getLast (List.cons_ne_nil a l) ∧
      (∀ y, y∉a :: l → C y=B y) ∧ (∀ y t, l=y :: t → a∉l → C a=B y) := by
  obtain ⟨C,path,len,eff⟩ := exists_walk a l chain B hb
  refine ⟨C,path,len,walk_blank a l eff hb,fun y hy => walk_fixed _ eff hy,?_⟩
  rintro y t rfl ha
  rw [eff,List.formPerm_cons_cons,Equiv.Perm.mul_apply,
    List.formPerm_apply_of_notMem ha,Equiv.swap_apply_left]

/-- Walk the blank along the cells `f 0, …, f k`. -/
theorem seg (B : Board n) (f : Nat → Cell n) (k : Nat)
    (adj : ∀ i, i<k → gridDistance (f i) (f (i+1))=1) (hb : blank B=f 0) :
    ∃ C : Board n, ∃ path : Path B C, path.length=k ∧ blank C=f k ∧
      ∀ y, (∀ i, i≤k → f i≠y) → C y=B y := by
  have chain : Chained (Seg.mk f (k+1)) := Seg.chained_mk (fun i hi => adj i (by omega))
  rw [Seg.mk_succ] at chain
  obtain ⟨C,path,len,blankC,fix,_⟩ := route B (f 0) _ chain hb
  refine ⟨C,path,by rw [len,Seg.length_mk],?_,?_⟩
  · rw [blankC,List.getLast_eq_getElem]
    cases k <;> simp [Seg.mk]
  · intro y hy
    apply fix
    rw [← Seg.mk_succ,Seg.mem_mk]
    rintro ⟨i,hi,e⟩
    exact hy i (by omega) e

/-! ### Frames -/

omit [NeZero n] in
/-- A rectangle of local coordinates `[0,R)×[0,C)` in the board, with
distances preserved. -/
structure Frame (n : Nat) where
  R : Nat
  C : Nat
  loc : Nat → Nat → Cell n
  inj : ∀ {r c r' c' : Nat}, r<R → c<C → r'<R → c'<C → loc r c=loc r' c' → r=r' ∧ c=c'
  dist : ∀ {r c r' c' : Nat}, r<R → c<C → r'<R → c'<C →
    gridDistance (loc r c) (loc r' c')=Nat.dist r r'+Nat.dist c c'

/-- A placed square as a frame. -/
def _root_.SlidingPuzzle.NestedRouting.Placement.toFrame {s : Nat} [NeZero s] (q : Placement s n) :
    Frame n :=
  ⟨s,s,q.loc,fun hr hc hr' hc' e => q.loc_inj hr hc hr' hc' e,fun hr hc hr' hc' => q.loc_dist hr hc hr' hc'⟩

/-- One axis of a sub-rectangle: forward from `x0`, or backward when `rev`. -/
def ax (rev : Bool) (x0 x : Nat) : Nat := if rev then x0-x else x0+x

theorem ax_dist {rev : Bool} {x0 x y L : Nat} (h : rev=true → L≤x0+1) (hx : x<L) (hy : y<L) :
    Nat.dist (ax rev x0 x) (ax rev x0 y)=Nat.dist x y := by
  cases rev
  · simp only [ax,Bool.false_eq_true,if_false,Nat.dist]; omega
  · have := h rfl
    simp only [ax,if_true,Nat.dist]; omega

theorem ax_lt {rev : Bool} {x0 x L s : Nat} (h : rev=true → L≤x0+1) (h' : rev=false → x0+L≤s)
    (hx : x<L) (hx0 : x0<s) : ax rev x0 x<s := by
  cases rev
  · have := h' rfl
    simp only [ax,Bool.false_eq_true,if_false]; omega
  · simp only [ax,if_true]; omega

/-- The rectangle of `R` rows and `C` columns of a placed square starting at
local `(r0,c0)`, going up (`dr`) or down, left (`dc`) or right. -/
def _root_.SlidingPuzzle.NestedRouting.Placement.rect {s : Nat} [NeZero s] (q : Placement s n)
    (r0 c0 R C : Nat) (dr dc : Bool) (hr0 : r0<s) (hc0 : c0<s)
    (hR : dr=true → R≤r0+1) (hR' : dr=false → r0+R≤s)
    (hC : dc=true → C≤c0+1) (hC' : dc=false → c0+C≤s) : Frame n where
  R := R
  C := C
  loc r c := q.loc (ax dr r0 r) (ax dc c0 c)
  inj := by
    intro r c r' c' hr hc hr' hc' e
    have := q.loc_inj (ax_lt hR hR' hr hr0) (ax_lt hC hC' hc hc0) (ax_lt hR hR' hr' hr0)
      (ax_lt hC hC' hc' hc0) e
    have d1 := ax_dist (x0:=r0) hR hr hr'
    have d2 := ax_dist (x0:=c0) hC hc hc'
    rw [this.1,this.2] at *
    simp [Nat.dist] at d1 d2
    omega
  dist := by
    intro r c r' c' hr hc hr' hc'
    rw [q.loc_dist (ax_lt hR hR' hr hr0) (ax_lt hC hC' hc hc0) (ax_lt hR hR' hr' hr0)
      (ax_lt hC hC' hc' hc0),ax_dist hR hr hr',ax_dist hC hc hc']

omit [NeZero n] in
theorem _root_.SlidingPuzzle.NestedRouting.Placement.rect_loc {s : Nat} [NeZero s] (q : Placement s n)
    {r0 c0 R C : Nat} {dr dc : Bool} {hr0 hc0 hR hR' hC hC'} (r c : Nat) :
    (q.rect r0 c0 R C dr dc hr0 hc0 hR hR' hC hC').loc r c=q.loc (ax dr r0 r) (ax dc c0 c) := rfl

variable (F : Frame n)

omit [NeZero n] in
theorem ne_loc {r c r' c' : Nat} (hr : r<F.R) (hc : c<F.C) (hr' : r'<F.R) (hc' : c'<F.C)
    (h : r≠r' ∨ c≠c') : F.loc r c≠F.loc r' c' := fun e => by
  have := F.inj hr hc hr' hc' e
  omega

omit [NeZero n] in
theorem adj_loc {r c r' c' : Nat} (hr : r<F.R) (hc : c<F.C) (hr' : r'<F.R) (hc' : c'<F.C)
    (h : Nat.dist r r'+Nat.dist c c'=1) : gridDistance (F.loc r c) (F.loc r' c')=1 := by
  rw [F.dist hr hc hr' hc']
  exact h

/-- Every cell has local coordinates in a full-board frame. -/
theorem exists_loc (F : Placement n n) (y : Cell n) : ∃ r c, r<n ∧ c<n ∧ F.loc r c=y := by
  have h0 : F.row=0 := by have := F.row_fits; omega
  have h1 : F.col=0 := by have := F.col_fits; omega
  have inv (fl : Bool) (x : Nat) (hx : x<n) : axis n 0 fl (axis n 0 fl x)=x := by
    cases fl <;> simp only [axis,Bool.false_eq_true,if_false,if_true] <;> omega
  have lt (fl : Bool) (x : Nat) (hx : x<n) : axis n 0 fl x<n := by
    cases fl <;> simp only [axis,Bool.false_eq_true,if_false,if_true] <;> omega
  refine ⟨axis n 0 F.flipRow y.1.val,axis n 0 F.flipCol y.2.val,lt _ _ y.1.isLt,lt _ _ y.2.isLt,?_⟩
  rw [F.loc_eq (lt _ _ y.1.isLt) (lt _ _ y.2.isLt)]
  ext
  · simp only [embed_row,h0]; exact inv _ _ y.1.isLt
  · simp only [embed_col,h1]; exact inv _ _ y.2.isLt

/-- Side goals: adjacency of explicit local cells. -/
macro "adj_tac" : tactic =>
  `(tactic| (apply Routes.adj_loc <;> first | omega | (unfold Nat.dist; omega)))

/-- Side goals: an explicit local cell is not in an explicit list. -/
macro "notmem_tac" : tactic =>
  `(tactic| (simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] <;> and_intros <;> exact Routes.ne_loc _ (by omega) (by omega) (by omega) (by omega) (by omega)))

/-- Side goals: a chain of explicit local cells. -/
macro "chain_tac" : tactic =>
  `(tactic| (simp only [Chained,List.isChain_cons_cons,List.isChain_singleton,and_true] <;> and_intros <;> adj_tac))

/-- Walk the blank along row `R` from column `c0` to column `c0+k`. -/
theorem walkRow (B : Board n) (R c0 k : Nat) (hR : R<F.R) (hk : c0+k<F.C) (hb : blank B=F.loc R c0) :
    ∃ C : Board n, ∃ path : Path B C, path.length=k ∧ blank C=F.loc R (c0+k) ∧
      ∀ r c, r<F.R → c<F.C → (r≠R ∨ c<c0 ∨ c0+k<c) → C (F.loc r c)=B (F.loc r c) := by
  obtain ⟨C,path,len,blankC,fix⟩ := seg B (fun i => F.loc R (c0+i)) k
    (fun i hi => adj_loc F hR (by omega) hR (by omega) (by unfold Nat.dist; omega)) (by simpa using hb)
  exact ⟨C,path,len,blankC,fun r c hr hc h => fix _ (fun i hi => ne_loc F hR (by omega) hr hc (by omega))⟩

/-- Walk the blank down column `C0` from row `r0` to row `r0+k`. -/
theorem walkCol (B : Board n) (C0 r0 k : Nat) (hC : C0<F.C) (hk : r0+k<F.R) (hb : blank B=F.loc r0 C0) :
    ∃ C : Board n, ∃ path : Path B C, path.length=k ∧ blank C=F.loc (r0+k) C0 ∧
      ∀ r c, r<F.R → c<F.C → (c≠C0 ∨ r<r0 ∨ r0+k<r) → C (F.loc r c)=B (F.loc r c) := by
  obtain ⟨C,path,len,blankC,fix⟩ := seg B (fun i => F.loc (r0+i) C0) k
    (fun i hi => adj_loc F (by omega) hC (by omega) hC (by unfold Nat.dist; omega)) (by simpa using hb)
  exact ⟨C,path,len,blankC,fun r c hr hc h => fix _ (fun i hi => ne_loc F (by omega) hC hr hc (by omega))⟩

/-- Walk the blank along row `R` from column `c0+k` back to column `c0`. -/
theorem walkRowLeft (B : Board n) (R c0 k : Nat) (hR : R<F.R) (hk : c0+k<F.C)
    (hb : blank B=F.loc R (c0+k)) :
    ∃ C : Board n, ∃ path : Path B C, path.length=k ∧ blank C=F.loc R c0 ∧
      ∀ r c, r<F.R → c<F.C → (r≠R ∨ c<c0 ∨ c0+k<c) → C (F.loc r c)=B (F.loc r c) := by
  obtain ⟨C,path,len,blankC,fix⟩ := seg B (fun i => F.loc R (c0+k-i)) k
    (fun i hi => adj_loc F hR (by omega) hR (by omega) (by unfold Nat.dist; omega)) (by simpa using hb)
  refine ⟨C,path,len,by rw [blankC]; congr 1; omega,
    fun r c hr hc h => fix _ (fun i hi => ne_loc F hR (by omega) hr hc (by omega))⟩

/-- Walk the blank up column `C0` from row `r0+k` to row `r0`. -/
theorem walkColUp (B : Board n) (C0 r0 k : Nat) (hC : C0<F.C) (hk : r0+k<F.R)
    (hb : blank B=F.loc (r0+k) C0) :
    ∃ C : Board n, ∃ path : Path B C, path.length=k ∧ blank C=F.loc r0 C0 ∧
      ∀ r c, r<F.R → c<F.C → (c≠C0 ∨ r<r0 ∨ r0+k<r) → C (F.loc r c)=B (F.loc r c) := by
  obtain ⟨C,path,len,blankC,fix⟩ := seg B (fun i => F.loc (r0+k-i) C0) k
    (fun i hi => adj_loc F (by omega) hC (by omega) hC (by unfold Nat.dist; omega)) (by simpa using hb)
  refine ⟨C,path,len,by rw [blankC]; congr 1; omega,
    fun r c hr hc h => fix _ (fun i hi => ne_loc F (by omega) hC hr hc (by omega))⟩

/-- The whole board, reflected so that the chosen corner is local `(0,0)`. -/
def frame (n : Nat) (fr fc : Bool) : Placement n n := ⟨0,0,fr,fc,by omega,by omega⟩

/-- In the unreflected frame, local coordinates are the cell's own. -/
theorem loc_id (x : Cell n) : (frame n false false).loc x.1.val x.2.val=x := by
  rw [(frame n false false).loc_eq x.1.isLt x.2.isLt]
  ext <;> simp [frame,axis]

/-- Walk the blank along column `C0` from row `r0` to row `r1`. -/
theorem walkColTo (B : Board n) (C0 r0 r1 : Nat) (hC : C0<F.C) (h0 : r0<F.R) (h1 : r1<F.R)
    (hb : blank B=F.loc r0 C0) :
    ∃ C : Board n, ∃ path : Path B C, path.length≤F.R ∧ blank C=F.loc r1 C0 ∧
      ∀ r c, r<F.R → c<F.C → c≠C0 → C (F.loc r c)=B (F.loc r c) := by
  rcases Nat.le_total r0 r1 with h | h
  · obtain ⟨C,p,l,b,f⟩ := walkCol F B C0 r0 (r1-r0) hC (by omega) hb
    exact ⟨C,p,by omega,by rw [b]; congr 1; omega,fun r c hr hc e => f r c hr hc (Or.inl e)⟩
  · obtain ⟨C,p,l,b,f⟩ := walkColUp F B C0 r1 (r0-r1) hC (by omega) (by rw [hb]; congr 1; omega)
    exact ⟨C,p,by omega,b,fun r c hr hc e => f r c hr hc (Or.inl e)⟩

/-- Walk the blank along row `R` from column `c0` to column `c1`. -/
theorem walkRowTo (B : Board n) (R c0 c1 : Nat) (hR : R<F.R) (h0 : c0<F.C) (h1 : c1<F.C)
    (hb : blank B=F.loc R c0) :
    ∃ C : Board n, ∃ path : Path B C, path.length≤F.C ∧ blank C=F.loc R c1 ∧
      ∀ r c, r<F.R → c<F.C → r≠R → C (F.loc r c)=B (F.loc r c) := by
  rcases Nat.le_total c0 c1 with h | h
  · obtain ⟨C,p,l,b,f⟩ := walkRow F B R c0 (c1-c0) hR (by omega) hb
    exact ⟨C,p,by omega,by rw [b]; congr 1; omega,fun r c hr hc e => f r c hr hc (Or.inl e)⟩
  · obtain ⟨C,p,l,b,f⟩ := walkRowLeft F B R c1 (c0-c1) hR (by omega) (by rw [hb]; congr 1; omega)
    exact ⟨C,p,by omega,b,fun r c hr hc e => f r c hr hc (Or.inl e)⟩

end SlidingPuzzle.NestedRouting.Routes

namespace SlidingPuzzle
open NestedRouting NestedRouting.Routes

/-- Walk the blank to any cell, first along its column, then along the target
row. Cells off the initial column and the final row are fixed. -/
theorem exists_blank_access_path_elbow {n : Nat} [NeZero n] (B : Board n) (c : Cell n) :
    ∃ C : Board n, ∃ p : Path B C,
      blank C=c ∧ p.length≤2*n ∧
      ∀ x : Cell n, x.2≠(blank B).2 → x.1≠c.1 → C x=B x := by
  set F := (frame n false false).toFrame
  set a := blank B
  obtain ⟨C1,p1,l1,b1,f1⟩ := walkColTo F B a.2.val a.1.val c.1.val a.2.isLt a.1.isLt c.1.isLt
    (loc_id a).symm
  obtain ⟨C,p2,l2,b2,f2⟩ := walkRowTo F C1 c.1.val a.2.val c.2.val c.1.isLt a.2.isLt c.2.isLt b1
  have lid (x : Cell n) : F.loc x.1.val x.2.val=x := loc_id x
  have FR : F.R=n := rfl
  have FC : F.C=n := rfl
  refine ⟨C,p1.append p2,by rw [b2]; exact lid c,by simp; omega,fun x hcol hrow => ?_⟩
  have := (f2 _ _ x.1.isLt x.2.isLt (fun e => hrow (Fin.ext e))).trans
    (f1 _ _ x.1.isLt x.2.isLt (fun e => hcol (Fin.ext e)))
  rwa [lid x] at this

end SlidingPuzzle
