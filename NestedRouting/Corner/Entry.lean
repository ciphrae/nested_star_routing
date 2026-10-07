import NestedRouting.Moves.TSort

/-! Frames at the entry of a node: a placed square of side `T`, entered at
`(2cs,0)` with the blank at `(2cs+1,0)`, cells in the rows `≥ W`. Every frame
runs down from row `2cs` and right from column 0, so its block is
`p = (2cs,0)`, `q = (2cs,1)`, `s = (2cs+1,0)`, `z = (2cs+1,1)`.

The direct exchange `(e x y)` of the entry with a cell `x` of the body and a
parking cell `y` on row `W` is `t_x⁺` in the frame of the whole square,
conjugated by `t_y⁻` in a frame of `6` columns reaching row `W`. -/
namespace SlidingPuzzle.NestedRouting.Corner.Entry
open Routes

variable {n : Nat} [NeZero n] {T : Nat} [NeZero T] (q : Placement T n)

/-- Where a node fits: the entry pair in the band, the body below it. -/
structure Fit (T W cs : Nat) : Prop where
  band : 2*cs+1<W
  room : W<T
  six : 6≤T

/-- The rectangle of `R` rows and `C` columns at the entry. -/
def frame (cs R C : Nat) (h0 : 2*cs<T) (hR : 2*cs+R≤T) (hC : C≤T) : Frame n :=
  q.rect (2*cs) 0 R C false false h0 (NeZero.pos T) (by simp) (fun _ => hR) (by simp) (fun _ => by omega)

omit [NeZero n] in
theorem frame_loc {cs R C : Nat} {h0 hR hC} (r c : Nat) :
    (frame q cs R C h0 hR hC).loc r c=q.loc (2*cs+r) c := by
  simp [frame,Placement.rect_loc,ax]

variable {W cs : Nat} (h : Fit T W cs)

/-- The parking frame reaches row `W`. -/
def gFrame : Frame n :=
  frame q cs (W+1-2*cs) 6 (by have := h.band; have := h.room; omega) (by have := h.band; have := h.room; omega)
    h.six
/-- The direct frame reaches every cell of the body. -/
def dFrame : Frame n :=
  frame q cs (T-2*cs) T (by have := h.band; have := h.room; omega) (by have := h.band; have := h.room; omega)
    le_rfl

/-- The length bound of a direct exchange. -/
def dcost : Nat := 2*(Cycle3.tcost (gFrame q h)+2)+(Cycle3.tcost (dFrame q h)+2)

omit [NeZero n] in
theorem dcost_le : dcost q h≤16*T+24*W+170 := by
  change 2*(2*(2*((W+1-2*cs)+6)+4*max (W+1-2*cs) 6)+4+2)+(2*(2*((T-2*cs)+T)+4*max (T-2*cs) T)+4+2)≤_
  omega

omit [NeZero n] in
theorem dtcost_le : Cycle3.tcost (dFrame q h)≤16*T+4 := by
  change 2*(2*((T-2*cs)+T)+4*max (T-2*cs) T)+4≤_
  omega

/-- The direct exchange: a three-cycle `(e x y)`. -/
theorem direct_exchange (B : Board n) (hB : blank B=q.loc (2*cs+1) 0) {r c : Nat} (hr : W≤r) (hrT : r<T)
    (hc : c<T) {c' : Nat} (hc' : c'<2) (xy : q.loc r c≠q.loc W c') :
    ∃ C : Board n, ∃ path : Path B C, path.length≤dcost q h ∧ blank C=q.loc (2*cs+1) 0 ∧
      Cycle3.IsCycle B C (q.loc (2*cs) 0) (q.loc r c) (q.loc W c') := by
  have := h.band; have := h.room; have := h.six
  have eF (i j : Nat) : (dFrame q h).loc i j=q.loc (2*cs+i) j := by rw [dFrame,frame_loc]
  have eG (i j : Nat) : (gFrame q h).loc i j=q.loc (2*cs+i) j := by rw [gFrame,frame_loc]
  have ex : (dFrame q h).loc (r-2*cs) c=q.loc r c := by rw [eF]; congr 1; omega
  have ey : (gFrame q h).loc (W-2*cs) c'=q.loc W c' := by rw [eG]; congr 1; omega
  obtain ⟨C,path,len,bC,cyc⟩ := Cycle3.tdirect (dFrame q h) (gFrame q h)
    (by change 3≤T-2*cs; omega) (by change 6≤T; omega)
    (by change 3≤W+1-2*cs; omega) (by change 6≤6; omega)
    (fun i j _ _ => by rw [eF,eG]) B (by rw [eF]; exact hB) (r-2*cs) c
    (by change _<T-2*cs; omega) hc (Or.inl (by omega)) (W-2*cs) c'
    (by change _<W+1-2*cs; omega) (by change _<6; omega) (Or.inl (by omega)) (by rw [ex,ey]; exact xy)
  rw [ex,ey,eF] at cyc
  exact ⟨C,path,len,by rw [bC,eF],cyc⟩

/-- The cost of a direct exchange with the cell at local `(r,c)`. -/
def dw (r c : Nat) : Nat := 2*(Cycle3.tcost (gFrame q h)+2)+(Cycle3.tw (r-2*cs) c+2)

omit [NeZero n] in
theorem dw_le {r c : Nat} (hr : r<T) (hc : c<T) : dw q h r c≤dcost q h := by
  unfold dw dcost
  have := Cycle3.tw_le (dFrame q h) (r:=r-2*cs) (c:=c) (by change _<T-2*cs; have := h.band; have := h.room; omega)
    (by change _<T; omega)
  omega

/-- The direct exchange, charged by the position of `x`. -/
theorem direct_exchange_at (B : Board n) (hB : blank B=q.loc (2*cs+1) 0) {r c : Nat} (hr : W≤r) (hrT : r<T)
    (hc : c<T) {c' : Nat} (hc' : c'<2) (xy : q.loc r c≠q.loc W c') :
    ∃ C : Board n, ∃ path : Path B C, path.length≤dw q h r c ∧ blank C=q.loc (2*cs+1) 0 ∧
      Cycle3.IsCycle B C (q.loc (2*cs) 0) (q.loc r c) (q.loc W c') := by
  have := h.band; have := h.room; have := h.six
  have eF (i j : Nat) : (dFrame q h).loc i j=q.loc (2*cs+i) j := by rw [dFrame,frame_loc]
  have eG (i j : Nat) : (gFrame q h).loc i j=q.loc (2*cs+i) j := by rw [gFrame,frame_loc]
  have ex : (dFrame q h).loc (r-2*cs) c=q.loc r c := by rw [eF]; congr 1; omega
  have ey : (gFrame q h).loc (W-2*cs) c'=q.loc W c' := by rw [eG]; congr 1; omega
  obtain ⟨C,path,len,bC,cyc⟩ := Cycle3.tdirect_at (dFrame q h) (gFrame q h)
    (by change 3≤T-2*cs; omega) (by change 6≤T; omega)
    (by change 3≤W+1-2*cs; omega) (by change 6≤6; omega)
    (fun i j _ _ => by rw [eF,eG]) B (by rw [eF]; exact hB) (r-2*cs) c
    (by change _<T-2*cs; omega) hc (Or.inl (by omega)) (W-2*cs) c'
    (by change _<W+1-2*cs; omega) (by change _<6; omega) (Or.inl (by omega)) (by rw [ex,ey]; exact xy)
  rw [ex,ey,eF] at cyc
  exact ⟨C,path,len,by rw [bC,eF],cyc⟩

omit [NeZero n] in
/-- Charging by position saves at least `16T - 12(r+c) - 12` on a cell at `(r,c)`. -/
theorem dw_gain {r c : Nat} (hr : 2*cs≤r) (hrT : r<T) : dw q h r c+16*T≤dcost q h+12*r+12*c+12 := by
  have := h.band; have := h.room
  unfold dw dcost
  change _+(2*(2*((r-2*cs)+c)+4*max (r-2*cs) c+6)+4+2)+16*T≤
    _+(2*(2*((T-2*cs)+T)+4*max (T-2*cs) T)+4+2)+12*r+12*c+12
  have m1 : max (r-2*cs) c≤(r-2*cs)+c := max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  have m2 : max (T-2*cs) T=T := max_eq_right (Nat.sub_le _ _)
  rw [m2]
  omega

omit [NeZero n] in
/-- The constant part of `dw`: `2(tcost G + 2) + 2 ≤ 24W + 166`. -/
theorem dw_const : 2*(Cycle3.tcost (gFrame q h)+2)+2≤24*W+166 := by
  change 2*(2*(2*((W+1-2*cs)+6)+4*max (W+1-2*cs) 6)+4+2)+2≤_
  omega

include h in
/-- The final sort of body cells, by `t`-cycles in the direct frame. The sort
costs three halves of the `t`-cycle weights, so it is charged twice a weight
`wt` with `4·wt` at least three times the `t`-cycle at each cell. -/
theorem finish (B G : Board n) (hB : blank B=q.loc (2*cs+1) 0) (R F : Finset (Cell n))
    (hR : ∀ x∈R, ∃ r c, W≤r ∧ r<T ∧ c<T ∧ q.loc r c=x) (wt : Cell n → Nat)
    (hwt : ∀ r c, W≤r → r<T → c<T → 3*(Cycle3.tw (r-2*cs) c+2)≤4*wt (q.loc r c))
    (inside : F⊆R) (hnonzero : ∀ x∈F, G x≠0)
    (hpresent : ∀ x∈F, ∃ y∈R, B y=G x) (room : F.card+3≤R.card) :
    ∃ C : Board n, ∃ path : Path B C, path.length≤2*∑ x∈R, wt x ∧
      blank C=blank B ∧ (∀ x, x∉R → C x=B x) ∧ ∀ x∈F, C x=G x := by
  have := h.band; have := h.room; have := h.six
  have eF (i j : Nat) : (dFrame q h).loc i j=q.loc (2*cs+i) j := by rw [dFrame,frame_loc]
  obtain ⟨C,path,len,rest⟩ := Cycle3.exists_tfinish (dFrame q h) (by change 3≤T-2*cs; omega)
    (by change 6≤T; omega) B G (by rw [eF]; exact hB) R F
    (by
      intro x hx
      obtain ⟨r,c,hr,hrT,hc,rfl⟩ := hR x hx
      exact ⟨r-2*cs,c,by change _<T-2*cs; omega,hc,Or.inl (by omega),by rw [eF]; congr 1; omega⟩)
    (fun x => 4*wt x/3)
    (by
      intro x hx r' c' hr' hc' e
      obtain ⟨r,c,hr,hrT,hc,rfl⟩ := hR x hx
      rw [eF] at e
      change r'<T-2*cs at hr'
      obtain ⟨e1,rfl⟩ := q.loc_inj (by omega) hc' hrT hc e
      have hw' := hwt r c' hr hrT hc
      rw [show r'=r-2*cs by omega]
      omega)
    inside hnonzero hpresent room
  refine ⟨C,path,?_,rest⟩
  have : 3*∑ x∈R, 4*wt x/3≤4*∑ x∈R, wt x := by
    rw [Finset.mul_sum,Finset.mul_sum]
    exact Finset.sum_le_sum (fun x _ => by omega)
  omega

end SlidingPuzzle.NestedRouting.Corner.Entry
