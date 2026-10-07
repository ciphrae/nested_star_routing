import NestedRouting.Geometry.Placement
import NestedRouting.Moves.Walk

/-! Local coordinates inside a placed square, sub-squares, and straight
segments of cells as lists. -/
namespace SlidingPuzzle.NestedRouting

namespace Placement
variable {s n : Nat}

/-- The sub-square of side `t` at local offset `(r0, c0)`, with the same flips. -/
def sub (q : Placement s n) (r0 c0 t : Nat) (hr : r0+t≤s) (hc : c0+t≤s) : Placement t n where
  row := if q.flipRow then q.row+(s-r0-t) else q.row+r0
  col := if q.flipCol then q.col+(s-c0-t) else q.col+c0
  flipRow := q.flipRow
  flipCol := q.flipCol
  row_fits := by have := q.row_fits; split_ifs <;> omega
  col_fits := by have := q.col_fits; split_ifs <;> omega

theorem axis_sub (s t base off : Nat) (flip : Bool) (x : Nat) (hx : x<t) (h : off+t≤s) :
    axis t (if flip then base+(s-off-t) else base+off) flip x=axis s base flip (off+x) := by
  cases flip <;> simp only [axis,Bool.false_eq_true,if_false,if_true] <;> omega

theorem sub_embed (q : Placement s n) (r0 c0 t : Nat) (hr : r0+t≤s) (hc : c0+t≤s) (x : Cell t) :
    (q.sub r0 c0 t hr hc).embed x=q.embed (⟨r0+x.1.val,by omega⟩,⟨c0+x.2.val,by omega⟩) := by
  ext
  · exact axis_sub s t q.row r0 q.flipRow x.1.val x.1.isLt hr
  · exact axis_sub s t q.col c0 q.flipCol x.2.val x.2.isLt hc

/-- A total local-coordinate map; exact for coordinates below the side. -/
def loc (q : Placement s n) [NeZero s] (r c : Nat) : Cell n :=
  q.embed (⟨r%s,Nat.mod_lt _ (NeZero.pos s)⟩,⟨c%s,Nat.mod_lt _ (NeZero.pos s)⟩)

variable (q : Placement s n) [NeZero s]

theorem loc_eq {r c : Nat} (hr : r<s) (hc : c<s) : q.loc r c=q.embed (⟨r,hr⟩,⟨c,hc⟩) := by
  simp [loc,Nat.mod_eq_of_lt hr,Nat.mod_eq_of_lt hc]

theorem loc_inj {r c r' c' : Nat} (hr : r<s) (hc : c<s) (hr' : r'<s) (hc' : c'<s)
    (h : q.loc r c=q.loc r' c') : r=r' ∧ c=c' := by
  rw [q.loc_eq hr hc,q.loc_eq hr' hc'] at h
  have := q.embed.injective h
  simp only [Prod.mk.injEq,Fin.mk.injEq] at this
  exact this

theorem loc_dist {r c r' c' : Nat} (hr : r<s) (hc : c<s) (hr' : r'<s) (hc' : c'<s) :
    gridDistance (q.loc r c) (q.loc r' c')=Nat.dist r r'+Nat.dist c c' := by
  rw [q.loc_eq hr hc,q.loc_eq hr' hc',q.distance]
  rfl

theorem loc_adj_h {r c : Nat} (hr : r<s) (hc : c+1<s) : gridDistance (q.loc r c) (q.loc r (c+1))=1 := by
  rw [q.loc_dist hr (by omega) hr hc]
  simp [Nat.dist]

theorem loc_adj_v {r c : Nat} (hr : r+1<s) (hc : c<s) : gridDistance (q.loc r c) (q.loc (r+1) c)=1 := by
  rw [q.loc_dist (by omega) hc hr hc]
  simp [Nat.dist]

theorem loc_sub {r0 c0 t : Nat} [NeZero t] (hr : r0+t≤s) (hc : c0+t≤s) {r c : Nat} (hr' : r<t) (hc' : c<t) :
    (q.sub r0 c0 t hr hc).loc r c=q.loc (r0+r) (c0+c) := by
  rw [(q.sub r0 c0 t hr hc).loc_eq hr' hc',sub_embed,q.loc_eq (by omega) (by omega)]

end Placement

namespace Seg
variable {n : Nat}

/-- Cells `f 0, …, f (len-1)`. -/
def mk (f : Nat → Cell n) (len : Nat) : List (Cell n) := (List.range len).map f

theorem mem_mk {f : Nat → Cell n} {len : Nat} {x : Cell n} : x∈mk f len ↔ ∃ i<len, f i=x := by
  simp [mk]

theorem length_mk (f : Nat → Cell n) (len : Nat) : (mk f len).length=len := by simp [mk]

theorem nodup_mk {f : Nat → Cell n} {len : Nat} (inj : ∀ i<len, ∀ j<len, f i=f j → i=j) :
    (mk f len).Nodup := by
  unfold mk
  rw [List.nodup_map_iff_inj_on List.nodup_range]
  intro i hi j hj e
  exact inj i (List.mem_range.mp hi) j (List.mem_range.mp hj) e

theorem mk_succ (f : Nat → Cell n) (len : Nat) : mk f (len+1)=f 0 :: mk (fun i => f (i+1)) len := by
  simp [mk,List.range_succ_eq_map,List.map_map,Function.comp_def]

/-- A segment is chained when consecutive cells are adjacent. -/
theorem chained_mk {f : Nat → Cell n} {len : Nat} (adj : ∀ i, i+1<len → gridDistance (f i) (f (i+1))=1) :
    Chained (mk f len) := by
  induction len generalizing f with
  | zero => exact List.isChain_nil
  | succ len ih =>
    rw [mk_succ]
    cases len with
    | zero => simp [mk]; exact List.isChain_singleton _
    | succ len =>
      rw [mk_succ]
      apply List.isChain_cons_cons.mpr
      refine ⟨adj 0 (by omega),?_⟩
      have := ih (f:=fun i => f (i+1)) (fun i hi => adj (i+1) (by omega))
      rwa [mk_succ] at this

theorem chained_append {l₁ l₂ : List (Cell n)} (h₁ : Chained l₁) (h₂ : Chained l₂)
    (link : ∀ a b, l₁.getLast? = some a → l₂.head? = some b → gridDistance a b=1) :
    Chained (l₁++l₂) := by
  unfold Chained at *
  exact List.IsChain.append h₁ h₂ (fun a ha b hb => link a b ha hb)

end Seg
end SlidingPuzzle.NestedRouting
