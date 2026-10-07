import NestedRouting.Geometry.Grid
import NestedRouting.Star.Layout

/-! The corner-rooted layout of a star node, in the local coordinates of its
slot (a placed square of side `T`; local `(0,0)` is the corner nearest the
root hub).

* rows `[0,W)`: the band, territory of the parent; the entry is `(2cs,0)`,
  blank cell `(2cs+1,0)`;
* rows `W..W+3`: the hub; the park cell `w = (W,2)` and the carrier
  `K = (W+1,1)` next to the entry column, `u v u2` at row `W+1` from column
  `M0+2`, markers beyond them; access walks run right along row `W` from `w`
  and down the spoke's column to row `W+2`;
* child slot `(r,c)` (index `j = r b + c`) at rows `W+4+r T'`, columns
  `M0+c T'`, side `T'`; its own band is its top `W` rows;
* spoke `j`: two nested L's, down margin columns `a_j, a_j+1` with
  `a_j = M0-2(j+1)`, then right along band rows `y_j+1, y_j` of its slot row,
  `y_j = W+4+r T'+2c`, to the child's corner column `f_j = M0+c T'`. -/
namespace SlidingPuzzle.NestedRouting.Corner

structure Params where
  b : Nat
  T : Nat
  T' : Nat
  cs : Nat
  b_pos : 1≤b
  rows_fit : (2*b)+4+b*T'≤T
  cols_fit : (2*(b*b)+4)+b*T'≤T
  hub_fit : (2*b)+(2*(b*b)+4)+11≤T
  band_fit : 2*b+3≤T'
  strip_fit : 2*cs+1<2*b

namespace Params
variable (p : Params)

def W : Nat := 2*p.b
def J : Nat := p.b*p.b
def M0 : Nat := 2*p.J+4
def rowOf (j : Nat) : Nat := j/p.b
def colOf (j : Nat) : Nat := j%p.b
/-- Top row of child slot row `r`. -/
def R (r : Nat) : Nat := p.W+4+r*p.T'
/-- Left column of child slot column `c`. -/
def C (c : Nat) : Nat := p.M0+c*p.T'
def a (j : Nat) : Nat := p.M0-2*(j+1)
def y (j : Nat) : Nat := p.R (p.rowOf j)+2*p.colOf j
def f (j : Nat) : Nat := p.C (p.colOf j)

theorem colOf_lt (j : Nat) : p.colOf j<p.b := Nat.mod_lt _ p.b_pos
theorem rowOf_lt {j : Nat} (hj : j<p.J) : p.rowOf j<p.b := by
  unfold rowOf J at *; exact Nat.div_lt_of_lt_mul hj

theorem j_eq (j : Nat) : j=p.rowOf j*p.b+p.colOf j := by
  unfold rowOf colOf; rw [Nat.mul_comm]; exact (Nat.div_add_mod j p.b).symm

theorem a_lt {j : Nat} (hj : j<p.J) : p.a j+2*(j+1)=p.M0 := by
  unfold a M0; omega

/-- Band rows increase with the spoke index. -/
theorem y_strict {j j' : Nat} (_hj' : j'<p.J) (h : j<j') : p.y j+2≤p.y j' := by
  have ej := p.j_eq j
  have ej' := p.j_eq j'
  have cj := p.colOf_lt j
  have cj' := p.colOf_lt j'
  have bT := p.band_fit
  unfold y R
  rcases Nat.lt_or_ge (p.rowOf j) (p.rowOf j') with hr | hr
  · have : (p.rowOf j+1)*p.T'≤p.rowOf j'*p.T' := Nat.mul_le_mul_right _ hr
    nlinarith
  · have hr' : p.rowOf j'≤p.rowOf j := by
      by_contra hc
      push Not at hc
      have : (p.rowOf j'+1)*p.b≤p.rowOf j*p.b := Nat.mul_le_mul_right _ (by omega)
      nlinarith
    have heq : p.rowOf j=p.rowOf j' := by
      by_contra hne
      have hlt : p.rowOf j'<p.rowOf j := by omega
      have : (p.rowOf j'+1)*p.b≤p.rowOf j*p.b := Nat.mul_le_mul_right _ hlt
      nlinarith
    rw [heq] at ej ⊢
    have : p.colOf j<p.colOf j' := by omega
    omega

end Params
namespace Seg
open Placement
variable {s n : Nat} (q : Placement s n) [NeZero s]

theorem mem_down {r0 c0 len : Nat} {x : Cell n} :
    x∈Seg.mk (fun i => q.loc (r0+i) c0) len ↔ ∃ r, r0≤r ∧ r<r0+len ∧ q.loc r c0=x := by
  rw [Seg.mem_mk]
  constructor
  · rintro ⟨i,hi,rfl⟩; exact ⟨r0+i,by omega,by omega,rfl⟩
  · rintro ⟨r,h1,h2,rfl⟩; exact ⟨r-r0,by omega,by congr 1; omega⟩

theorem mem_right {r0 c0 len : Nat} {x : Cell n} :
    x∈Seg.mk (fun i => q.loc r0 (c0+i)) len ↔ ∃ c, c0≤c ∧ c<c0+len ∧ q.loc r0 c=x := by
  rw [Seg.mem_mk]
  constructor
  · rintro ⟨i,hi,rfl⟩; exact ⟨c0+i,by omega,by omega,rfl⟩
  · rintro ⟨c,h1,h2,rfl⟩; exact ⟨c-c0,by omega,by congr 1; omega⟩

theorem mem_up {r0 c0 len : Nat} (hl : len≤r0+1) {x : Cell n} :
    x∈Seg.mk (fun i => q.loc (r0-i) c0) len ↔ ∃ r, r0+1≤r+len ∧ r≤r0 ∧ q.loc r c0=x := by
  rw [Seg.mem_mk]
  constructor
  · rintro ⟨i,hi,rfl⟩; exact ⟨r0-i,by omega,by omega,rfl⟩
  · rintro ⟨r,h1,h2,rfl⟩; exact ⟨r0-r,by omega,by congr 1; omega⟩

theorem mem_left {r0 c0 len : Nat} (hl : len≤c0+1) {x : Cell n} :
    x∈Seg.mk (fun i => q.loc r0 (c0-i)) len ↔ ∃ c, c0+1≤c+len ∧ c≤c0 ∧ q.loc r0 c=x := by
  rw [Seg.mem_mk]
  constructor
  · rintro ⟨i,hi,rfl⟩; exact ⟨c0-i,by omega,by omega,rfl⟩
  · rintro ⟨c,h1,h2,rfl⟩; exact ⟨c0-c,by omega,by congr 1; omega⟩

end Seg

namespace Params
variable (p : Params) {n : Nat} (q : Placement p.T n) [NeZero p.T]
open Placement

def hubSide : Nat := p.M0+5

omit [NeZero p.T] in
theorem hub_fits : p.W+p.hubSide≤p.T := by
  unfold hubSide W M0 J; have := p.hub_fit; omega
omit [NeZero p.T] in
theorem hub_fits' : 0+p.hubSide≤p.T := by have := p.hub_fits; omega

def hub : Cell p.hubSide ↪ Cell n := (q.sub p.W 0 p.hubSide p.hub_fits p.hub_fits').embed

def hcell (r c : Nat) (hr : r<p.hubSide) (hc : c<p.hubSide) : Cell p.hubSide := (⟨r,hr⟩,⟨c,hc⟩)

def K : Cell p.hubSide := p.hcell 1 1 (by unfold hubSide; omega) (by unfold hubSide; omega)
def u : Cell p.hubSide := p.hcell 1 (p.M0+2) (by unfold hubSide; omega) (by unfold hubSide; omega)
def v : Cell p.hubSide := p.hcell 1 (p.M0+3) (by unfold hubSide; omega) (by unfold hubSide; omega)
def w : Cell p.hubSide := p.hcell 0 2 (by unfold hubSide; omega) (by unfold hubSide; omega)
def u2 : Cell p.hubSide := p.hcell 1 (p.M0+4) (by unfold hubSide; omega) (by unfold hubSide; omega)
def H (j : Fin p.J) : Cell p.hubSide :=
  p.hcell 2 (p.a j+1) (by unfold hubSide; omega) (by unfold hubSide a; omega)

theorem hub_loc (r c : Nat) (hr : r<p.hubSide) (hc : c<p.hubSide) :
    p.hub q (p.hcell r c hr hc)=q.loc (p.W+r) c := by
  have : NeZero p.hubSide := ⟨by unfold hubSide; omega⟩
  unfold hub hcell
  rw [←(q.sub p.W 0 p.hubSide p.hub_fits p.hub_fits').loc_eq hr hc,q.loc_sub p.hub_fits p.hub_fits' hr hc]
  simp

def x (j : Fin p.J) : Cell n := q.loc (p.W+2) (p.a j)
def z (j : Fin p.J) : Cell n := q.loc (p.y j+1) (p.f j)
def e (j : Fin p.J) : Cell n := q.loc (p.y j) (p.f j)

def exportLane (j : Fin p.J) : List (Cell n) :=
  Seg.mk (fun i => q.loc (p.W+3+i) (p.a j)) (p.y j-p.W-1)++
  Seg.mk (fun i => q.loc (p.y j+1) (p.a j+1+i)) (p.f j-p.a j-1)

def deliveryLane (j : Fin p.J) : List (Cell n) :=
  Seg.mk (fun i => q.loc (p.y j) (p.f j-1-i)) (p.f j-p.a j-1)++
  Seg.mk (fun i => q.loc (p.y j-1-i) (p.a j+1)) (p.y j-p.W-3)

def accessTail (j : Fin p.J) : List (Cell n) :=
  Seg.mk (fun i => q.loc p.W (3+i)) (p.a j-2)++
  Seg.mk (fun i => q.loc (p.W+1+i) (p.a j)) 2

end Params

namespace Params
variable (p : Params)

theorem R_le {r : Nat} (hr : r<p.b) : p.R r+p.T'≤p.T := by
  have := p.rows_fit
  have h : (r+1)*p.T'≤p.b*p.T' := Nat.mul_le_mul_right _ hr
  unfold R W; nlinarith

theorem C_le {c : Nat} (hc : c<p.b) : p.C c+p.T'≤p.T := by
  have := p.cols_fit
  have h : (c+1)*p.T'≤p.b*p.T' := Nat.mul_le_mul_right _ hc
  unfold C M0 J; nlinarith

structure SpokeBounds (j : Nat) : Prop where
  a_eq : p.a j+2*(j+1)=p.M0
  a_ge : 4≤p.a j
  y_ge : p.W+4≤p.y j
  y_band : p.R (p.rowOf j)≤p.y j ∧ p.y j+2≤p.R (p.rowOf j)+p.W
  f_ge : p.M0≤p.f j
  f_le : p.f j+p.T'≤p.T
  R_le : p.R (p.rowOf j)+p.T'≤p.T
  M0_le : p.M0+p.W+11≤p.T

theorem bounds {j : Nat} (hj : j<p.J) : p.SpokeBounds j := by
  have ha := p.a_lt hj
  have hr := p.rowOf_lt hj
  have hc := p.colOf_lt j
  refine ⟨ha,?_,?_,?_,?_,p.C_le hc,p.R_le hr,?_⟩
  · unfold M0 at ha; have : j<p.J := hj; unfold J at *; omega
  · unfold y R; omega
  · unfold y; unfold W; constructor <;> omega
  · unfold f C; omega
  · have := p.hub_fit; unfold M0 J W; omega

/-- Export queue cells, `z` included. -/
def expP (j r c : Nat) : Prop :=
  (c=p.a j ∧ p.W+3≤r ∧ r≤p.y j+1) ∨ (r=p.y j+1 ∧ p.a j+1≤c ∧ c≤p.f j)
/-- Delivery queue cells, `e` included. -/
def delP (j r c : Nat) : Prop :=
  (r=p.y j ∧ p.a j+1≤c ∧ c≤p.f j) ∨ (c=p.a j+1 ∧ p.W+3≤r ∧ r≤p.y j)
def loopP (j r c : Nat) : Prop :=
  (r=p.W+2 ∧ (c=p.a j ∨ c=p.a j+1)) ∨ p.expP j r c ∨ p.delP j r c
def accP (j r c : Nat) : Prop :=
  (r=p.W ∧ 2≤c ∧ c≤p.a j) ∨ (c=p.a j ∧ p.W≤r ∧ r≤p.W+2)
/-- The body of child slot `j`. -/
def bodyP (j r c : Nat) : Prop :=
  p.R (p.rowOf j)+p.W≤r ∧ r<p.R (p.rowOf j)+p.T' ∧ p.C (p.colOf j)≤c ∧ c<p.C (p.colOf j)+p.T'
/-- The band of child slot `j`. -/
def bandP (j r c : Nat) : Prop :=
  p.R (p.rowOf j)≤r ∧ r<p.R (p.rowOf j)+p.W ∧ p.C (p.colOf j)≤c ∧ c<p.C (p.colOf j)+p.T'

/-- Different child slots do not overlap. -/
theorem slot_disjoint {j j' : Nat} (_hj : j<p.J) (_hj' : j'<p.J) (h : j≠j') {r c : Nat}
    (h1 : p.R (p.rowOf j)≤r ∧ r<p.R (p.rowOf j)+p.T' ∧ p.C (p.colOf j)≤c ∧ c<p.C (p.colOf j)+p.T')
    (h2 : p.R (p.rowOf j')≤r ∧ r<p.R (p.rowOf j')+p.T' ∧ p.C (p.colOf j')≤c ∧ c<p.C (p.colOf j')+p.T') :
    False := by
  have ej := p.j_eq j
  have ej' := p.j_eq j'
  have sameRow : p.rowOf j=p.rowOf j' := by
    by_contra hne
    unfold R at h1 h2
    rcases Nat.lt_or_gt_of_ne hne with hl | hl
    · have : (p.rowOf j+1)*p.T'≤p.rowOf j'*p.T' := Nat.mul_le_mul_right _ hl
      nlinarith
    · have : (p.rowOf j'+1)*p.T'≤p.rowOf j*p.T' := Nat.mul_le_mul_right _ hl
      nlinarith
  have sameCol : p.colOf j=p.colOf j' := by
    by_contra hne
    unfold C at h1 h2
    rcases Nat.lt_or_gt_of_ne hne with hl | hl
    · have : (p.colOf j+1)*p.T'≤p.colOf j'*p.T' := Nat.mul_le_mul_right _ hl
      nlinarith
    · have : (p.colOf j'+1)*p.T'≤p.colOf j*p.T' := Nat.mul_le_mul_right _ hl
      nlinarith
  rw [sameRow,sameCol] at ej
  exact h (ej.trans ej'.symm)

end Params

namespace Params
variable (p : Params) {n : Nat} (q : Placement p.T n) [NeZero p.T]
open Placement

theorem mem_exportQ (j : Fin p.J) {x : Cell n} :
    x∈p.exportLane q j++[p.z q j] ↔ ∃ r c, p.expP j r c ∧ q.loc r c=x := by
  have hb := p.bounds j.isLt
  have ha := hb.a_eq; have hy := hb.y_ge; have hf := hb.f_ge
  simp only [exportLane,z,List.mem_append,List.mem_singleton,Seg.mem_down,Seg.mem_right,expP]
  constructor
  · rintro ((⟨r,h1,h2,rfl⟩ | ⟨c,h1,h2,rfl⟩) | rfl)
    · exact ⟨r,p.a j,Or.inl ⟨rfl,h1,by omega⟩,rfl⟩
    · exact ⟨p.y j+1,c,Or.inr ⟨rfl,h1,by omega⟩,rfl⟩
    · exact ⟨p.y j+1,p.f j,Or.inr ⟨rfl,by omega,le_rfl⟩,rfl⟩
  · rintro ⟨r,c,(⟨rfl,h1,h2⟩ | ⟨rfl,h1,h2⟩),rfl⟩
    · exact Or.inl (Or.inl ⟨r,h1,by omega,rfl⟩)
    · rcases Nat.lt_or_ge c (p.f j) with hc | hc
      · exact Or.inl (Or.inr ⟨c,h1,by omega,rfl⟩)
      · have : c=p.f j := by omega
        subst this; exact Or.inr rfl

theorem mem_deliveryQ (j : Fin p.J) {x : Cell n} :
    x∈p.e q j :: p.deliveryLane q j ↔ ∃ r c, p.delP j r c ∧ q.loc r c=x := by
  have hb := p.bounds j.isLt
  have ha := hb.a_eq; have hy := hb.y_ge; have hf := hb.f_ge
  simp only [deliveryLane,e,List.mem_cons,List.mem_append,delP]
  rw [Seg.mem_left q (by omega),Seg.mem_up q (by omega)]
  constructor
  · rintro (rfl | ⟨c,h1,h2,rfl⟩ | ⟨r,h1,h2,rfl⟩)
    · exact ⟨p.y j,p.f j,Or.inl ⟨rfl,by omega,le_rfl⟩,rfl⟩
    · exact ⟨p.y j,c,Or.inl ⟨rfl,by omega,by omega⟩,rfl⟩
    · exact ⟨r,p.a j+1,Or.inr ⟨rfl,by omega,by omega⟩,rfl⟩
  · rintro ⟨r,c,(⟨rfl,h1,h2⟩ | ⟨rfl,h1,h2⟩),rfl⟩
    · rcases Nat.lt_or_ge c (p.f j) with hc | hc
      · exact Or.inr (Or.inl ⟨c,by omega,by omega,rfl⟩)
      · have : c=p.f j := by omega
        subst this; exact Or.inl rfl
    · rcases Nat.lt_or_ge r (p.y j) with hr | hr
      · exact Or.inr (Or.inr ⟨r,by omega,by omega,rfl⟩)
      · have : r=p.y j := by omega
        subst this
        rcases Nat.lt_or_ge (p.a j+1) (p.f j) with hc | hc
        · exact Or.inr (Or.inl ⟨p.a j+1,by omega,by omega,rfl⟩)
        · omega

theorem mem_access (j : Fin p.J) {x : Cell n} :
    x∈p.hub q p.w :: p.accessTail q j ↔ ∃ r c, p.accP j r c ∧ q.loc r c=x := by
  have hb := p.bounds j.isLt
  have ha := hb.a_eq
  have hw : p.hub q p.w=q.loc p.W 2 := by unfold w; rw [hub_loc]; simp
  have ha4 := hb.a_ge
  simp only [accessTail,List.mem_cons,List.mem_append,hw,accP,Seg.mem_down,Seg.mem_right]
  constructor
  · rintro (rfl | ⟨c,h1,h2,rfl⟩ | ⟨r,h1,h2,rfl⟩)
    · exact ⟨p.W,2,Or.inl ⟨rfl,le_rfl,by omega⟩,rfl⟩
    · exact ⟨p.W,c,Or.inl ⟨rfl,by omega,by omega⟩,rfl⟩
    · exact ⟨r,p.a j,Or.inr ⟨rfl,by omega,by omega⟩,rfl⟩
  · rintro ⟨r,c,(⟨rfl,h1,h2⟩ | ⟨rfl,h1,h2⟩),rfl⟩
    · rcases Nat.lt_or_ge 2 c with hc | hc
      · exact Or.inr (Or.inl ⟨c,by omega,by omega,rfl⟩)
      · have : c=2 := by omega
        subst this; exact Or.inl rfl
    · rcases Nat.lt_or_ge p.W r with hr | hr
      · exact Or.inr (Or.inr ⟨r,by omega,by omega,rfl⟩)
      · have : r=p.W := by omega
        subst this
        exact Or.inr (Or.inl ⟨p.a j,by omega,by omega,rfl⟩)

theorem hubH (j : Fin p.J) : p.hub q (p.H j)=q.loc (p.W+2) (p.a j+1) := by
  unfold H; rw [hub_loc]

theorem mem_loop (j : Fin p.J) {x : Cell n} :
    x∈Interface.loopOf (p.x q j) (p.exportLane q j) (p.z q j) (p.e q j) (p.deliveryLane q j) (p.hub q (p.H j)) ↔
      ∃ r c, p.loopP j r c ∧ q.loc r c=x := by
  have split : Interface.loopOf (p.x q j) (p.exportLane q j) (p.z q j) (p.e q j) (p.deliveryLane q j)
      (p.hub q (p.H j))=[p.x q j]++(p.exportLane q j++[p.z q j])++(p.e q j :: p.deliveryLane q j)++
        [p.hub q (p.H j)] := by
    simp [Interface.loopOf]
  rw [split,List.mem_append,List.mem_append,List.mem_append,p.mem_exportQ,p.mem_deliveryQ,
    List.mem_singleton,List.mem_singleton,hubH]
  unfold loopP
  constructor
  · rintro (((rfl | ⟨r,c,hp,rfl⟩) | ⟨r,c,hp,rfl⟩) | rfl)
    · exact ⟨_,_,Or.inl ⟨rfl,Or.inl rfl⟩,rfl⟩
    · exact ⟨r,c,Or.inr (Or.inl hp),rfl⟩
    · exact ⟨r,c,Or.inr (Or.inr hp),rfl⟩
    · exact ⟨_,_,Or.inl ⟨rfl,Or.inr rfl⟩,rfl⟩
  · rintro ⟨r,c,(⟨rfl,rfl | rfl⟩ | hp | hp),rfl⟩
    · exact Or.inl (Or.inl (Or.inl rfl))
    · exact Or.inr rfl
    · exact Or.inl (Or.inl (Or.inr ⟨r,c,hp,rfl⟩))
    · exact Or.inl (Or.inr ⟨r,c,hp,rfl⟩)

end Params

namespace Seg
open Placement
variable {s n : Nat} (q : Placement s n) [NeZero s]

theorem gd_comm (x y : Cell n) : gridDistance x y=gridDistance y x := by
  unfold gridDistance; rw [Nat.dist_comm,Nat.dist_comm x.2.val]

theorem chained_down {r0 c len : Nat} (hr : r0+len≤s) (hc : c<s) :
    Chained (Seg.mk (fun i => q.loc (r0+i) c) len) :=
  Seg.chained_mk (fun i hi => by rw [show r0+(i+1)=(r0+i)+1 by omega]; exact q.loc_adj_v (by omega) hc)

theorem chained_right {r c0 len : Nat} (hr : r<s) (hc : c0+len≤s) :
    Chained (Seg.mk (fun i => q.loc r (c0+i)) len) :=
  Seg.chained_mk (fun i hi => by rw [show c0+(i+1)=(c0+i)+1 by omega]; exact q.loc_adj_h hr (by omega))

theorem chained_up {r0 c len : Nat} (hr : r0<s) (hl : len≤r0+1) (hc : c<s) :
    Chained (Seg.mk (fun i => q.loc (r0-i) c) len) :=
  Seg.chained_mk (fun i hi => by
    rw [gd_comm,show r0-i=(r0-(i+1))+1 by omega]; exact q.loc_adj_v (by omega) hc)

theorem chained_left {r c0 len : Nat} (hr : r<s) (hc : c0<s) (hl : len≤c0+1) :
    Chained (Seg.mk (fun i => q.loc r (c0-i)) len) :=
  Seg.chained_mk (fun i hi => by
    rw [gd_comm,show c0-i=(c0-(i+1))+1 by omega]; exact q.loc_adj_h hr (by omega))

theorem head?_mk (f : Nat → Cell n) (len : Nat) (h : 0<len) : (Seg.mk f len).head?=some (f 0) := by
  obtain ⟨l,rfl⟩ : ∃ l, len=l+1 := ⟨len-1,by omega⟩
  simp [Seg.mk_succ]

theorem getLast?_mk (f : Nat → Cell n) (len : Nat) (h : 0<len) :
    (Seg.mk f len).getLast?=some (f (len-1)) := by
  obtain ⟨l,rfl⟩ : ∃ l, len=l+1 := ⟨len-1,by omega⟩
  simp [Seg.mk,List.range_succ]

end Seg

namespace Params
variable (p : Params)

theorem loopP_lt {j r c : Nat} (hj : j<p.J) (h : p.loopP j r c) : r<p.T ∧ c<p.T := by
  have hb := p.bounds hj
  have := hb.a_eq; have := hb.y_band; have := hb.f_le; have := hb.R_le; have := hb.M0_le
  have hW : p.W<p.T' := by unfold W; have := p.band_fit; omega
  unfold loopP expP delP at h
  rcases h with ⟨rfl,rfl | rfl⟩ | (⟨rfl,_,_⟩ | ⟨rfl,_,_⟩) | (⟨rfl,_,_⟩ | ⟨rfl,_,_⟩) <;> omega

theorem accP_lt {j r c : Nat} (hj : j<p.J) (h : p.accP j r c) : r<p.T ∧ c<p.T := by
  have hb := p.bounds hj
  have := hb.a_eq; have := hb.M0_le
  unfold accP at h
  rcases h with ⟨rfl,_,_⟩ | ⟨rfl,_,_⟩ <;> omega

theorem bodyP_lt {j r c : Nat} (hj : j<p.J) (h : p.bodyP j r c) : r<p.T ∧ c<p.T := by
  have hb := p.bounds hj
  have := hb.f_le; have := hb.R_le
  unfold bodyP at h; unfold f at *; omega

end Params

namespace Params
variable (p : Params)

theorem slotRow_eq {r1 r2 x : Nat} (h1 : p.R r1≤x ∧ x<p.R r1+p.T') (h2 : p.R r2≤x ∧ x<p.R r2+p.T') :
    r1=r2 := by
  by_contra hne
  unfold R at h1 h2
  rcases Nat.lt_or_gt_of_ne hne with hl | hl
  · have : (r1+1)*p.T'≤r2*p.T' := Nat.mul_le_mul_right _ hl
    nlinarith
  · have : (r2+1)*p.T'≤r1*p.T' := Nat.mul_le_mul_right _ hl
    nlinarith

/-- Lanes of different spokes do not meet. -/
theorem loopP_disjoint {j j' r c : Nat} (hj : j<p.J) (hj' : j'<p.J) (h : j<j')
    (h1 : p.loopP j r c) (h2 : p.loopP j' r c) : False := by
  have b1 := p.bounds hj
  have b2 := p.bounds hj'
  have hy := p.y_strict hj' h
  have a1 := b1.a_eq; have a2 := b2.a_eq
  have := b1.y_ge; have := b2.y_ge; have := b1.f_ge; have := b2.f_ge
  unfold loopP expP delP at h1 h2
  rcases h1 with ⟨rfl,rfl | rfl⟩ | (⟨rfl,_,_⟩ | ⟨rfl,_,_⟩) | (⟨rfl,_,_⟩ | ⟨rfl,_,_⟩) <;>
  rcases h2 with ⟨h3,h4 | h4⟩ | (⟨h3,_,_⟩ | ⟨h3,_,_⟩) | (⟨h3,_,_⟩ | ⟨h3,_,_⟩) <;> omega

theorem loopP_body {j j' r c : Nat} (hj : j<p.J) (hj' : j'<p.J) (h1 : p.loopP j r c) (h2 : p.bodyP j' r c) :
    False := by
  have b1 := p.bounds hj
  have b2 := p.bounds hj'
  have a1 := b1.a_eq
  have yb := b1.y_band
  have hW : p.W<p.T' := by unfold W; have := p.band_fit; omega
  have hf : p.f j=p.C (p.colOf j) := rfl
  have hC : p.M0≤p.C (p.colOf j') := by unfold C; omega
  have hR : p.W+4≤p.R (p.rowOf j') := by unfold R; omega
  unfold bodyP at h2
  unfold loopP expP delP at h1
  rcases h1 with ⟨rfl,rfl | rfl⟩ | (⟨rfl,_,_⟩ | ⟨rfl,h5,h6⟩) | (⟨rfl,h5,h6⟩ | ⟨rfl,_,_⟩)
  · omega
  · omega
  · omega
  · have := p.slotRow_eq (r1:=p.rowOf j) (r2:=p.rowOf j') (x:=p.y j+1) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
    rw [this] at yb; omega
  · have := p.slotRow_eq (r1:=p.rowOf j) (r2:=p.rowOf j') (x:=p.y j) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
    rw [this] at yb; omega
  · omega

end Params

end SlidingPuzzle.NestedRouting.Corner
