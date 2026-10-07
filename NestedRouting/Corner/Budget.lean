import NestedRouting.Corner.Tree

/-! Budget bounds for the node tree. Every node of side `T` has rate at most
`Kr*T` and base at most `2*Σ_{x∈cells} d(o,x) + Kl*T² + K0*T²*depth`, where `o`
is the corner of its square. The distance sum is the productive term: it
telescopes because a child's corner offset plus the distance inside the
child is the distance in the parent. -/
namespace SlidingPuzzle.NestedRouting.Corner
open Interface Placement Finset

set_option linter.unusedSectionVars false

namespace Consts
variable (k : Consts)

/-- The depth of the tree below a node of side `T`. -/
def dep (T : Nat) : Nat := if h : k.Tbig≤T then dep (k.child T)+1 else 0
termination_by T
decreasing_by exact k.child_lt h

theorem dep_star {T : Nat} (h : k.Tbig≤T) : k.dep T=k.dep (k.child T)+1 := by
  rw [dep]; simp [h]

theorem dep_leaf {T : Nat} (h : ¬k.Tbig≤T) : k.dep T=0 := by
  rw [dep]; simp [h]

/-- A star needs side at least `Tbig`, so the depth is at most `log_b (T/Tbig) + 1`. -/
theorem dep_le_log_div (T : Nat) (hT : k.Tbig≤T) : k.dep T≤Nat.log k.b (T/k.Tbig)+1 := by
  induction T using Nat.strong_induction_on with
  | _ T ih =>
  rw [k.dep_star hT]
  have hb := k.b_two
  have hTb : 0<k.Tbig := by unfold Tbig; omega
  by_cases hc : k.Tbig≤k.child T
  · have h1 := ih (k.child T) (k.child_lt hT) hc
    have h2 : k.child T/k.Tbig≤T/k.Tbig/k.b := by
      rw [Nat.div_div_eq_div_mul,Nat.mul_comm,←Nat.div_div_eq_div_mul]
      apply Nat.div_le_div_right
      unfold child; exact Nat.div_le_div_right (Nat.sub_le _ _)
    have h3 := Nat.log_mono_right (b:=k.b) h2
    rw [Nat.log_div_base] at h3
    have h4 : k.b≤T/k.Tbig := by
      apply (Nat.le_div_iff_mul_le hTb).mpr
      have := k.child_mul T
      have : k.b*k.Tbig≤k.b*k.child T := Nat.mul_le_mul_left _ hc
      omega
    have h5 : 1≤Nat.log k.b (T/k.Tbig) := Nat.log_pos (by omega) h4
    omega
  · rw [k.dep_leaf hc]; omega

/-- The hub overhead of a service on spoke `j`, `a_j = M0 - 2(j+1)` from the
carrier: two hub exchanges `12 a_j + 24`, the access walk `a_j`, the hand-over. -/
def cs0 : Nat := 26*(k.M0-2)+50
/-- A service's cost per cell of its child beyond `2δ_j` (the exact lanes take
`2W + 2a_j + 4 - 4c_j` off): `24 a_j + 46 + 4(b-1) - 2W`, averaged over the
spokes with `Σ a_j = J (M0 - J - 1)`. -/
def sv : Nat := 24*(k.M0-k.b*k.b-1)+46+4*(k.b-1)-2*k.W
/-- The constant part of a service cost, lanes included. -/
def csl : Nat := 24*(k.M0-2)+2*k.M0+4*k.b+50
/-- Per unit of side of a star: `csl + 1 ≤ lam·T` for `T ≥ Tbig` (the `1`
pays for rounding). -/
def lam : Nat := Ledger.cdiv (k.csl+1) k.Tbig
/-- Direct-exchange cost per unit of side of a star: `16T + 24W + 170 ≤ dk·T`. -/
def dk : Nat := 16+Ledger.cdiv (24*k.W+170) k.Tbig

/-- The wrapper cost of a request: two wrapper cycles and the connector both ways. -/
def wrapC : Nat := 2*(12*k.W+34)+2*(k.W+1)
/-- The constant part of a late request: a direct exchange and a wrapper
cost `16T + dc`. -/
def dc : Nat := 24*k.W+170+k.wrapC

/-- The part of a service cost not carried by the weights `2T'·(row+col)` and
`48·(J-1-j)`. -/
def cb0 : Nat := 24*(k.M0-2*(k.b*k.b))+54+2*k.M0+4*(k.b-1)

/-- The rate per unit of side: `Kr·(b - H)·Tbig ≥ b·(H·cb0 + 48·W2 + 4 + dc) + (2·W1 + 16b)·Tbig`
with the layered bounds `W1 = wp1/hq`, `W2 = wp2/hq`, the constants divided by `Tbig ≤ T`. -/
def Kr : Nat := Ledger.cdiv (k.hp*k.b*k.cb0+48*k.b*k.wp2+4*k.b*k.hq+k.b*k.hq*k.dc+(2*k.wp1+16*k.b*k.hq)*k.Tbig)
  ((k.hq*k.b-k.hp)*k.Tbig)

theorem Tbig_pos : 0<k.Tbig := by unfold Tbig; omega

theorem Kr_spec : k.hp*k.b*k.cb0+48*k.b*k.wp2+4*k.b*k.hq+k.b*k.hq*k.dc+(2*k.wp1+16*k.b*k.hq)*k.Tbig≤
    k.Kr*((k.hq*k.b-k.hp)*k.Tbig) := by
  have := Ledger.le_mul_cdiv
    (x:=k.hp*k.b*k.cb0+48*k.b*k.wp2+4*k.b*k.hq+k.b*k.hq*k.dc+(2*k.wp1+16*k.b*k.hq)*k.Tbig)
    (q:=(k.hq*k.b-k.hp)*k.Tbig) (Nat.mul_pos (by have := k.hJ_lt; omega) k.Tbig_pos)
  unfold Kr; exact this.trans (le_of_eq (Nat.mul_comm _ _))
/-- Reserve cells per unit of side, with the remainder `T - M0 - b·T'` at most `b - 1`. -/
def cr : Nat := 2*(k.M0+k.b-1)+(k.b-1)*k.W
/-- The constant the reserve count falls short of `cr·T` by. -/
def crc : Nat := (k.M0+k.b-1)*(k.M0+k.b-1+k.b*k.W)+6-6*(k.b*k.b)
/-- Constant part of the lane total: `J + Σ_j (|X_j|+|Y_j|+2) ≤ 2b(b-1)T + J + Lc`. -/
def Lc : Nat := k.b*k.b*(2*(k.b*k.b)+4*k.b+4)
/-- The terms of a star's base that are only linear in `T`, per unit of `T`. -/
def linC (b cs0 M0 W Kr Lc fl ll : Nat) : Nat :=
  b*b*(2*M0+4)+8*(b*b)+Ledger.cdiv (Kr*(b*b+Lc)) b+b*b*cs0+2*(W+M0)+fl+ll

/-- The final sort's `T²` coefficient, per `24`: the reserve region's distance sum. -/
def al : Nat := 3*(k.b-1)+2*(k.M0-2)+k.W*(k.b-2)
/-- The final sort's linear coefficient. -/
def fl : Nat := Ledger.cdiv (9*(k.b*(6*(k.b-1+k.M0)^2+2*k.M0*k.W*k.b+3*k.W^2*k.b+6*k.W*k.b+2*k.W))) k.b+
  Ledger.cdiv (9*((k.b-1+k.M0)^2*(2*(k.b-1+k.M0)+k.W))) k.Tbig+216*(k.b*k.b)+28*k.cr+168

/-- The corner offset of the first slot. -/
def kap : Nat := k.W+4+k.M0
/-- The largest service cost beyond `2δ_j`. -/
def smax : Nat := 24*(k.M0-2)+46+4*(k.b-1)-2*k.W
/-- Services on lane tiles, the `T²` part: `4 Σ_j (row + col)² T'²`. -/
def lq : Nat := Ledger.cdiv (4*∑ j ∈ Finset.range (k.b*k.b), (j/k.b+j%k.b)^2) (k.b*k.b)
/-- Services on lane tiles, the linear part (the constant divided by `Tbig ≤ T`). -/
def ll : Nat := 2*(4*k.kap+k.smax)*(k.b*(k.b-1))+Ledger.cdiv (2*(k.b*k.b)*(k.kap*(2*k.kap+k.smax))) k.Tbig

/-- Width of the static margin in slot row `ρ`: four left columns and the
columns of the spokes of slot rows `≤ ρ`. -/
def sw (ρ : Nat) : Nat := 4+2*k.b*(ρ+1)
/-- The static margin's gain per `T²`: `Σ_ρ sw ρ (16b - 12ρ - 6) / b²`. -/
def gq : Nat := (∑ ρ ∈ Finset.range k.b, k.sw ρ*(16*k.b-12*ρ-6))/(k.b*k.b)
/-- Its linear correction. -/
def gl : Nat := (∑ ρ ∈ Finset.range k.b, k.sw ρ*((16*k.b-12*ρ-6)*k.W+(18*k.W+54-4*k.M0)))+2*k.gq*(k.M0+k.b)

def K0 : Nat := k.sv+k.lq+2*(k.b-1)*k.Kr+k.wrapC+(k.dk*k.cr-k.gq)+18*k.al+
  Ledger.cdiv (linC k.b k.cs0 k.M0 k.W k.Kr k.Lc k.fl (k.ll+k.gl)-k.dk*k.crc) k.Tbig
/-- Leaf cost per unit of area (charged once, not per level): one request
per cell, charged by its position, at `(28/3)T³ + O(T²)` in all, and the
final sort at `14T³ + O(T²)`. -/
def Kl : Nat := Ledger.cdiv (280*k.Tbig+(288*k.W+2526)) 12

/-- The rate constant is at least `24`: `24(qb - p) ≤ 4p(b-1) + 16bq` as `2q ≤ p`. -/
theorem Kr_ge : 24≤k.Kr := by
  have h := k.Kr_spec
  have hlt := k.hJ_lt
  have hb3 := k.hb3
  have hT := k.Tbig_pos
  set D := k.hq*k.b-k.hp with hD
  have eb : 16*k.b*k.hq=16*(k.hq*k.b) := by ring
  have a4 : 24*D≤16*k.b*k.hq := by omega
  have a5 : 24*D*k.Tbig≤(2*k.wp1+16*k.b*k.hq)*k.Tbig :=
    Nat.mul_le_mul_right _ (by omega)
  have hD0 : 0<D*k.Tbig := Nat.mul_pos (by omega) hT
  by_contra hc
  push Not at hc
  have a1 : k.Kr*(D*k.Tbig)≤23*(D*k.Tbig) := Nat.mul_le_mul_right _ (by omega)
  have e1 : 24*D*k.Tbig=24*(D*k.Tbig) := by ring
  omega

theorem csl_le {T : Nat} (hT : k.Tbig≤T) : k.csl+1≤k.lam*T := by
  have := Ledger.le_mul_cdiv (x:=k.csl+1) (q:=k.Tbig) k.Tbig_pos
  unfold lam
  calc k.csl+1≤k.Tbig*Ledger.cdiv (k.csl+1) k.Tbig := this
    _≤T*Ledger.cdiv (k.csl+1) k.Tbig := Nat.mul_le_mul_right _ hT
    _=_ := Nat.mul_comm _ _

theorem cs0_le {T : Nat} (hT : k.Tbig≤T) : k.cs0≤k.lam*T := by
  have := k.csl_le hT; unfold csl at this; unfold cs0; omega

theorem six_bb_le_Tbig : 6*(k.b*k.b)≤k.Tbig := by
  have hl := k.Tmin_lane
  have hb := k.b_two
  have : k.b*(2*(k.b*k.b))≤k.b*k.Tmin := Nat.mul_le_mul_left _ (by omega)
  have : 4*(k.b*k.b)≤k.b*(2*(k.b*k.b)) := by nlinarith
  unfold Tbig M0; omega

theorem Tmin_le_Tbig : k.Tmin≤k.Tbig := by
  have := Nat.le_mul_of_pos_left k.Tmin k.b_pos; unfold Tbig; omega

variable {n : Nat} [NeZero n] {G : Board n}

omit [NeZero n] in
theorem card_leafBody (T : Nat) : (k.leafBody (T:=T)).card=(T-k.W)*T := by
  have e : k.leafBody (T:=T)=(univ.filter (fun i : Fin T => k.W ≤ i.val))×ˢ(univ : Finset (Fin T)) := by
    ext x; simp [leafBody]
  rw [e,card_product,card_univ,Fintype.card_fin]
  congr 1
  have h1 := Fin.card_filter_val_lt (n:=T) (m:=k.W)
  have h2 := card_filter_add_card_filter_not (s:=(univ : Finset (Fin T))) (fun i : Fin T => i.val<k.W)
  simp only [card_univ,Fintype.card_fin,not_lt] at h2
  have h3 : (univ.filter (fun i : Fin T => i.val<k.W)).card=min T k.W := h1
  omega

theorem card_bodyCells {T : Nat} (q : Placement T n) : (k.bodyCells q).card=(T-k.W)*T := by
  unfold bodyCells; rw [card_map,card_leafBody]

/-- Distance sum from the corner of the square. -/
def dsum {T : Nat} [NeZero T] (q : Placement T n) (X : Finset (Cell n)) : Nat :=
  ∑ x∈X, gridDistance (q.loc 0 0) x

/-- A body's distance sum is at most that of the whole square, `T²(T-1)`. -/
theorem dsum_body_le {T : Nat} [NeZero T] (q : Placement T n) : dsum q (k.bodyCells q)≤T*(T*(T-1)) := by
  unfold dsum bodyCells
  rw [sum_map]
  have hpt : ∀ y : Cell T, gridDistance (q.loc 0 0) (q.embed y)=y.1.val+y.2.val := by
    intro y
    have h0 : 0<T := NeZero.pos T
    rw [←q.loc_eq y.1.isLt y.2.isLt,q.loc_dist h0 h0 y.1.isLt y.2.isLt]
    simp [Nat.dist]
  simp_rw [hpt]
  calc ∑ y∈k.leafBody, (y.1.val+y.2.val)≤∑ y : Cell T, (y.1.val+y.2.val) :=
        sum_le_sum_of_subset (subset_univ _)
    _=T*(T*(T-1)) := by
      rw [Fintype.sum_prod_type]
      simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,smul_eq_mul]
      rw [←mul_sum]
      have hs : ∑ i : Fin T, (i : Nat)=∑ i∈range T, i := Fin.sum_univ_eq_sum_range (fun i => i) T
      have h2 := Finset.sum_range_id_mul_two T
      rw [hs]
      calc T*∑ i∈range T, i+T*∑ i∈range T, i=T*((∑ i∈range T, i)*2) := by ring
        _=T*(T*(T-1)) := by rw [h2]

theorem dsum_body_eq {T : Nat} [NeZero T] (q : Placement T n) :
    dsum q (k.bodyCells q)=∑ i∈range T, ∑ j∈range T, if k.W ≤ i then i+j else 0 := by
  classical
  unfold dsum bodyCells
  rw [sum_map]
  have hpt : ∀ y : Cell T, gridDistance (q.loc 0 0) (q.embed y)=y.1.val+y.2.val := by
    intro y
    have h0 : 0<T := NeZero.pos T
    rw [←q.loc_eq y.1.isLt y.2.isLt,q.loc_dist h0 h0 y.1.isLt y.2.isLt]
    simp [Nat.dist]
  simp_rw [hpt]
  unfold leafBody
  rw [sum_filter,Fintype.sum_prod_type]
  rw [Fin.sum_univ_eq_sum_range (fun i => ∑ y : Fin T, if k.W ≤ i then i+y.val else 0) T]
  apply sum_congr rfl; intro i _
  rw [Fin.sum_univ_eq_sum_range (fun j => if k.W ≤ i then i+j else 0) T]

theorem dist_body_le {T : Nat} [NeZero T] (q : Placement T n) {x : Cell n} (hx : x∈k.bodyCells q) :
    gridDistance (q.loc 0 0) x≤2*T := by
  obtain ⟨r,c,_,hr,hc,rfl⟩ := (k.mem_bodyCells q).mp hx
  have h0 : 0<T := NeZero.pos T
  rw [q.loc_dist h0 h0 hr hc]; simp [Nat.dist]; omega

/-- The budget invariant of a built node. -/
def Bud {T cs : Nat} [NeZero T] {q : Placement T n} (B : k.Built G T cs q) : Prop :=
  B.R.rate≤k.Kr*T ∧ B.R.base≤2*dsum q B.R.cells+k.Kl*(T*T)+k.K0*(T*T)*k.dep T

/-! ### Sums over a square grid -/

theorem sum_max_le (T : Nat) : 6*∑ i∈range T, ∑ j∈range T, max i j≤4*(T*(T*T)) := by
  induction T with
  | zero => simp
  | succ T ih =>
    have row (i : Nat) : ∑ j∈range (T+1), max i j=∑ j∈range T, max i j+max i T := sum_range_succ _ _
    simp_rw [row]
    rw [sum_add_distrib,sum_range_succ (fun i => ∑ j∈range T, max i j),sum_range_succ (fun i => max i T)]
    have h1 : ∑ i∈range T, max i T=T*T := by
      rw [sum_congr rfl (fun i hi => max_eq_right (le_of_lt (mem_range.mp hi))),sum_const,card_range,smul_eq_mul]
    have h2 : ∑ j∈range T, max T j=T*T := by
      rw [sum_congr rfl (fun j hj => max_eq_left (le_of_lt (mem_range.mp hj))),sum_const,card_range,smul_eq_mul]
    rw [h1,h2,max_self]
    have : 4*(T*(T*T))+6*(2*(T*T)+T)≤4*((T+1)*((T+1)*(T+1))) := by ring_nf; omega
    omega

theorem sum_add_grid (T : Nat) : ∑ i∈range T, ∑ j∈range T, (i+j)=T*(T*(T-1)) := by
  have inner (i : Nat) : ∑ j∈range T, (i+j)=T*i+∑ j∈range T, j := by
    rw [sum_add_distrib,sum_const,card_range,smul_eq_mul]
  rw [sum_congr rfl (fun i _ => inner i),sum_add_distrib,←mul_sum,sum_const,card_range,smul_eq_mul]
  have h2 := sum_range_id_mul_two T
  have : T*∑ i∈range T, i+T*∑ j∈range T, j=T*((∑ i∈range T, i)*2) := by ring
  rw [this,h2]

/-- The distance sum of the rows `≥ W` of a `T × T` grid, doubled. -/
theorem body_grid (T W : Nat) (hW : W≤T) :
    2*(∑ i∈range T, ∑ j∈range T, if W ≤ i then i+j else 0)+T*(W*(W-1))+W*(T*(T-1))=2*(T*(T*(T-1))) := by
  have split (i : Nat) : ∑ j∈range T, (i+j)=(∑ j∈range T, if W ≤ i then i+j else 0)+
      ∑ j∈range T, (if W ≤ i then 0 else i+j) := by
    rw [←sum_add_distrib]; apply sum_congr rfl; intro j _; split_ifs <;> simp
  have h1 := sum_add_grid T
  rw [sum_congr rfl (fun i _ => split i),sum_add_distrib] at h1
  have low : ∑ i∈range T, ∑ j∈range T, (if W ≤ i then 0 else i+j)=∑ i∈range W, ∑ j∈range T, (i+j) := by
    rw [←sum_range_add_sum_Ico _ hW]
    have e1 : ∑ i∈range W, ∑ j∈range T, (if W ≤ i then 0 else i+j)=∑ i∈range W, ∑ j∈range T, (i+j) := by
      apply sum_congr rfl; intro i hi; have := mem_range.mp hi
      apply sum_congr rfl; intro j _; rw [if_neg (by omega)]
    have e2 : ∑ i∈Ico W T, ∑ j∈range T, (if W ≤ i then 0 else i+j)=0 := by
      apply sum_eq_zero; intro i hi; have := (mem_Ico.mp hi).1
      apply sum_eq_zero; intro j _; rw [if_pos this]
    rw [e1,e2,Nat.add_zero]
  have inner (i : Nat) : ∑ j∈range T, (i+j)=T*i+∑ j∈range T, j := by
    rw [sum_add_distrib,sum_const,card_range,smul_eq_mul]
  rw [low] at h1
  rw [sum_congr rfl (fun i _ => inner i),sum_add_distrib,←mul_sum,sum_const,card_range,smul_eq_mul] at h1
  have g1 := sum_range_id_mul_two W
  have g2 := sum_range_id_mul_two T
  have e : 2*(T*∑ i∈range W, i+W*∑ j∈range T, j)=T*((∑ i∈range W, i)*2)+W*((∑ j∈range T, j)*2) := by ring
  rw [g1,g2] at e
  omega

/-- The reserve region of a corner star, doubled, as a polynomial: with
`T = b·x + M0 + E`, it is at most `2b²·α·x² + β·x + γ`. -/
theorem reserve_poly (b W M0 x E : Nat) (hb : 2≤b) (hE : E+1≤b) (hWM : W≤M0) (hW2 : 2≤W) :
    (2*(b*x+M0+E)^3-(2+W)*(b*x+M0+E)^2+(2*W-W^2)*(b*x+M0+E) : ℤ)-
      b^2*(2*x^3-(2+W)*x^2+(2*W-W^2)*x)-2*(x-W)*x*(b^2*(W+4+M0)+x*b^2*(b-1))≤
      2*b^2*(3*(b-1)+2*M0+W*b-2*W-4)*x^2+
      b*(6*(b-1+M0)^2+2*M0*W*b+3*W^2*b+6*W*b+2*W)*x+(b-1+M0)^2*(2*(b-1+M0)+W) := by
  have e : (2*(b*x+M0+E)^3-(2+W)*(b*x+M0+E)^2+(2*W-W^2)*(b*x+M0+E) : ℤ)-
      b^2*(2*x^3-(2+W)*x^2+(2*W-W^2)*x)-2*(x-W)*x*(b^2*(W+4+M0)+x*b^2*(b-1))=
      2*b^2*(3*E+2*M0+W*b-2*W-4)*x^2+
      b*(6*(E+M0)^2+2*M0*W*b-2*M0*W-4*M0+3*W^2*b-W^2+6*W*b+2*W-2*E*W-4*E)*x+
      (E+M0)*(E+M0-W)*(2*(E+M0)+W-2) := by ring
  rw [e]
  have hE' : (E:ℤ)≤b-1 := by omega
  have hx0 : (0:ℤ)≤x := by positivity
  have hb0 : (0:ℤ)≤b := by positivity
  have hE0 : (0:ℤ)≤E := by positivity
  have hM : (W:ℤ)≤M0 := by exact_mod_cast hWM
  have hW0 : (2:ℤ)≤W := by exact_mod_cast hW2
  -- the x² coefficient
  have a1 : 2*(b:ℤ)^2*(3*E+2*M0+W*b-2*W-4)*x^2≤2*b^2*(3*(b-1)+2*M0+W*b-2*W-4)*x^2 := by
    have : (0:ℤ)≤2*b^2*x^2 := by positivity
    nlinarith
  -- the x coefficient
  have a2 : (b:ℤ)*(6*(E+M0)^2+2*M0*W*b-2*M0*W-4*M0+3*W^2*b-W^2+6*W*b+2*W-2*E*W-4*E)*x≤
      b*(6*(b-1+M0)^2+2*M0*W*b+3*W^2*b+6*W*b+2*W)*x := by
    have hu : ((E:ℤ)+M0)^2≤(b-1+M0)^2 := by
      have : (0:ℤ)≤E+M0 := by positivity
      nlinarith
    have : (0:ℤ)≤b*x := by positivity
    have h3 : (6*(E+M0)^2+2*M0*W*b-2*M0*W-4*M0+3*W^2*b-W^2+6*W*b+2*W-2*E*W-4*E : ℤ)≤
        6*(b-1+M0)^2+2*M0*W*b+3*W^2*b+6*W*b+2*W := by nlinarith
    have := mul_le_mul_of_nonneg_left h3 this
    nlinarith
  -- the constant
  have a3 : ((E:ℤ)+M0)*(E+M0-W)*(2*(E+M0)+W-2)≤(b-1+M0)^2*(2*(b-1+M0)+W) := by
    set u : ℤ := E+M0
    have hu0 : W≤u := by simp only [u]; linarith
    have huU : u≤b-1+M0 := by simp only [u]; linarith
    have h1 : u*(u-W)*(2*u+W-2)≤u*u*(2*u+W) := by
      have : 0≤u := by linarith
      have : 0≤u-W := by linarith
      have : 0≤2*u+W-2 := by linarith
      have : u*(u-W)≤u*u := by nlinarith
      nlinarith
    have h2 : u*u*(2*u+W)≤(b-1+M0)^2*(2*(b-1+M0)+W) := by
      have : 0≤u := by linarith
      have : u*u≤(b-1+M0)^2 := by nlinarith
      have : 0≤2*u+W := by linarith
      have : 2*u+W≤2*(b-1+M0)+W := by linarith
      nlinarith
    linarith
  linarith

/-- The reserve distance sum of a corner star from its closed-form pieces. -/
theorem resid_arith {T x b W M0 E AT Ax Sd R Z : Nat} (hb : 2≤b) (hE : E+1≤b) (hWM : W≤M0) (hW2 : 2≤W)
    (hx : W≤x) (hT : T=b*x+M0+E)
    (hAT : 2*AT+T*(W*(W-1))+W*(T*(T-1))=2*(T*(T*(T-1))))
    (hAx : 2*Ax+x*(W*(W-1))+W*(x*(x-1))=2*(x*(x*(x-1))))
    (hSd : Sd=b*b*(W+4+M0)+x*(b*(b*(b-1))))
    (hR : R+(b*b*Ax+(x-W)*x*Sd)≤AT+Z) :
    2*R≤2*(3*(b-1)+2*(M0-2)+W*(b-2))*(T*T)+
      b*(6*(b-1+M0)^2+2*M0*W*b+3*W^2*b+6*W*b+2*W)*x+(b-1+M0)^2*(2*(b-1+M0)+W)+2*Z := by
  have key := reserve_poly b W M0 x E hb hE hWM hW2
  have hT1 : 1≤T := by subst hT; nlinarith
  have hx1 : 1≤x := by omega
  have hM2 : 2≤M0 := by omega
  have hR2 := Nat.mul_le_mul_left 2 hR
  zify [hx,(by omega : 1≤W),hT1,hx1,(by omega : 1≤b),hM2,hb] at hAT hAx hSd hR2 ⊢
  have hTz : (T:ℤ)=b*x+M0+E := by exact_mod_cast hT
  have h1 : (2*AT : ℤ)=2*T^3-(2+W)*T^2+(2*W-W^2)*T := by linear_combination hAT
  have h2a : (2*Ax : ℤ)=2*x^3-(2+W)*x^2+(2*W-W^2)*x := by linear_combination hAx
  have h2 : (b:ℤ)^2*(2*Ax)=b^2*(2*x^3-(2+W)*x^2+(2*W-W^2)*x) := by rw [h2a]
  have h4 : ((x:ℤ)-W)*x*Sd=((x:ℤ)-W)*x*(b*b*(W+4+M0)+x*(b*(b*(b-1)))) := by rw [hSd]
  rw [hTz] at h1
  have A : (2*R : ℤ)≤2*(b:ℤ)^2*(3*(b-1)+2*M0+W*b-2*W-4)*x^2+
      b*(6*(b-1+M0)^2+2*M0*W*b+3*W^2*b+6*W*b+2*W)*x+(b-1+M0)^2*(2*(b-1+M0)+W)+2*Z := by
    linear_combination hR2+key+h1-h2-2*h4
  have hbx : (b:ℤ)*x≤T := by
    have : (0:ℤ)≤M0+E := by positivity
    linarith [hTz]
  have hsq : (b:ℤ)^2*x^2≤(T:ℤ)*T := by
    have h0 : (0:ℤ)≤b*x := by positivity
    have := mul_le_mul hbx hbx h0 (by linarith)
    have e : (b:ℤ)^2*x^2=(b*x)*(b*x) := by ring
    rw [e]; exact this
  have hcoef : (0:ℤ)≤3*((b:ℤ)-1)+2*((M0:ℤ)-2)+W*((b:ℤ)-2) := by
    have hb2 : (2:ℤ)≤b := by exact_mod_cast hb
    have : (0:ℤ)≤W*((b:ℤ)-2) := mul_nonneg (by positivity) (by linarith)
    have : (2:ℤ)≤M0 := by exact_mod_cast hM2
    linarith
  have B : 2*(b:ℤ)^2*(3*(b-1)+2*M0+W*b-2*W-4)*x^2≤2*(3*((b:ℤ)-1)+2*((M0:ℤ)-2)+W*((b:ℤ)-2))*(T*T) := by
    have e : 2*(b:ℤ)^2*(3*(b-1)+2*M0+W*b-2*W-4)*x^2=
        2*(3*((b:ℤ)-1)+2*((M0:ℤ)-2)+W*((b:ℤ)-2))*((b:ℤ)^2*x^2) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hsq hcoef
    linarith
  linarith

theorem sumTw_le (T : Nat) [NeZero T] :
    6*∑ y : Cell T, (Cycle3.tw y.1.val y.2.val+2)≤56*(T*(T*T))+108*(T*T) := by
  unfold Cycle3.tw
  rw [Fintype.sum_prod_type]
  have e : ∑ x : Fin T, ∑ y : Fin T, (2*(2*(x.val+y.val)+4*max x.val y.val+6)+4+2)=
      ∑ i∈range T, ∑ j∈range T, (4*(i+j)+8*max i j+18) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => ∑ y : Fin T, (2*(2*(i+y.val)+4*max i y.val+6)+4+2)) T]
    apply sum_congr rfl; intro i _
    rw [Fin.sum_univ_eq_sum_range (fun j => 2*(2*(i+j)+4*max i j+6)+4+2) T]
    apply sum_congr rfl; intro j _; ring_nf
  have inner (i : Nat) : ∑ j∈range T, (4*(i+j)+8*max i j+18)=
      4*∑ j∈range T, (i+j)+8*∑ j∈range T, max i j+18*T := by
    rw [sum_add_distrib,sum_add_distrib,←mul_sum,←mul_sum,sum_const,card_range,smul_eq_mul,Nat.mul_comm T 18]
  have outer : ∑ i∈range T, ∑ j∈range T, (4*(i+j)+8*max i j+18)=
      4*∑ i∈range T, ∑ j∈range T, (i+j)+8*∑ i∈range T, ∑ j∈range T, max i j+18*(T*T) := by
    rw [sum_congr rfl (fun i _ => inner i),sum_add_distrib,sum_add_distrib,←mul_sum,←mul_sum,sum_const,
      card_range,smul_eq_mul]
    ring
  rw [e,outer]
  have h1 := sum_max_le T
  have h2 := sum_add_grid T
  have h3 : T*(T*(T-1))≤T*(T*T) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  omega

theorem leafF_le (T : Nat) [NeZero T] : 4*leafF (T:=T)≤56*(T*(T*T))+114*(T*T) := by
  have h := sumTw_le T
  unfold leafF
  have : 4*∑ y : Cell T, (3*(Cycle3.tw y.1.val y.2.val+2)+3)/4≤
      3*∑ y : Cell T, (Cycle3.tw y.1.val y.2.val+2)+3*(T*T) := by
    rw [mul_sum,mul_sum]
    calc ∑ y : Cell T, 4*((3*(Cycle3.tw y.1.val y.2.val+2)+3)/4)
        ≤∑ y : Cell T, (3*(Cycle3.tw y.1.val y.2.val+2)+3) := sum_le_sum (fun y _ => by omega)
      _=_ := by
        rw [sum_add_distrib,sum_const,card_univ,Fintype.card_prod,Fintype.card_fin,smul_eq_mul]
        ring
  omega

/-! ### Leaves -/

theorem leaf_bud {T : Nat} [NeZero T] (hW : k.W<T) (h6 : 6≤T) (cs : Nat) (hcs : 2*cs+1<k.W)
    (q : Placement T n) (hg : k.GoalOK G q) (hT : ¬k.Tbig≤T) (hTm : k.Tmin≤T) :
    k.Bud (k.leaf hW h6 cs hcs q hg) := by
  -- a request costs at most `16T + 24W + 170`
  have hr : (k.leafSpec hW h6 cs hcs q hg).rcost≤16*T+(24*k.W+170) := by
    change Entry.dcost q (k.leaf_fit hW h6 cs hcs)≤_
    have := Entry.dcost_le q (k.leaf_fit hW h6 cs hcs)
    omega
  refine ⟨?_,?_⟩
  · change (k.leafSpec hW h6 cs hcs q hg).rcost≤_
    have h1 := k.Tmin_leaf
    have h2 := k.Kr_ge
    have : 24*T≤k.Kr*T := Nat.mul_le_mul_right _ h2
    unfold W at hr; omega
  change (k.leafSpec hW h6 cs hcs q hg).budgetBase≤_
  unfold LeafSpec.budgetBase
  have e0 : (k.leafSpec hW h6 cs hcs q hg).reserve=∅ := rfl
  rw [e0,card_empty,Nat.mul_zero,Nat.add_zero]
  -- the requests: each core cell once, at its position
  have hdw : ∑ x∈(k.leafSpec hW h6 cs hcs q hg).core, (k.leafSpec hW h6 cs hcs q hg).rw x≤
      ∑ y : Cell T, (Cycle3.tw y.1.val y.2.val+2)+(24*k.W+164)*(T*T) := by
    have hc := Entry.dw_const q (k.leaf_fit hW h6 cs hcs)
    calc ∑ x∈(k.leafSpec hW h6 cs hcs q hg).core, (k.leafSpec hW h6 cs hcs q hg).rw x
        ≤∑ y : Cell T, Entry.dw q (k.leaf_fit hW h6 cs hcs) y.1.val y.2.val :=
          sum_le_sum_of_subset (subset_univ _)
      _≤∑ y : Cell T, ((Cycle3.tw y.1.val y.2.val+2)+(24*k.W+164)) := by
          apply sum_le_sum; intro y _
          unfold Entry.dw Cycle3.tw
          have : y.1.val-2*cs≤y.1.val := Nat.sub_le _ _
          have : max (y.1.val-2*cs) y.2.val≤max y.1.val y.2.val := max_le_max this le_rfl
          omega
      _=_ := by
          rw [sum_add_distrib,sum_const,card_univ,Fintype.card_prod,Fintype.card_fin,smul_eq_mul]; ring
  have hf : 4*(k.leafSpec hW h6 cs hcs q hg).fcost≤56*(T*(T*T))+114*(T*T) := leafF_le T
  have hs := sumTw_le T
  have hT' : T≤k.Tbig := by omega
  have hK : 280*T+(288*k.W+2526)≤12*k.Kl := by
    have := Ledger.le_mul_cdiv (x:=280*k.Tbig+(288*k.W+2526)) (q:=12) (by norm_num)
    have h280 : 280*T≤280*k.Tbig := Nat.mul_le_mul_left _ hT'
    change _≤12*Ledger.cdiv (280*k.Tbig+(288*k.W+2526)) 12
    exact le_trans (Nat.add_le_add_right h280 _) this
  have := Nat.mul_le_mul_right (T*T) hK
  have e : (280*T+(288*k.W+2526))*(T*T)=280*(T*(T*T))+288*k.W*(T*T)+2526*(T*T) := by ring
  have e2 : 12*k.Kl*(T*T)=12*(k.Kl*(T*T)) := by ring
  have e3 : 12*((24*k.W+164)*(T*T))=288*k.W*(T*T)+1968*(T*T) := by ring
  omega

/-- Reserve count arithmetic, exactly: with `T = b·x + D` and `D ≤ D'`, the
cells of the node minus those of its `b²` child bodies are at most
`(2D' + (b-1)W)·T - D'(D' + bW) + 6b² - 6`. -/
theorem r_arith {T x r b W D D' : Nat} (hb : 1≤b) (hWT : W≤T) (hT : T=b*x+D) (hD : D≤D')
    (hroom : D+D'+b*W≤2*T) (hx : W≤x) (h : (T-W)*T+6*(b*b)=(b*b)*((x-W)*x)+r+6) :
    r+(D'*(D'+b*W)+6)≤(2*D'+(b-1)*W)*T+6*(b*b) := by
  have h' : ((T:Int)-W)*T+6*(b*b)=(b*b)*((x-W)*x)+r+6 := by
    have := congrArg (fun m : Nat => (m:Int)) h
    push_cast [Nat.cast_sub hx,Nat.cast_sub hWT] at this
    exact this
  have hT' : (T:Int)=b*x+D := by exact_mod_cast hT
  have hD' : (D:Int)≤D' := by exact_mod_cast hD
  have hr' : ((D+D'+b*W : Nat) : Int)≤((2*T : Nat) : Int) := by exact_mod_cast hroom
  push_cast at hr'
  have h1 : (0:Int)≤((D':Int)-D)*(2*T-D-D'-b*W) := mul_nonneg (by linarith) (by linarith)
  have key : (r:Int)+(D'*(D'+b*W)+6)≤(2*D'+((b:Int)-1)*W)*T+6*(b*b) := by
    rw [hT'] at h' h1 ⊢
    nlinarith
  have : ((r+(D'*(D'+b*W)+6) : Nat) : Int)≤(((2*D'+(b-1)*W)*T+6*(b*b) : Nat) : Int) := by
    push_cast [Nat.cast_sub hb]; linarith
  exact_mod_cast this

theorem child_upper' {T : Nat} (hT : k.Tbig≤T) : T+1≤k.b*k.child T+(k.M0+k.b) := by
  have hM := k.M0_le hT
  have h1 := Nat.div_add_mod (T-k.M0) k.b
  have h2 := Nat.mod_lt (T-k.M0) (by have := k.b_pos; omega : k.b>0)
  unfold child
  omega

theorem child_upper {T : Nat} (hT : k.Tbig≤T) : T≤k.b*k.child T+(k.M0+k.b) := by
  have hM := k.M0_le hT
  have h1 := Nat.div_add_mod (T-k.M0) k.b
  have h2 := Nat.mod_lt (T-k.M0) (by have := k.b_pos; omega : k.b>0)
  unfold child
  omega

theorem rate_arith {T Tb x b c0 K cb rm dc dw p q w1 w2 : Nat} (hq : 0<q) (hb : 1≤b)
    (hTb : Tb≤T) (hTb0 : 0<Tb) (hu : b*x≤T) (hlt : p<q*b)
    (hX : p*b*c0+48*b*w2+4*b*q+b*q*dc+(2*w1+16*b*q)*Tb≤K*((q*b-p)*Tb))
    (hcb : cb≤c0) (hrm : rm≤K*x) (hdw : dw≤16*T+dc) :
    (Ledger.cdiv (cb*p) q+Ledger.cdiv (2*x*w1) q+Ledger.cdiv (48*w2) q)+Ledger.cdiv (rm*p) q+dw≤K*T := by
  have c1 : q*Ledger.cdiv (cb*p) q≤cb*p+q := Ledger.cdiv_le.trans (by omega)
  have c2 : q*Ledger.cdiv (2*x*w1) q≤2*x*w1+q := Ledger.cdiv_le.trans (by omega)
  have c3 : q*Ledger.cdiv (48*w2) q≤48*w2+q := Ledger.cdiv_le.trans (by omega)
  have c4 : q*Ledger.cdiv (rm*p) q≤rm*p+q := Ledger.cdiv_le.trans (by omega)
  set D := q*b-p with hD
  have s1 : b*(cb*p)≤p*b*c0 := by
    calc b*(cb*p)=p*b*cb := by ring
      _≤p*b*c0 := Nat.mul_le_mul_left _ hcb
  have s2 : b*(2*x*w1)≤2*w1*T := by
    calc b*(2*x*w1)=2*w1*(b*x) := by ring
      _≤2*w1*T := Nat.mul_le_mul_left _ hu
  have s3 : b*(rm*p)≤K*T*p := by
    calc b*(rm*p)≤b*(K*x*p) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hrm)
      _=K*(b*x)*p := by ring
      _≤K*T*p := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hu)
  have s4 : b*(q*dw)≤b*q*(16*T+dc) := by
    calc b*(q*dw)=b*q*dw := by ring
      _≤_ := Nat.mul_le_mul_left _ hdw
  have sK : K*T*p+K*T*D=K*T*(q*b) := by rw [←Nat.mul_add]; congr 1; omega
  -- the constants, divided by `Tb ≤ T`
  set C := p*b*c0+48*b*w2+4*b*q+b*q*dc with hC
  have t1 : C*Tb≤C*T := Nat.mul_le_mul_left _ hTb
  have t2 : (C+(2*w1+16*b*q)*Tb)*T≤K*((q*b-p)*Tb)*T := Nat.mul_le_mul_right _ hX
  have t3 : Tb*(C+(2*w1+16*b*q)*T)≤Tb*(K*T*D) := by
    have e1 : Tb*(C+(2*w1+16*b*q)*T)=C*Tb+(2*w1+16*b*q)*(T*Tb) := by ring
    have e2 : (C+(2*w1+16*b*q)*Tb)*T=C*T+(2*w1+16*b*q)*(T*Tb) := by ring
    have e3 : K*((q*b-p)*Tb)*T=Tb*(K*T*D) := by rw [hD]; ring
    omega
  have t4 : C+(2*w1+16*b*q)*T≤K*T*D := Nat.le_of_mul_le_mul_left t3 hTb0
  have goal : b*(q*((Ledger.cdiv (cb*p) q+Ledger.cdiv (2*x*w1) q+Ledger.cdiv (48*w2) q)+
      Ledger.cdiv (rm*p) q+dw))≤b*(q*(K*T)) := by
    have e1 : b*(q*((Ledger.cdiv (cb*p) q+Ledger.cdiv (2*x*w1) q+Ledger.cdiv (48*w2) q)+
        Ledger.cdiv (rm*p) q+dw))=b*(q*Ledger.cdiv (cb*p) q)+b*(q*Ledger.cdiv (2*x*w1) q)+
        b*(q*Ledger.cdiv (48*w2) q)+b*(q*Ledger.cdiv (rm*p) q)+b*(q*dw) := by ring
    have e2 : b*(q*(K*T))=K*T*(q*b) := by ring
    have c1' := Nat.mul_le_mul_left b c1
    have c2' := Nat.mul_le_mul_left b c2
    have c3' := Nat.mul_le_mul_left b c3
    have c4' := Nat.mul_le_mul_left b c4
    have e4 : b*(cb*p+q)=b*(cb*p)+b*q := by ring
    have e5 : b*(2*x*w1+q)=b*(2*x*w1)+b*q := by ring
    have e6 : b*(48*w2+q)=48*b*w2+b*q := by ring
    have e7 : b*(rm*p+q)=b*(rm*p)+b*q := by ring
    have e8 : b*q*(16*T+dc)=16*b*q*T+b*q*dc := by ring
    have e9 : (2*w1+16*b*q)*T=2*w1*T+16*b*q*T := by ring
    have e10 : 4*b*q=4*(b*q) := by ring
    rw [e1,e2]
    omega
  exact Nat.le_of_mul_le_mul_left (Nat.le_of_mul_le_mul_left goal hb) hq

/-- The non-productive part of a star's base is `O(T²)`. -/
theorem rest_arith {T Tb x c b cs0 sv M0 W Kr wrapC cr crc K0 d Lc al fl sortT dxv lq ll gq gl : Nat} (hT1 : 1≤T) (hTb : Tb≤T) (hTb1 : 1≤Tb)
    (hc : b*b*c≤T*T) (hbx : b*x≤T) (hb : 1≤b) (hs : sortT≤18*al*(T*T)+fl*T)
    (hdx : dxv+d*crc*T+gq*(T*T)≤d*cr*(T*T)+gl*T)
    (hK : K0=sv+lq+2*(b-1)*Kr+wrapC+(d*cr-gq)+18*al+
      Ledger.cdiv (linC b cs0 M0 W Kr Lc fl (ll+gl)-d*crc) Tb) :
    b*b*(sv*c)+(lq*(T*T)+ll*T)+b*b*(2*(M0+2+2*T))+Kr*x*(b*b+2*b*(b-1)*T+Lc)+(cs0+4*T)*(b*b)+
      wrapC*(T*T)+dxv+2*(W+M0)+sortT≤K0*(T*T) := by
  have hTT : T≤T*T := Nat.le_mul_of_pos_right T hT1
  have t1 : b*b*(sv*c)≤sv*(T*T) := by
    rw [Nat.mul_left_comm]; exact Nat.mul_le_mul_left _ hc
  have t4a : Kr*x*(2*b*(b-1)*T)≤2*(b-1)*Kr*(T*T) := by
    calc Kr*x*(2*b*(b-1)*T)=2*(b-1)*Kr*((b*x)*T) := by ring
      _≤2*(b-1)*Kr*(T*T) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hbx)
  -- the linear terms
  have t4b : Kr*x*(b*b+Lc)≤Ledger.cdiv (Kr*(b*b+Lc)) b*T := by
    have h1 : b*(Kr*x*(b*b+Lc))≤b*(Ledger.cdiv (Kr*(b*b+Lc)) b*T) := by
      calc b*(Kr*x*(b*b+Lc))=Kr*(b*b+Lc)*(b*x) := by ring
        _≤Kr*(b*b+Lc)*T := Nat.mul_le_mul_left _ hbx
        _≤b*Ledger.cdiv (Kr*(b*b+Lc)) b*T := Nat.mul_le_mul_right _ (Ledger.le_mul_cdiv hb)
        _=_ := by ring
    exact Nat.le_of_mul_le_mul_left h1 hb
  have lin : b*b*(2*(M0+2+2*T))+Kr*x*(b*b+Lc)+(cs0+4*T)*(b*b)+2*(W+M0)+fl*T+ll*T+gl*T≤
      linC b cs0 M0 W Kr Lc fl (ll+gl)*T := by
    unfold linC
    have c1 : b*b*(2*M0+4)≤b*b*(2*M0+4)*T := Nat.le_mul_of_pos_right _ hT1
    have c2 : b*b*cs0≤b*b*cs0*T := Nat.le_mul_of_pos_right _ hT1
    have c3 : 2*(W+M0)≤2*(W+M0)*T := Nat.le_mul_of_pos_right _ hT1
    have e1 : b*b*(2*(M0+2+2*T))=b*b*(2*M0+4)+4*(b*b*T) := by ring
    have e2 : (cs0+4*T)*(b*b)=b*b*cs0+4*(b*b*T) := by ring
    have e3 : (b*b*(2*M0+4)+8*(b*b)+Ledger.cdiv (Kr*(b*b+Lc)) b+b*b*cs0+2*(W+M0)+fl+(ll+gl))*T=
        b*b*(2*M0+4)*T+8*(b*b*T)+Ledger.cdiv (Kr*(b*b+Lc)) b*T+b*b*cs0*T+2*(W+M0)*T+fl*T+ll*T+gl*T := by
      ring
    omega
  have lin2 : (linC b cs0 M0 W Kr Lc fl (ll+gl)-d*crc)*T≤Ledger.cdiv (linC b cs0 M0 W Kr Lc fl (ll+gl)-d*crc) Tb*(T*T) := by
    calc (linC b cs0 M0 W Kr Lc fl (ll+gl)-d*crc)*T≤Tb*Ledger.cdiv (linC b cs0 M0 W Kr Lc fl (ll+gl)-d*crc) Tb*T :=
          Nat.mul_le_mul_right _ (Ledger.le_mul_cdiv hTb1)
      _≤T*Ledger.cdiv (linC b cs0 M0 W Kr Lc fl (ll+gl)-d*crc) Tb*T :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hTb)
      _=_ := by ring
  have lin3 : linC b cs0 M0 W Kr Lc fl (ll+gl)*T≤(linC b cs0 M0 W Kr Lc fl (ll+gl)-d*crc)*T+d*crc*T := by
    rw [←Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
  have e4 : Kr*x*(b*b+2*b*(b-1)*T+Lc)=Kr*x*(2*b*(b-1)*T)+Kr*x*(b*b+Lc) := by ring
  have esub : d*cr*(T*T)≤(d*cr-gq)*(T*T)+gq*(T*T) := by rw [Nat.sub_mul]; omega
  have e : K0*(T*T)=sv*(T*T)+lq*(T*T)+2*(b-1)*Kr*(T*T)+wrapC*(T*T)+
      (d*cr-gq)*(T*T)+18*al*(T*T)+Ledger.cdiv (linC b cs0 M0 W Kr Lc fl (ll+gl)-d*crc) Tb*(T*T) := by
    rw [hK]; ring
  omega

/-- The gain of one slot row of static margin cells, per column: over the body
rows `[2W+4+ρx, W+4+ρx+x)`, `Σ (16T - 12r - (12M0+12)) ≥ (16b-12ρ-6)x² - λx`. -/
theorem rows_gain (T x W M0 b ρ : Nat) (hx : W≤x) (hT : b*x+M0≤T) (hρ : ρ<b) (hWM : W+4≤M0)
    (hbig : 12*T+(12*M0+12)≤16*T) :
    (16*b-12*ρ-6)*(x*x)≤∑ r ∈ Ico (2*W+4+ρ*x) (W+4+ρ*x+x), (16*T-12*r-(12*M0+12))+
      ((16*b-12*ρ-6)*W+(18*W+54-4*M0))*x := by
  have hρx : (ρ+1)*x≤b*x := Nat.mul_le_mul_right _ hρ
  rw [Nat.add_mul,Nat.one_mul] at hρx
  set lo := 2*W+4+ρ*x with hlo
  set L := x-W with hL
  have hhi : W+4+ρ*x+x=lo+L := by omega
  rw [hhi,sum_Ico_eq_sum_range,Nat.add_sub_cancel_left]
  -- each term is `C - 12 k` with no truncation
  set C := 16*T-12*lo-(12*M0+12) with hC
  have term : ∀ k∈range L, 16*T-12*(lo+k)-(12*M0+12)=C-12*k := by
    intro k hk; have := mem_range.mp hk; omega
  rw [sum_congr rfl term]
  have hCk : ∀ k∈range L, 12*k≤C := by intro k hk; have := mem_range.mp hk; omega
  have split : ∑ k ∈ range L, (C-12*k)+12*∑ k ∈ range L, k=L*C := by
    rw [mul_sum,←sum_add_distrib,sum_congr rfl (fun k hk => Nat.sub_add_cancel (hCk k hk))]
    simp
  have tri := sum_range_id_mul_two L
  generalize ∑ k ∈ range L, (C-12*k)=S at split ⊢
  generalize hsk : ∑ k ∈ range L, k=sk at split tri
  -- the polynomial bound, in ℤ
  have hA : 12*ρ+6≤16*b := by omega
  have hCge : (16*b-12*ρ)*x+4*M0≤C+24*W+60 := by
    have : 16*(b*x)+16*M0≤16*T := by omega
    have e : (16*b-12*ρ)*x=16*(b*x)-12*(ρ*x) := by
      rw [Nat.sub_mul]; ring_nf
    omega
  have tri' : 2*(sk:ℤ)=((x:ℤ)-W)*((x:ℤ)-W-1) := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · have : x=W := by omega
      rw [h0] at tri; simp at tri; rw [tri,this]; push_cast; ring
    · have e : ((L-1 : Nat) : ℤ)=(x:ℤ)-W-1 := by omega
      have := congrArg (fun m : Nat => (m:ℤ)) tri
      push_cast at this; rw [e,hL] at this; push_cast [Nat.cast_sub hx] at this; linarith
  have split' : (S:ℤ)+12*sk=((x:ℤ)-W)*C := by
    have := congrArg (fun m : Nat => (m:ℤ)) split
    push_cast [hL,Nat.cast_sub hx] at this; linarith
  have hCge' : ((16*b:ℤ)-12*ρ)*x+4*M0≤C+24*W+60 := by
    have := congrArg (fun m : Nat => (m:ℤ)) (rfl : (16*b-12*ρ)*x+4*M0=(16*b-12*ρ)*x+4*M0)
    have h2 : ((16*b-12*ρ : Nat) : ℤ)=16*b-12*ρ := by omega
    have := (Nat.cast_le (α:=ℤ)).mpr hCge
    push_cast [h2] at this; linarith
  have hgoal : (((16*b-12*ρ-6)*(x*x) : Nat) : ℤ)≤(S:ℤ)+((((16*b-12*ρ-6)*W+(18*W+54-4*M0))*x : Nat) : ℤ) := by
    have h2 : ((16*b-12*ρ-6 : Nat) : ℤ)=16*b-12*ρ-6 := by omega
    have h3 : ((18*W+54-4*M0 : Nat) : ℤ)≥18*W+54-4*M0 := by omega
    have h3' : (0:ℤ)≤((18*W+54-4*M0 : Nat) : ℤ) := by positivity
    push_cast [h2]
    have p4 : ((18*W+54-4*M0 : Nat) : ℤ)*(x-W)≥(18*W+54-4*M0)*(x-W) :=
      mul_le_mul_of_nonneg_right h3 (sub_nonneg.mpr (by exact_mod_cast hx))
    have p5 : (0:ℤ)≤((18*W+54-4*M0 : Nat) : ℤ)*W := mul_nonneg h3' (by positivity)
    have hxW : (0:ℤ)≤x-W := sub_nonneg.mpr (by exact_mod_cast hx)
    have c1 : ((x:ℤ)-W)*(((16*b:ℤ)-12*ρ)*x+4*M0)≤((x:ℤ)-W)*(C+24*W+60) :=
      mul_le_mul_of_nonneg_left hCge' hxW
    have p1 : (0:ℤ)≤(12*ρ+6)*W*x := by positivity
    have p2 : (0:ℤ)≤4*M0*(x-W) := mul_nonneg (by positivity) hxW
    have p3 : (0:ℤ)≤(18*W+54)*W := by positivity
    nlinarith
  exact_mod_cast hgoal

/-- Rows and columns of a `b × r` grid of slots: `Σ (row + col)`. -/
theorem sum_divmod (b : Nat) : ∀ r, ∑ j ∈ range (b*r), (j/b+j%b)=b*(∑ i ∈ range r, i)+r*(∑ x ∈ range b, x) := by
  intro r
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.mul_succ,sum_range_add,ih,sum_range_succ]
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    have inner : ∑ x ∈ range b, ((b*r+x)/b+(b*r+x)%b)=∑ x ∈ range b, (r+x) := by
      apply sum_congr rfl; intro x hx
      have hx' := mem_range.mp hx
      rw [Nat.add_comm (b*r) x,Nat.add_mul_div_left _ _ hb,Nat.add_mul_mod_self_left,
        Nat.div_eq_of_lt hx',Nat.mod_eq_of_lt hx']
      omega
    rw [inner,sum_add_distrib,sum_const,card_range,smul_eq_mul]
    ring

theorem sum_divmod_sq (b : Nat) : ∑ j ∈ range (b*b), (j/b+j%b)=b*(b*(b-1)) := by
  have h := sum_divmod b b
  have g := sum_range_id_mul_two b
  have : 2*∑ j ∈ range (b*b), (j/b+j%b)=2*(b*(b*(b-1))) := by rw [h]; nlinarith
  omega

/-! ### Star geometry -/

section Star
variable {T : Nat} [NeZero T] (hT : k.Tbig≤T) (cs : Nat) (hcs : 2*cs+1<k.W) (q : Placement T n)
  [NeZero (k.child T)] (sub : k.Sub G T) (hg : k.GoalOK G q)

local notation "P" => k.params T cs hT hcs
local notation "S" => k.starSpec hT cs hcs q sub hg

theorem W_le_M0 : k.W≤k.M0 := by have := k.bb; unfold W M0; omega

theorem S_h (j : Fin (P).J) : (S).L.hcost j≤12*(P).a j+24 := by
  change 2*(2*(1+(P).a j)+4*max 1 ((P).a j)+6)+4+4≤_
  have := ((P).bounds j.isLt).a_ge
  omega

theorem S_pm : (S).pm=T := rfl

theorem S_wcost : (S).wcost≤12*k.W+34 := by
  change 2*(2*(((P).W+1-2*cs)+1)+4*max ((P).W+1-2*cs) 1+6)+4+2≤_
  have : (P).W=k.W := rfl
  have : 1≤k.W := by have := k.b_two; unfold W; omega
  omega

theorem S_dcost : (S).dcost≤k.dk*T := by
  change Entry.dcost q (P).fit≤_
  have := Entry.dcost_le q (P).fit
  have : (P).W=k.W := rfl
  have h := Ledger.le_mul_cdiv (x:=24*k.W+170) (q:=k.Tbig) k.Tbig_pos
  have h2 : k.Tbig*Ledger.cdiv (24*k.W+170) k.Tbig≤T*Ledger.cdiv (24*k.W+170) k.Tbig :=
    Nat.mul_le_mul_right _ hT
  unfold dk
  rw [Nat.add_mul,Nat.mul_comm (Ledger.cdiv _ _) T]
  omega

/-- The sort weight of a body cell at `(r,c)`. -/
theorem S_fw_loc {r c : Nat} (hr : r<T) (hc : c<T) : (S).fw (q.loc r c)=(3*(Cycle3.tw (r-2*cs) c+2)+3)/4 :=
  (P).sortW_loc q hr hc

theorem S_access (j : Fin (P).J) : ((S).L.accessTail j).length≤(P).a j := by
  change ((P).accessTail q j).length≤_
  unfold Params.accessTail
  simp only [List.length_append,Seg.length_mk]
  have := ((P).bounds j.isLt).a_ge
  omega

theorem S_a_le (j : Fin (P).J) : (P).a j+2≤k.M0 := by
  have := ((P).bounds j.isLt).a_eq
  have : (P).M0=k.M0 := rfl
  omega

theorem S_conn : (S).connTail.length≤k.W+1 := by
  change ((P).connTail q).length≤_
  unfold Params.connTail
  simp only [List.length_append,Seg.length_mk]
  have : (P).W=k.W := rfl
  omega


theorem S_wrap : (S).wrapCost≤k.wrapC := by
  unfold StarSpec.wrapCost wrapC
  have := k.S_wcost hT cs hcs q sub hg
  have := k.S_conn hT cs hcs q sub hg
  omega

/-- A late request: a direct exchange and a wrapped service, `≤ 16T + dc`. -/
theorem S_dwcost : (S).dxCost+(S).wrapCost≤16*T+k.dc := by
  unfold StarSpec.dxCost
  have hd : (S).dcost≤16*T+24*k.W+170 := by
    change Entry.dcost q (P).fit≤_
    have := Entry.dcost_le q (P).fit
    have : (P).W=k.W := rfl
    omega
  have hw := k.S_wrap hT cs hcs q sub hg
  unfold dc
  omega

/-- Lane lengths: each at most `2T`, together at most twice the corner
offset of the slot plus `4b`. -/
theorem S_lanes (j : Fin (P).J) :
    (S).elen j≤2*T ∧ (S).dlen j≤2*T ∧
      (S).elen j+(S).dlen j≤2*((P).R ((P).rowOf j)+(P).C ((P).colOf j))+4*k.b := by
  have hE : (S).elen j=((P).y j-(P).W-1)+((P).f j-(P).a j-1)+1 := by
    change ((P).exportLane q j++[(P).z q j]).length=_
    unfold Params.exportLane
    simp only [List.length_append,Seg.length_mk,List.length_singleton]
  have hD : (S).dlen j=1+(((P).f j-(P).a j-1)+((P).y j-(P).W-3)) := by
    change ((P).e q j :: (P).deliveryLane q j).length=_
    unfold Params.deliveryLane
    simp only [List.length_cons,List.length_append,Seg.length_mk]
    omega
  have hb := (P).bounds j.isLt
  have := hb.a_ge; have := hb.y_ge; have := hb.y_band; have := hb.f_ge; have := hb.f_le
  have := hb.R_le; have := hb.a_eq
  have hc := (P).colOf_lt j
  have hy : (P).y j=(P).R ((P).rowOf j)+2*(P).colOf j := rfl
  have hf : (P).f j=(P).C ((P).colOf j) := rfl
  have e1 : (P).T=T := rfl
  have e2 : (P).b=k.b := rfl
  rw [hE,hD]
  omega

/-- The corner offset of slot `j`. -/
def δ (j : Fin (P).J) : Nat := (P).R ((P).rowOf j)+(P).C ((P).colOf j)

/-- The two lanes exactly: down from the hub to the band row, right from the
margin column to the slot corner. -/
theorem S_lanes_eq (j : Fin (P).J) :
    (S).elen j+(S).dlen j+2*k.W+2*(P).a j+4=2*k.δ hT cs hcs j+4*(P).colOf j := by
  have hE : (S).elen j=((P).y j-(P).W-1)+((P).f j-(P).a j-1)+1 := by
    change ((P).exportLane q j++[(P).z q j]).length=_
    unfold Params.exportLane
    simp only [List.length_append,Seg.length_mk,List.length_singleton]
  have hD : (S).dlen j=1+(((P).f j-(P).a j-1)+((P).y j-(P).W-3)) := by
    change ((P).e q j :: (P).deliveryLane q j).length=_
    unfold Params.deliveryLane
    simp only [List.length_cons,List.length_append,Seg.length_mk]
    omega
  have hb := (P).bounds j.isLt
  have := hb.a_ge; have := hb.y_ge; have := hb.y_band; have := hb.f_ge; have := hb.f_le
  have := hb.R_le; have := hb.a_eq
  have hy : (P).y j=(P).R ((P).rowOf j)+2*(P).colOf j := rfl
  have hf : (P).f j=(P).C ((P).colOf j) := rfl
  have e2 : (P).W=k.W := rfl
  have hδ : k.δ hT cs hcs j=(P).R ((P).rowOf j)+(P).C ((P).colOf j) := rfl
  rw [hE,hD,hδ]
  omega

/-- A child's distance sum, seen from the parent corner, gains its corner
offset once per cell. -/
theorem dsum_kid (j : Fin (P).J) :
    dsum q (k.kids hT cs hcs q sub hg j).R.cells=
      dsum (k.slot hT cs hcs q j) (k.kids hT cs hcs q sub hg j).R.cells+
        (k.kids hT cs hcs q sub hg j).R.cells.card*k.δ hT cs hcs j := by
  rw [(k.kids hT cs hcs q sub hg j).cells_eq]
  unfold dsum bodyCells
  rw [sum_map,sum_map,card_map,←smul_eq_mul,←sum_const,←sum_add_distrib]
  apply sum_congr rfl
  intro y _
  have hc := k.child_ge hT
  have := k.Tmin_six
  have h0 : 0<k.child T := by omega
  have l1 := y.1.isLt; have l2 := y.2.isLt
  have hb := (P).bounds j.isLt
  have := hb.R_le; have := hb.f_le
  have hf : (P).f j=(P).C ((P).colOf j) := rfl
  have e2 : (P).T'=k.child T := rfl
  have e1 : (P).T=T := rfl
  rw [←(k.slot hT cs hcs q j).loc_eq l1 l2,k.slot_loc hT cs hcs q j l1 l2,k.slot_loc hT cs hcs q j h0 h0,
    q.loc_dist (by omega) (by omega) (by omega) (by omega),
    q.loc_dist (by omega) (by omega) (by omega) (by omega)]
  unfold δ
  simp only [Nat.dist]
  omega

theorem dsum_kids : ∑ j, (dsum (k.slot hT cs hcs q j) (k.kids hT cs hcs q sub hg j).R.cells+
      (k.kids hT cs hcs q sub hg j).R.cells.card*k.δ hT cs hcs j)≤dsum q (S).frame.cells := by
  simp_rw [←k.dsum_kid hT cs hcs q sub hg]
  unfold dsum
  rw [←sum_biUnion]
  · apply sum_le_sum_of_subset
    rw [StarSpec.frame_cells]
    intro x hx
    simp only [mem_union]
    exact Or.inl (Or.inl hx)
  · intro j _ j' _ h
    exact (S).L.children_disjoint j j' h

/-- The reserve cells of the star: their distances, together with the
children's, fit in the body; only the children's spares are counted twice. -/
theorem S_resid_d : ∑ x∈(S).resid, gridDistance (q.loc 0 0) x+∑ j, dsum q (k.kids hT cs hcs q sub hg j).R.cells≤
    dsum q (S).frame.cells+(S).childSpare.card*(2*T) := by
  classical
  set d : Cell n → Nat := fun x => gridDistance (q.loc 0 0) x
  have hcellsB : (S).frame.cells=k.bodyCells q := (k.star hT cs hcs q sub hg).cells_eq
  have sub1 : (S).resid⊆((S).frame.cells\(S).childCells)∪(S).childSpare := by
    intro x hx
    obtain ⟨hc,hh⟩ := (S).mem_resid.mp hx
    by_cases hU : x∈(S).childCells
    · apply mem_union_right
      simp only [StarSpec.childCells,mem_biUnion,mem_univ,true_and] at hU
      obtain ⟨j,hj⟩ := hU
      simp only [Frame.cells,mem_union] at hj
      simp only [StarSpec.childSpare,mem_biUnion,mem_univ,true_and]
      refine ⟨j,?_⟩
      rcases hj with (hj | hj) | hj
      · exact absurd (by simp only [StarSpec.homeCells,mem_biUnion,mem_univ,true_and,mem_union]; exact ⟨j,Or.inl hj⟩) hh
      · exact absurd (by simp only [StarSpec.homeCells,mem_biUnion,mem_univ,true_and,mem_union]; exact ⟨j,Or.inr hj⟩) hh
      · exact hj
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hc,hU⟩)
  have s1 : ∑ x∈(S).resid, d x≤∑ x∈((S).frame.cells\(S).childCells)∪(S).childSpare, d x :=
    sum_le_sum_of_subset sub1
  have s2 := sum_union_inter (s₁:=(S).frame.cells\(S).childCells) (s₂:=(S).childSpare) (f:=d)
  have hU : (S).childCells⊆(S).frame.cells := by
    rw [StarSpec.frame_cells]; intro x hx; simp [hx]
  have s3 := sum_sdiff (f:=d) hU
  have s4 : ∑ x∈(S).childCells, d x=∑ j, dsum q (k.kids hT cs hcs q sub hg j).R.cells := by
    unfold StarSpec.childCells dsum
    rw [sum_biUnion]
    · rfl
    · intro j _ j' _ h
      exact (S).L.children_disjoint j j' h
  have s5 : ∑ x∈(S).childSpare, d x≤(S).childSpare.card*(2*T) := by
    have := sum_le_card_nsmul (S).childSpare d (2*T) (fun x hx => by
      have hb : x∈k.bodyCells q := by
        rw [←hcellsB,StarSpec.frame_cells]
        have := (S).childSpare_sub hx
        simp [this]
      exact k.dist_body_le q hb)
    simpa using this
  have e1 : dsum q (S).frame.cells=∑ x∈(S).frame.cells, d x := rfl
  change ∑ x∈(S).resid, d x+_≤_
  rw [e1,←s4]
  omega

theorem kid_pop (j : Fin (P).J) : (S).pop j+6=(k.child T-k.W)*k.child T := by
  have h1 := Frame.cells_card (k.kids hT cs hcs q sub hg j).R.toFrame
  have h2 := (k.kids hT cs hcs q sub hg j).spare6
  have h3 := (k.kids hT cs hcs q sub hg j).cells_eq
  have h4 := k.card_bodyCells (k.slot hT cs hcs q j)
  change (k.kids hT cs hcs q sub hg j).R.M+(k.kids hT cs hcs q sub hg j).R.r+6=_
  rw [←h4,←h3]
  rw [h1]
  rw [h2]

theorem S_r' : (S).frame.r+k.crc≤k.cr*T := by
  have h1 := Frame.cells_card (S).frame
  have h2 : (S).frame.cells=k.bodyCells q := (k.star hT cs hcs q sub hg).cells_eq
  have h3 := (S).M_eq
  have hg6 : (S).frame.g=6 := (P).markers_card q
  rw [h2,k.card_bodyCells,h3,hg6] at h1
  have hp : ∀ j, (S).pop j=(k.child T-k.W)*k.child T-6 := by
    intro j; have := k.kid_pop hT cs hcs q sub hg j; omega
  simp only [hp,sum_const,card_univ,Fintype.card_fin,smul_eq_mul] at h1
  generalize (S).frame.r=r at h1 ⊢
  have hJ : (P).J=k.b*k.b := rfl
  rw [hJ] at h1
  have hc := k.child_ge hT
  have hW := k.W_lt_Tmin
  have h6 := k.Tmin_six
  have hc6 : 6≤(k.child T-k.W)*k.child T := by
    have : 1≤k.child T-k.W := by omega
    nlinarith
  have hM := k.M0_le hT
  have hmul := k.child_mul T
  have hup := k.child_upper' hT
  have hb := k.b_pos
  have hTb : k.b*k.Tmin≤k.b*k.child T := Nat.mul_le_mul_left _ hc
  have hbW : k.b*k.W≤k.b*k.Tmin := Nat.mul_le_mul_left _ (by omega)
  have hroom : (T-k.b*k.child T)+(k.M0+k.b-1)+k.b*k.W≤2*T := by
    have : k.b≤k.b*k.Tmin := Nat.le_mul_of_pos_right _ (by omega)
    unfold Tbig at hT; omega
  have key := r_arith (T:=T) (x:=k.child T) (r:=r) (b:=k.b) (W:=k.W) (D:=T-k.b*k.child T)
    (D':=k.M0+k.b-1) hb (by unfold Tbig at hT; omega) (by omega) (by omega)
    hroom (by omega) (by
      rw [Nat.mul_sub,Nat.mul_comm (k.b*k.b) 6] at h1
      have : 6*(k.b*k.b)≤k.b*k.b*((k.child T-k.W)*k.child T) := by
        rw [Nat.mul_comm 6]; exact Nat.mul_le_mul_left _ hc6
      omega)
  have big : 6*(k.b*k.b)≤(k.M0+k.b-1)*(k.M0+k.b-1+k.b*k.W)+6 := by
    have e1 : k.b*k.b≤k.M0 := by unfold M0; omega
    have e2 : 6≤k.M0 := by unfold M0; have := k.bb; have := k.b_two; omega
    have e3 : 6*k.M0≤k.M0*k.M0 := Nat.mul_le_mul_right _ e2
    have e4 : k.M0*k.M0≤(k.M0+k.b-1)*(k.M0+k.b-1+k.b*k.W) := Nat.mul_le_mul (by omega) (by omega)
    omega
  unfold cr crc
  omega

theorem S_stat_card : (S).stat.card≤(S).frame.r := by
  have : (S).stat⊆(S).own∪(S).childSpare := fun x hx => mem_union_left _ ((S).stat_own x hx)
  exact card_le_card this

theorem S_dw_le {x : Cell n} (hx : x∈(S).stat) : (S).dw x≤(S).dxCost := by
  obtain ⟨r,c,hr,hc,_,rfl⟩ := ((P).mem_statF q).mp hx
  exact ((P).dwW_loc q (r:=r) (c:=c) (by exact hr) (by exact hc)).trans_le (Entry.dw_le q (P).fit hr hc)

/-- Static margin cells charged by position save `gq·T²` up to a linear term. -/
theorem S_stat_gain : k.gq*(T*T)≤∑ x∈(S).stat, ((S).dxCost-(S).dw x)+k.gl*T := by
  classical
  have hc := k.child_ge hT
  have hW := k.W_lt_Tmin
  have hmul := k.child_mul T
  have hM := k.M0_le hT
  have hup := k.child_upper' hT
  have hb := k.b_two
  have hbb := k.bb
  have hWM := k.W_M0
  have hl := k.Tmin_lane
  have hTb : 3*k.M0+3≤T := by
    have : 2*k.Tmin≤k.b*k.Tmin := Nat.mul_le_mul_right _ hb
    unfold Tbig at hT; unfold M0 at *; omega
  set x := k.child T with hxdef
  have eW : (P).W=k.W := rfl
  have eM : (P).M0=k.M0 := rfl
  have eT : (P).T'=x := rfl
  have eb : (P).b=k.b := rfl
  -- the static cells by their coordinates
  set U := ((range T)×ˢ(range T)).filter (fun rc => (P).statP rc.1 rc.2) with hU
  have hstat : (S).stat=U.image (fun rc => q.loc rc.1 rc.2) := rfl
  have inj : ∀ u∈U, ∀ v∈U, q.loc u.1 u.2=q.loc v.1 v.2 → u=v := by
    rintro ⟨r,c⟩ hu ⟨r',c'⟩ hv e
    simp only [hU,mem_filter,mem_product,mem_range] at hu hv
    obtain ⟨rfl,rfl⟩ := (P).coords q hu.1.1 hu.1.2 hv.1.1 hv.1.2 e
    rfl
  rw [hstat,sum_image inj]
  -- rectangles of static cells: the body rows of each slot row, its static columns
  let cols : Nat → Finset Nat := fun ρ => range 4∪Ico (k.M0-2*k.b*(ρ+1)) k.M0
  let rows : Nat → Finset Nat := fun ρ => Ico (2*k.W+4+ρ*x) (k.W+4+ρ*x+x)
  set V := (range k.b).biUnion (fun ρ => rows ρ×ˢcols ρ) with hV
  have hρx {ρ : Nat} (hρ : ρ<k.b) : ρ*x+x≤k.b*x := by
    have : (ρ+1)*x≤k.b*x := Nat.mul_le_mul_right _ hρ
    rw [Nat.add_mul,Nat.one_mul] at this; exact this
  have hcol {ρ : Nat} (hρ : ρ<k.b) : 2*k.b*(ρ+1)+4≤k.M0 := by
    have : k.b*(ρ+1)≤k.b*k.b := Nat.mul_le_mul_left _ hρ
    have e : 2*k.b*(ρ+1)=2*(k.b*(ρ+1)) := by ring
    unfold M0; omega
  have VU : V⊆U := by
    rintro ⟨r,c⟩ hv
    simp only [hV,mem_biUnion,mem_range,mem_product,rows,cols,mem_union,mem_Ico] at hv
    obtain ⟨ρ,hρ,⟨h1,h2⟩,hcc⟩ := hv
    have := hρx hρ; have := hcol hρ
    simp only [hU,mem_filter,mem_product,mem_range]
    refine ⟨⟨by omega,by rcases hcc with h | h <;> omega⟩,ρ,by rw [eb]; exact hρ,?_,?_,?_,?_⟩
    · show (P).W+4+ρ*(P).T'+(P).W≤r; rw [eW,eT]; omega
    · show r<(P).W+4+ρ*(P).T'+(P).T'; rw [eW,eT]; omega
    · rw [eM]; rcases hcc with h | h <;> omega
    · rw [eM,eb]; rcases hcc with h | h
      · left; omega
      · right; omega
  refine le_trans ?_ (Nat.add_le_add_right (sum_le_sum_of_subset VU) _)
  -- each static cell saves `16T - 12r - (12M0+12)`
  set H : Nat → Nat := fun r => 16*T-12*r-(12*k.M0+12) with hH
  have cell : ∀ u∈V, H u.1≤(S).dxCost-(S).dw (q.loc u.1 u.2) := by
    rintro ⟨r,c⟩ hv
    simp only [hV,mem_biUnion,mem_range,mem_product,rows,cols,mem_union,mem_Ico] at hv
    obtain ⟨ρ,hρ,⟨h1,h2⟩,hcc⟩ := hv
    have := hρx hρ; have := hcol hρ
    have hcT : c<k.M0 := by rcases hcc with h | h <;> omega
    have hcs2 : 2*cs≤r := by have : 2*cs+1<k.W := hcs; omega
    have hrT : r<T := by omega
    have hcT' : c<T := by omega
    have key : (S).dw (q.loc r c)+16*T≤(S).dxCost+12*r+12*c+12 := by
      have g := Entry.dw_gain q (P).fit (r:=r) (c:=c) hcs2 hrT
      exact (congrArg (·+16*T) ((P).dwW_loc q (r:=r) (c:=c) (by exact hrT) (by exact hcT'))).trans_le g
    simp only [hH]
    omega
  refine le_trans ?_ (Nat.add_le_add_right (sum_le_sum cell) _)
  -- by slot rows
  have disj : ∀ ρ∈range k.b, ∀ ρ'∈range k.b, ρ≠ρ' → Disjoint (rows ρ×ˢcols ρ) (rows ρ'×ˢcols ρ') := by
    intro ρ hρ ρ' hρ' hne
    rw [disjoint_left]
    rintro ⟨r,c⟩ h1 h2
    simp only [mem_product,rows,mem_Ico] at h1 h2
    rcases Nat.lt_or_gt_of_ne hne with hl | hl
    · have : (ρ+1)*x≤ρ'*x := Nat.mul_le_mul_right _ hl
      rw [Nat.add_mul,Nat.one_mul] at this; omega
    · have : (ρ'+1)*x≤ρ*x := Nat.mul_le_mul_right _ hl
      rw [Nat.add_mul,Nat.one_mul] at this; omega
  rw [sum_biUnion disj]
  have perρ : ∀ ρ∈range k.b, ∑ u ∈ rows ρ×ˢcols ρ, H u.1=k.sw ρ*∑ r ∈ rows ρ, H r := by
    intro ρ hρ
    have := hcol (mem_range.mp hρ)
    have hcard : (cols ρ).card=k.sw ρ := by
      show (range 4∪Ico (k.M0-2*k.b*(ρ+1)) k.M0).card=_
      rw [card_union_of_disjoint (by rw [disjoint_left]; intro a ha hb; simp at ha hb; omega),card_range,
        Nat.card_Ico]
      unfold sw; omega
    rw [sum_product,Finset.mul_sum]
    apply sum_congr rfl; intro r _
    simp only [sum_const,smul_eq_mul]
    rw [hcard,Nat.mul_comm]
  rw [sum_congr rfl perρ]
  -- the gain of each slot row
  set lam : Nat → Nat := fun ρ => (16*k.b-12*ρ-6)*k.W+(18*k.W+54-4*k.M0) with hlam
  have rowρ : ∀ ρ∈range k.b, k.sw ρ*((16*k.b-12*ρ-6)*(x*x))≤
      k.sw ρ*(∑ r ∈ rows ρ, H r)+k.sw ρ*lam ρ*x := by
    intro ρ hρ
    rw [Nat.mul_assoc,←Nat.mul_add]
    apply Nat.mul_le_mul_left
    exact rows_gain T x k.W k.M0 k.b ρ (by omega) (by omega) (mem_range.mp hρ) hWM (by omega)
  have sumρ := sum_le_sum rowρ
  rw [sum_add_distrib,←sum_mul] at sumρ
  have hSA : ∑ ρ ∈ range k.b, k.sw ρ*((16*k.b-12*ρ-6)*(x*x))=
      (∑ ρ ∈ range k.b, k.sw ρ*(16*k.b-12*ρ-6))*(x*x) := by
    rw [sum_mul]; apply sum_congr rfl; intro ρ _; ring
  rw [hSA] at sumρ
  -- `gq·T² ≤ SA·x² + 2 gq (M0+b) T`
  set SA := ∑ ρ ∈ range k.b, k.sw ρ*(16*k.b-12*ρ-6) with hSAdef
  have hgq : k.gq*(k.b*k.b)≤SA := Nat.div_mul_le_self _ _
  set D := T-k.b*x with hD
  have hTD : T=k.b*x+D := by omega
  have hD1 : D≤k.M0+k.b := by omega
  have hsq : k.gq*(T*T)≤SA*(x*x)+2*k.gq*(k.M0+k.b)*T := by
    have e : k.gq*(T*T)=k.gq*(k.b*k.b)*(x*x)+k.gq*(D*(2*(k.b*x)+D)) := by rw [hTD]; ring
    have h1 : k.gq*(k.b*k.b)*(x*x)≤SA*(x*x) := Nat.mul_le_mul_right _ hgq
    have h2 : D*(2*(k.b*x)+D)≤(k.M0+k.b)*(2*T) := Nat.mul_le_mul hD1 (by omega)
    have h3 : k.gq*(D*(2*(k.b*x)+D))≤k.gq*((k.M0+k.b)*(2*T)) := Nat.mul_le_mul_left _ h2
    have e2 : k.gq*((k.M0+k.b)*(2*T))=2*k.gq*(k.M0+k.b)*T := by ring
    omega
  have hx1 : x≤T := by have : x≤k.b*x := Nat.le_mul_of_pos_left x (by omega); omega
  have hlin : (∑ ρ ∈ range k.b, k.sw ρ*lam ρ)*x≤(∑ ρ ∈ range k.b, k.sw ρ*lam ρ)*T :=
    Nat.mul_le_mul_left _ hx1
  unfold gl
  have e3 : ((∑ ρ ∈ range k.b, k.sw ρ*((16*k.b-12*ρ-6)*k.W+(18*k.W+54-4*k.M0)))+2*k.gq*(k.M0+k.b))*T=
      (∑ ρ ∈ range k.b, k.sw ρ*lam ρ)*T+2*k.gq*(k.M0+k.b)*T := by rw [Nat.add_mul]
  omega

theorem S_r : (S).frame.r≤k.cr*T := by
  have := k.S_r' hT cs hcs q sub hg; omega

/-- A service cost is at most `cs0` plus the two lane lengths. -/
theorem S_sc' (j : Fin (P).J) : (S).serviceCost j≤(26*(P).a j+50)+((S).elen j+(S).dlen j) := by
  unfold StarSpec.serviceCost
  have := k.S_access hT cs hcs q sub hg j
  have := k.S_h hT cs hcs q sub hg j
  change _+_+(S).elen j+(S).dlen j+2≤_
  omega

theorem S_sc (j : Fin (P).J) : (S).serviceCost j≤k.cs0+((S).elen j+(S).dlen j) := by
  have := k.S_sc' hT cs hcs q sub hg j
  have := k.S_a_le hT cs hcs j
  unfold cs0
  omega

/-- The spokes' margin columns add up: `Σ a_j = J (M0 - J - 1)`. -/
theorem S_a_sum : ∑ j : Fin (P).J, (P).a j=k.b*k.b*(k.M0-k.b*k.b-1) := by
  have hJ : (P).J=k.b*k.b := rfl
  have hM : (P).M0=k.M0 := rfl
  have e : ∀ j : Fin (P).J, (P).a j=k.M0-2*(j.val+1) := fun j => by unfold Params.a; rw [hM]
  rw [sum_congr rfl (fun j _ => e j),Fin.sum_univ_eq_sum_range (fun j => k.M0-2*(j+1)) (P).J,hJ]
  have hM0 : k.M0=2*(k.b*k.b)+4 := rfl
  have h1 : ∑ j∈range (k.b*k.b), (k.M0-2*(j+1))+∑ j∈range (k.b*k.b), 2*(j+1)=k.b*k.b*k.M0 := by
    rw [←sum_add_distrib]
    rw [sum_congr rfl (fun j hj => by have := mem_range.mp hj; show k.M0-2*(j+1)+2*(j+1)=k.M0; omega)]
    simp
  have h2 : ∑ j∈range (k.b*k.b), 2*(j+1)=k.b*k.b*(k.b*k.b+1) := by
    rw [←mul_sum,sum_add_distrib,sum_const,card_range,smul_eq_mul]
    have h := sum_range_id_mul_two (k.b*k.b)
    have hb := k.b_two
    have : 1≤k.b*k.b := by nlinarith
    obtain ⟨m,hm⟩ : ∃ m, k.b*k.b=m+1 := ⟨k.b*k.b-1,by omega⟩
    rw [hm] at h ⊢
    have e : (m+1)*(m+1+1)=(m+1)*m+2*(m+1) := by ring
    simp only [Nat.add_sub_cancel] at h
    omega
  have e3 : k.b*k.b*k.M0=k.b*k.b*(k.M0-k.b*k.b-1)+k.b*k.b*(k.b*k.b+1) := by
    rw [←Nat.mul_add]; congr 1; omega
  omega

theorem S_cmax : (S).cmax≤k.cs0+4*T := by
  unfold StarSpec.cmax
  apply Finset.sup_le
  intro j _
  have := k.S_sc hT cs hcs q sub hg j
  have := k.S_lanes hT cs hcs q sub hg j
  omega

/-- The unweighted part of a service cost: `cost_j ≤ cb0 + 2T'·(row+col) + 48·(J-1-j)`. -/
theorem S_cb : (S).cb≤k.cb0 := by
  unfold StarSpec.cb
  apply Finset.sup_le
  intro j _
  have h1 := k.S_sc' hT cs hcs q sub hg j
  have h2 := k.S_lanes_eq hT cs hcs q sub hg j
  have ha := ((P).bounds j.isLt).a_eq
  have hj := j.isLt
  have hc := (P).colOf_lt j
  have eδ : k.δ hT cs hcs j=k.W+4+(P).rowOf j*k.child T+(k.M0+(P).colOf j*k.child T) := rfl
  have e2 : (P).b=k.b := rfl
  have eM : (P).M0=k.M0 := rfl
  have eJ : (P).J=k.b*k.b := rfl
  have l1 : (S).lw1=2*k.child T := rfl
  have l2 : (S).lw2=48 := rfl
  have r1 : (S).ρ1 j=(P).rowOf j+(P).colOf j := rfl
  have r2 : (S).ρ2 j=(P).J-1-j.val := rfl
  have e3 : 2*k.child T*((P).rowOf j+(P).colOf j)=2*((P).rowOf j*k.child T)+2*((P).colOf j*k.child T) := by ring
  rw [l1,l2,r1,r2,e3]
  rw [eδ] at h2
  unfold cb0
  omega

/-- The weights add up: `Σ (row + col) = b²(b-1)` and `2 Σ (J-1-j) = J(J-1)`. -/
theorem S_cbase : (S).cb*(P).J+(S).lw1*∑ j, (S).ρ1 j+(S).lw2*∑ j, (S).ρ2 j≤(k.cs0+4*T)*(k.b*k.b) := by
  have hJ : (P).J=k.b*k.b := rfl
  have l1 : (S).lw1=2*k.child T := rfl
  have l2 : (S).lw2=48 := rfl
  have s1 : ∑ j, (S).ρ1 j=k.b*(k.b*(k.b-1)) := by
    have e : ∀ j : Fin (P).J, (S).ρ1 j=j.val/k.b+j.val%k.b := fun j => rfl
    rw [sum_congr rfl (fun j _ => e j),Fin.sum_univ_eq_sum_range (fun j => j/k.b+j%k.b) (P).J,hJ,
      sum_divmod_sq]
  have s2 : 2*∑ j, (S).ρ2 j=k.b*k.b*(k.b*k.b-1) := by
    have e : ∀ j : Fin (P).J, (S).ρ2 j=k.b*k.b-1-j.val := fun j => rfl
    rw [sum_congr rfl (fun j _ => e j),Fin.sum_univ_eq_sum_range (fun j => k.b*k.b-1-j) (P).J,hJ,
      sum_range_reflect (fun j => j) (k.b*k.b),Nat.mul_comm 2,sum_range_id_mul_two]
  have hcb := k.S_cb hT cs hcs q sub hg
  have hbx : k.b*k.child T≤T := by have := k.child_mul T; have := k.M0_le hT; omega
  have hb := k.b_two
  have hbb := k.bb
  set B2 := k.b*k.b with hB2
  have hM : k.M0=2*B2+4 := rfl
  -- the lane weight: `2 T' b²(b-1) ≤ 4 b² T`
  have w1 : 2*k.child T*(k.b*(k.b-1))≤4*T*B2 := by
    have : k.b-1≤k.b := Nat.sub_le _ _
    calc 2*k.child T*(k.b*(k.b-1))=2*(k.b-1)*(k.b*k.child T) := by ring
      _≤2*k.b*T := Nat.mul_le_mul (by omega) hbx
      _≤4*T*B2 := by nlinarith
  -- the constants: `cb0·J + 24 J(J-1) ≤ cs0·J`
  have w2 : k.cb0*B2+24*(B2*(B2-1))≤k.cs0*B2 := by
    have hc0 : k.cb0=154+4*B2+4*k.b := by unfold cb0; rw [hM]; omega
    have hc1 : k.cs0=52*B2+102 := by unfold cs0; rw [hM]; omega
    rw [hc0,hc1]
    have e : B2*(B2-1)+B2=B2*B2 := by
      rcases Nat.eq_zero_or_pos B2 with h0 | h0
      · rw [h0]
      · rw [←Nat.mul_succ]; congr 1; omega
    have hb4 : 4≤B2 := by omega
    have h3 : (28+4*k.b)*B2≤24*(B2*B2) := by nlinarith
    have e1 : (154+4*B2+4*k.b)*B2=154*B2+4*(B2*B2)+4*(k.b*B2) := by ring
    have e2 : (52*B2+102)*B2=52*(B2*B2)+102*B2 := by ring
    have e3 : (28+4*k.b)*B2=28*B2+4*(k.b*B2) := by ring
    omega
  have hcJ : (S).cb*(P).J=(S).cb*B2 := rfl
  rw [hcJ,l1,l2,s1]
  have m1 : (S).cb*B2≤k.cb0*B2 := Nat.mul_le_mul_right _ hcb
  have e2 : (k.cs0+4*T)*B2=k.cs0*B2+4*T*B2 := by ring
  have e3 : 2*k.child T*(k.b*(k.b*(k.b-1)))=2*k.child T*(k.b*(k.b-1))*k.b := by ring
  have w1' : 2*k.child T*(k.b*(k.b*(k.b-1)))≤4*T*B2 := by
    have : 2*k.child T*(k.b*(k.b*(k.b-1)))=2*(k.b-1)*((k.b*k.child T)*k.b) := by ring
    rw [this]
    have hbx' : (k.b*k.child T)*k.b≤T*k.b := Nat.mul_le_mul_right _ hbx
    have : 2*(k.b-1)*((k.b*k.child T)*k.b)≤2*(k.b-1)*(T*k.b) := Nat.mul_le_mul_left _ hbx'
    have : 2*(k.b-1)*(T*k.b)≤4*T*B2 := by
      have : 2*(k.b-1)≤4*k.b := by omega
      calc 2*(k.b-1)*(T*k.b)≤4*k.b*(T*k.b) := Nat.mul_le_mul_right _ this
        _=4*T*B2 := by rw [hB2]; ring
    omega
  omega

theorem S_rmax (hb : ∀ j, k.Bud (k.kids hT cs hcs q sub hg j)) : (S).rmax≤k.Kr*k.child T := by
  unfold StarSpec.rmax
  apply Finset.sup_le
  intro j _
  exact (hb j).1

theorem S_rate (hb : ∀ j, k.Bud (k.kids hT cs hcs q sub hg j)) : (S).rateP≤k.Kr*T := by
  unfold StarSpec.rateP
  have hd := k.S_dwcost hT cs hcs q sub hg
  have hc := k.child_ge hT
  have hl := k.Tmin_lane
  have := k.child_upper hT
  have hT' : T≤(k.b+1)*k.child T := by unfold M0 at this; rw [Nat.add_mul,Nat.one_mul]; omega
  have hcs0 : k.cs0≤k.lam*T := k.cs0_le hT
  have hmul := k.child_mul T
  have hhp : (S).hp=k.hp := rfl
  have hhq : (S).hq=k.hq := rfl
  rw [hhp,hhq]
  have hT1 : 1≤T := by have := k.Tmin_six; have := k.Tmin_le_Tbig; omega
  refine le_trans (Nat.add_le_add_left hd _) ?_
  have l1 : (S).lw1=2*k.child T := rfl
  have l2 : (S).lw2=48 := rfl
  have w1 : (S).wp1=k.wp1 := rfl
  have w2 : (S).wp2=k.wp2 := rfl
  rw [l1,l2,w1,w2]
  exact rate_arith k.hq_pos k.b_pos hT k.Tbig_pos (by omega) k.hJ_lt k.Kr_spec
    (k.S_cb hT cs hcs q sub hg) (k.S_rmax hT cs hcs q sub hg hb) le_rfl

theorem kid_card (j : Fin (P).J) : (k.kids hT cs hcs q sub hg j).R.cells.card=(k.child T-k.W)*k.child T := by
  rw [(k.kids hT cs hcs q sub hg j).cells_eq,k.card_bodyCells]

/-- Services on lane tiles: `Σ_j cost_j (|X_j|+|Y_j|) ≤ lq·T² + ll·T`, from
`cost_j ≤ 2δ_j + smax`, `|X_j|+|Y_j| ≤ 2δ_j` and `δ_j = kap + (row + col)·T'`. -/
theorem S_lanework : ∑ j, (S).serviceCost j*((S).elen j+(S).dlen j)≤k.lq*(T*T)+k.ll*T := by
  have hJ : (P).J=k.b*k.b := rfl
  have hbx : k.b*k.child T≤T := by have := k.child_mul T; have := k.M0_le hT; omega
  set x := k.child T with hx
  have eδ : ∀ j : Fin (P).J, k.δ hT cs hcs j=k.kap+x*(j.val/k.b+j.val%k.b) := by
    intro j
    have e1 : (P).W=k.W := rfl
    have e2 : (P).M0=k.M0 := rfl
    have e3 : (P).T'=k.child T := rfl
    have e4 : (P).b=k.b := rfl
    unfold δ kap Params.R Params.C Params.rowOf Params.colOf
    rw [e1,e2,e3,e4]; ring
  have per : ∀ j : Fin (P).J, (S).serviceCost j*((S).elen j+(S).dlen j)≤
      4*(x*x)*(j.val/k.b+j.val%k.b)^2+2*(4*k.kap+k.smax)*x*(j.val/k.b+j.val%k.b)+
        2*k.kap*(2*k.kap+k.smax) := by
    intro j
    have hsc := k.S_sc' hT cs hcs q sub hg j
    have hal := k.S_a_le hT cs hcs j
    have hq := k.S_lanes_eq hT cs hcs q sub hg j
    have hcol := (P).colOf_lt j
    have e2b : (P).b=k.b := rfl
    have hW : k.W=2*k.b := rfl
    have h1 : (S).serviceCost j≤2*k.δ hT cs hcs j+k.smax := by unfold smax; omega
    have h2 : (S).elen j+(S).dlen j≤2*k.δ hT cs hcs j := by omega
    have h3 := Nat.mul_le_mul h1 h2
    rw [eδ j] at h3
    have e : (2*(k.kap+x*(j.val/k.b+j.val%k.b))+k.smax)*(2*(k.kap+x*(j.val/k.b+j.val%k.b)))=
        4*(x*x)*(j.val/k.b+j.val%k.b)^2+2*(4*k.kap+k.smax)*x*(j.val/k.b+j.val%k.b)+
          2*k.kap*(2*k.kap+k.smax) := by ring
    omega
  refine (sum_le_sum (fun j _ => per j)).trans ?_
  rw [sum_add_distrib,sum_add_distrib,sum_const,card_univ,Fintype.card_fin,smul_eq_mul,←mul_sum,←mul_sum,
    Fin.sum_univ_eq_sum_range (fun j => (j/k.b+j%k.b)^2) (P).J,
    Fin.sum_univ_eq_sum_range (fun j => j/k.b+j%k.b) (P).J,hJ,sum_divmod_sq]
  set S2 := ∑ j ∈ range (k.b*k.b), (j/k.b+j%k.b)^2 with hS2
  have hb := k.b_pos
  -- the quadratic part
  have q1 : 4*S2≤k.b*k.b*k.lq := by
    unfold lq; rw [←hS2]; exact Ledger.le_mul_cdiv (by positivity)
  have q2 : 4*(x*x)*S2≤k.lq*(T*T) := by
    calc 4*(x*x)*S2=x*x*(4*S2) := by ring
      _≤x*x*(k.b*k.b*k.lq) := Nat.mul_le_mul_left _ q1
      _=(k.b*x)*(k.b*x)*k.lq := by ring
      _≤T*T*k.lq := Nat.mul_le_mul_right _ (Nat.mul_le_mul hbx hbx)
      _=_ := by ring
  -- the linear part
  have l1 : 2*(4*k.kap+k.smax)*x*(k.b*(k.b*(k.b-1)))≤2*(4*k.kap+k.smax)*(k.b*(k.b-1))*T := by
    calc 2*(4*k.kap+k.smax)*x*(k.b*(k.b*(k.b-1)))=2*(4*k.kap+k.smax)*(k.b*(k.b-1))*(k.b*x) := by ring
      _≤_ := Nat.mul_le_mul_left _ hbx
  have l2 : k.b*k.b*(2*k.kap*(2*k.kap+k.smax))≤
      Ledger.cdiv (2*(k.b*k.b)*(k.kap*(2*k.kap+k.smax))) k.Tbig*T := by
    have := Ledger.le_mul_cdiv (x:=2*(k.b*k.b)*(k.kap*(2*k.kap+k.smax))) (q:=k.Tbig) k.Tbig_pos
    have h2 : k.Tbig*Ledger.cdiv (2*(k.b*k.b)*(k.kap*(2*k.kap+k.smax))) k.Tbig≤
        T*Ledger.cdiv (2*(k.b*k.b)*(k.kap*(2*k.kap+k.smax))) k.Tbig := Nat.mul_le_mul_right _ hT
    have e : k.b*k.b*(2*k.kap*(2*k.kap+k.smax))=2*(k.b*k.b)*(k.kap*(2*k.kap+k.smax)) := by ring
    rw [e,Nat.mul_comm _ T]; omega
  unfold ll
  have e : (2*(4*k.kap+k.smax)*(k.b*(k.b-1))+Ledger.cdiv (2*(k.b*k.b)*(k.kap*(2*k.kap+k.smax))) k.Tbig)*T=
      2*(4*k.kap+k.smax)*(k.b*(k.b-1))*T+Ledger.cdiv (2*(k.b*k.b)*(k.kap*(2*k.kap+k.smax))) k.Tbig*T := by
    ring
  have e2 : 2*(4*k.kap+k.smax)*(x*(k.b*(k.b*(k.b-1))))=2*(4*k.kap+k.smax)*x*(k.b*(k.b*(k.b-1))) := by ring
  have e3 : 4*(x*x)*S2=4*(x*x)*S2 := rfl
  omega

/-- Productive part of the services: per spoke, `pop*(E+D)` against twice
the corner offset per child cell. -/
theorem S_sum1 : ∑ j, (S).serviceCost j*((S).pop j+(S).elen j+(S).dlen j)≤
    ∑ j, 2*((k.child T-k.W)*k.child T*k.δ hT cs hcs j)+
      ((k.b*k.b)*(k.sv*((k.child T-k.W)*k.child T))+(k.lq*(T*T)+k.ll*T)) := by
  have hJ : (P).J=k.b*k.b := rfl
  have hlw := k.S_lanework hT cs hcs q sub hg
  set c := (k.child T-k.W)*k.child T with hcdef
  have split : ∑ j, (S).serviceCost j*((S).pop j+(S).elen j+(S).dlen j)=
      ∑ j, (S).serviceCost j*(S).pop j+∑ j, (S).serviceCost j*((S).elen j+(S).dlen j) := by
    rw [←sum_add_distrib]; apply sum_congr rfl; intro j _; ring
  rw [split]
  suffices ∑ j, (S).serviceCost j*(S).pop j≤∑ j, 2*(c*k.δ hT cs hcs j)+(k.b*k.b)*(k.sv*c) by omega
  have per : ∀ j : Fin (P).J, (S).serviceCost j*(S).pop j≤
      2*(c*k.δ hT cs hcs j)+(24*(P).a j+46+4*(k.b-1)-2*k.W)*c := by
    intro j
    have hsc := k.S_sc' hT cs hcs q sub hg j
    have hal := k.S_a_le hT cs hcs j
    have ha : 26*(P).a j+50≤k.cs0 := by unfold cs0; omega
    have hl := k.S_lanes hT cs hcs q sub hg j
    have hq := k.S_lanes_eq hT cs hcs q sub hg j
    have hcol := (P).colOf_lt j
    have e2b : (P).b=k.b := rfl
    have hW : k.W=2*k.b := rfl
    have hp := k.kid_pop hT cs hcs q sub hg j
    rw [←hcdef] at hp
    generalize (S).serviceCost j=sc at hsc ⊢
    generalize (S).pop j=pop at hp ⊢
    generalize c=c' at hp ⊢
    have hδ : (P).R ((P).rowOf j)+(P).C ((P).colOf j)=k.δ hT cs hcs j := rfl
    rw [hδ] at hl
    generalize k.δ hT cs hcs j=δ at hl hq ⊢
    generalize (S).elen j=E at hl hq hsc ⊢
    generalize (S).dlen j=D at hl hq hsc ⊢
    generalize (P).a j=a at hsc ha hq ⊢
    -- the service minus `2δ` costs at most `24a + 46 + 4(b-1) - 2W` per cell
    have hA : sc≤2*δ+(24*a+46+4*(k.b-1)-2*k.W) := by omega
    have hpc : pop≤c' := by omega
    have h2 : sc*pop≤(2*δ+(24*a+46+4*(k.b-1)-2*k.W))*c' := Nat.mul_le_mul hA hpc
    have e : (2*δ+(24*a+46+4*(k.b-1)-2*k.W))*c'=2*(c'*δ)+(24*a+46+4*(k.b-1)-2*k.W)*c' := by ring
    omega
  calc _≤∑ j : Fin (P).J, (2*(c*k.δ hT cs hcs j)+(24*(P).a j+46+4*(k.b-1)-2*k.W)*c) :=
        sum_le_sum (fun j _ => per j)
    _=∑ j, 2*(c*k.δ hT cs hcs j)+(k.b*k.b)*(k.sv*c) := by
        rw [sum_add_distrib]
        congr 1
        have hW : 2*k.W≤46+4*(k.b-1) := by unfold W; have := k.b_two; omega
        have e : ∀ j : Fin (P).J, (24*(P).a j+46+4*(k.b-1)-2*k.W)*c=
            (24*c)*(P).a j+(46+4*(k.b-1)-2*k.W)*c := fun j => by
          rw [show 24*(P).a j+46+4*(k.b-1)-2*k.W=24*(P).a j+(46+4*(k.b-1)-2*k.W) by omega]; ring
        rw [sum_congr rfl (fun j _ => e j),sum_add_distrib,←mul_sum,k.S_a_sum hT cs hcs,sum_const,
          card_univ,Fintype.card_fin,hJ,smul_eq_mul]
        unfold sv
        rw [show 24*(k.M0-k.b*k.b-1)+46+4*(k.b-1)-2*k.W=24*(k.M0-k.b*k.b-1)+(46+4*(k.b-1)-2*k.W) by omega]
        ring

/-- Children's budgets and access walks. -/
theorem S_sum2 (hb : ∀ j, k.Bud (k.kids hT cs hcs q sub hg j)) :
    ∑ j, (((S).Q j).base+2*(((S).L.accessTail j).length+((S).L.exportQ j).length))≤
    ∑ j, 2*dsum (k.slot hT cs hcs q j) (k.kids hT cs hcs q sub hg j).R.cells+
      (k.b*k.b)*(k.Kl*(k.child T*k.child T)+k.K0*(k.child T*k.child T)*k.dep (k.child T)+2*(k.M0+2+2*T)) := by
  have hJ : (P).J=k.b*k.b := rfl
  have : (k.b*k.b)*(k.Kl*(k.child T*k.child T)+k.K0*(k.child T*k.child T)*k.dep (k.child T)+2*(k.M0+2+2*T))=
      ∑ _j : Fin (P).J, (k.Kl*(k.child T*k.child T)+k.K0*(k.child T*k.child T)*k.dep (k.child T)+2*(k.M0+2+2*T)) := by
    rw [sum_const,card_univ,Fintype.card_fin,hJ,smul_eq_mul]
  rw [this,←sum_add_distrib]
  apply sum_le_sum
  intro j _
  have h1 := (hb j).2
  have h2 := k.S_access hT cs hcs q sub hg j
  have h2' := k.S_a_le hT cs hcs j
  have h3 := (k.S_lanes hT cs hcs q sub hg j).1
  change (k.kids hT cs hcs q sub hg j).R.base+2*(((S).L.accessTail j).length+(S).elen j)≤_
  unfold dsum at h1 ⊢
  omega

/-- The slot offsets add up to `b²(W+4+M0)` plus `b(b-1)` times the side. -/
theorem S_delta_sum : ∑ j : Fin (P).J, k.δ hT cs hcs j≤k.b*k.b*(k.W+4+k.M0)+k.b*(k.b-1)*T := by
  have hJ : (P).J=k.b*k.b := rfl
  have e : ∀ j : Fin (P).J, k.δ hT cs hcs j=(k.W+4+k.M0)+k.child T*(j.val/k.b+j.val%k.b) := by
    intro j
    have e1 : (P).W=k.W := rfl
    have e2 : (P).M0=k.M0 := rfl
    have e3 : (P).T'=k.child T := rfl
    have e4 : (P).b=k.b := rfl
    unfold δ Params.R Params.C Params.rowOf Params.colOf
    rw [e1,e2,e3,e4]; ring
  rw [sum_congr rfl (fun j _ => e j),sum_add_distrib,sum_const,card_univ,Fintype.card_fin,smul_eq_mul,
    ←mul_sum,Fin.sum_univ_eq_sum_range (fun j => j/k.b+j%k.b) (P).J,hJ,sum_divmod_sq]
  have hm := k.child_mul T
  have : k.child T*(k.b*(k.b*(k.b-1)))≤k.b*(k.b-1)*T := by
    calc k.child T*(k.b*(k.b*(k.b-1)))=(k.b*k.child T)*(k.b*(k.b-1)) := by ring
      _≤T*(k.b*(k.b-1)) := Nat.mul_le_mul_right _ (by omega)
      _=_ := by ring
  omega

theorem S_delta_eq : ∑ j : Fin (P).J, k.δ hT cs hcs j=k.b*k.b*(k.W+4+k.M0)+k.child T*(k.b*(k.b*(k.b-1))) := by
  have hJ : (P).J=k.b*k.b := rfl
  have e : ∀ j : Fin (P).J, k.δ hT cs hcs j=(k.W+4+k.M0)+k.child T*(j.val/k.b+j.val%k.b) := by
    intro j
    have e1 : (P).W=k.W := rfl
    have e2 : (P).M0=k.M0 := rfl
    have e3 : (P).T'=k.child T := rfl
    have e4 : (P).b=k.b := rfl
    unfold δ Params.R Params.C Params.rowOf Params.colOf
    rw [e1,e2,e3,e4]; ring
  rw [sum_congr rfl (fun j _ => e j),sum_add_distrib,sum_const,card_univ,Fintype.card_fin,smul_eq_mul,
    ←mul_sum,Fin.sum_univ_eq_sum_range (fun j => j/k.b+j%k.b) (P).J,hJ,sum_divmod_sq]

theorem S_childSpare : (S).childSpare.card≤6*(k.b*k.b) := by
  unfold StarSpec.childSpare
  calc _≤∑ j : Fin (P).J, ((S).Q j).spareCells.card := card_biUnion_le
    _=∑ _j : Fin (P).J, 6 := by
        apply sum_congr rfl; intro j _
        exact (k.kids hT cs hcs q sub hg j).spare6
    _=6*(k.b*k.b) := by simp only [sum_const,card_univ,Fintype.card_fin,smul_eq_mul]; rw [Nat.mul_comm]; rfl

/-- The final sort, charged by position. -/
theorem S_fin : 2*∑ x∈(S).resid, (S).fw x≤
    9*(2*(3*(k.b-1)+2*(k.M0-2)+k.W*(k.b-2))*(T*T)+
      k.b*(6*(k.b-1+k.M0)^2+2*k.M0*k.W*k.b+3*k.W^2*k.b+6*k.W*k.b+2*k.W)*k.child T+
      (k.b-1+k.M0)^2*(2*(k.b-1+k.M0)+k.W)+2*(6*(k.b*k.b)*(2*T)))+28*(k.cr*T+6) := by
  classical
  set x := k.child T with hxdef
  set d : Cell n → Nat := fun y => gridDistance (q.loc 0 0) y with hd
  have hcellsB : (S).frame.cells=k.bodyCells q := (k.star hT cs hcs q sub hg).cells_eq
  -- weights against distances
  have hw : ∀ y∈(S).resid, (S).fw y≤9*d y+14 := by
    intro y hy
    have hc := ((S).mem_resid.mp hy).1
    rw [hcellsB] at hc
    obtain ⟨r,c,_,hr,hc',rfl⟩ := (k.mem_bodyCells q).mp hc
    rw [k.S_fw_loc hT cs hcs q sub hg hr hc']
    have h0 : 0<T := NeZero.pos T
    have : d (q.loc r c)=r+c := by
      simp only [d]; rw [q.loc_dist h0 h0 hr hc']; simp [Nat.dist]
    rw [this]; unfold Cycle3.tw; omega
  have s1 : ∑ y∈(S).resid, (S).fw y≤9*∑ y∈(S).resid, d y+14*(S).resid.card := by
    calc _≤∑ y∈(S).resid, (9*d y+14) := sum_le_sum hw
      _=_ := by rw [sum_add_distrib,←mul_sum,sum_const,smul_eq_mul,Nat.mul_comm _ 14]
  -- distances of the reserve cells
  have s2 := k.S_resid_d hT cs hcs q sub hg
  have hkid (j : Fin (P).J) : dsum q (k.kids hT cs hcs q sub hg j).R.cells=
      (∑ i∈range x, ∑ jj∈range x, if k.W ≤ i then i+jj else 0)+(x-k.W)*x*k.δ hT cs hcs j := by
    rw [k.dsum_kid hT cs hcs q sub hg j,k.kid_card hT cs hcs q sub hg j,(k.kids hT cs hcs q sub hg j).cells_eq,
      k.dsum_body_eq]
  have hJ : (P).J=k.b*k.b := rfl
  have s3 : ∑ j, dsum q (k.kids hT cs hcs q sub hg j).R.cells=
      k.b*k.b*(∑ i∈range x, ∑ jj∈range x, if k.W ≤ i then i+jj else 0)+(x-k.W)*x*∑ j, k.δ hT cs hcs j := by
    rw [sum_congr rfl (fun j _ => hkid j),sum_add_distrib,sum_const,card_univ,Fintype.card_fin,smul_eq_mul,
      ←mul_sum]
    rfl
  rw [s3,k.S_delta_eq hT cs hcs,hcellsB,k.dsum_body_eq] at s2
  -- the closed forms
  have hc := k.child_ge hT
  have hW := k.W_lt_Tmin
  have hWT : k.W≤T := by have := k.Tmin_le_Tbig; omega
  have hAT := body_grid T k.W hWT
  have hAx := body_grid x k.W (by omega)
  have hb := k.b_two
  have hmod := Nat.div_add_mod (T-k.M0) k.b
  have hmlt := Nat.mod_lt (T-k.M0) (by omega : k.b>0)
  have hM := k.M0_le hT
  have hxe : x=(T-k.M0)/k.b := rfl
  have hR := resid_arith (T:=T) (x:=x) (b:=k.b) (W:=k.W) (M0:=k.M0) (E:=(T-k.M0)%k.b)
    (AT:=∑ i∈range T, ∑ jj∈range T, if k.W ≤ i then i+jj else 0)
    (Ax:=∑ i∈range x, ∑ jj∈range x, if k.W ≤ i then i+jj else 0)
    (Sd:=k.b*k.b*(k.W+4+k.M0)+x*(k.b*(k.b*(k.b-1))))
    (R:=∑ y∈(S).resid, d y) (Z:=(S).childSpare.card*(2*T)) hb (by omega)
    (by have := k.W_M0; omega) (by unfold W; omega) (by omega)
    (by rw [hxe]; omega) hAT hAx rfl (by simp only [hd,hxdef]; exact s2)
  have hsp := k.S_childSpare hT cs hcs q sub hg
  have hsp2 : (S).childSpare.card*(2*T)≤6*(k.b*k.b)*(2*T) := Nat.mul_le_mul_right _ hsp
  have hres := (S).resid_card
  have hres2 : (S).own.card+(S).childSpare.card=(S).frame.r := by
    change _=((S).own∪(S).childSpare).card
    rw [card_union_of_disjoint]
    exact (S).disjoint_own_childCells.mono_right (S).childSpare_sub
  have hmk : (S).markers.card=6 := (P).markers_card q
  have hr := k.S_r hT cs hcs q sub hg
  omega

theorem S_fin' : 2*∑ x∈(S).resid, (S).fw x≤18*k.al*(T*T)+k.fl*T := by
  have h := k.S_fin hT cs hcs q sub hg
  have hbx : k.b*k.child T≤T := by have := k.child_mul T; omega
  have hT1 : 1≤T := by have := k.Tmin_six; have := k.Tmin_le_Tbig; omega
  set be := k.b*(6*(k.b-1+k.M0)^2+2*k.M0*k.W*k.b+3*k.W^2*k.b+6*k.W*k.b+2*k.W)
  set ga := (k.b-1+k.M0)^2*(2*(k.b-1+k.M0)+k.W)
  have h1 : 9*be*k.child T≤Ledger.cdiv (9*be) k.b*T := by
    have : k.b*(9*be*k.child T)≤k.b*(Ledger.cdiv (9*be) k.b*T) := by
      calc k.b*(9*be*k.child T)=9*be*(k.b*k.child T) := by ring
        _≤9*be*T := Nat.mul_le_mul_left _ hbx
        _≤k.b*Ledger.cdiv (9*be) k.b*T := Nat.mul_le_mul_right _ (Ledger.le_mul_cdiv k.b_pos)
        _=_ := by ring
    exact Nat.le_of_mul_le_mul_left this k.b_pos
  have h2 : 9*ga≤Ledger.cdiv (9*ga) k.Tbig*T := by
    have := Ledger.le_mul_cdiv (x:=9*ga) (q:=k.Tbig) k.Tbig_pos
    calc 9*ga≤k.Tbig*Ledger.cdiv (9*ga) k.Tbig := this
      _≤T*Ledger.cdiv (9*ga) k.Tbig := Nat.mul_le_mul_right _ hT
      _=_ := Nat.mul_comm _ _
  have h3 : 168≤168*T := by omega
  have e : k.fl*T=Ledger.cdiv (9*be) k.b*T+Ledger.cdiv (9*ga) k.Tbig*T+216*(k.b*k.b)*T+28*k.cr*T+168*T := by
    unfold fl; ring
  have e2 : 9*(2*k.al*(T*T)+be*k.child T+ga+2*(6*(k.b*k.b)*(2*T)))+28*(k.cr*T+6)=
      18*k.al*(T*T)+9*be*k.child T+9*ga+216*(k.b*k.b)*T+28*k.cr*T+168 := by ring
  have hal : 3*(k.b-1)+2*(k.M0-2)+k.W*(k.b-2)=k.al := rfl
  rw [hal,e2] at h
  omega

theorem S_sum3 (hb : ∀ j, k.Bud (k.kids hT cs hcs q sub hg j)) :
    (S).rmax*((P).J+∑ j, ((S).elen j+(S).dlen j+2))≤
      k.Kr*k.child T*(k.b*k.b+2*k.b*(k.b-1)*T+k.Lc) := by
  have hJ : (P).J=k.b*k.b := rfl
  apply Nat.mul_le_mul (k.S_rmax hT cs hcs q sub hg hb)
  have per : ∑ j : Fin (P).J, (((S).elen j+(S).dlen j+2)+(2*k.W+2+2*(P).a j))≤
      ∑ j : Fin (P).J, (2*k.δ hT cs hcs j+4*(k.b-1)) := by
    apply sum_le_sum; intro j _
    have := k.S_lanes_eq hT cs hcs q sub hg j
    have := (P).colOf_lt j
    have e2b : (P).b=k.b := rfl
    omega
  have lhs : ∑ j : Fin (P).J, (((S).elen j+(S).dlen j+2)+(2*k.W+2+2*(P).a j))=
      ∑ j : Fin (P).J, ((S).elen j+(S).dlen j+2)+((P).J*(2*k.W+2)+2*∑ j : Fin (P).J, (P).a j) := by
    rw [Finset.sum_add_distrib (f:=fun j => (S).elen j+(S).dlen j+2)]
    congr 1
    rw [Finset.sum_add_distrib (f:=fun _ => 2*k.W+2),←mul_sum,sum_const,card_univ,Fintype.card_fin,
      smul_eq_mul]
  have rhs : ∑ j : Fin (P).J, (2*k.δ hT cs hcs j+4*(k.b-1))=
      2*∑ j : Fin (P).J, k.δ hT cs hcs j+(P).J*(4*(k.b-1)) := by
    rw [sum_add_distrib,←mul_sum,sum_const,card_univ,Fintype.card_fin,smul_eq_mul]
  rw [lhs,rhs,k.S_a_sum hT cs hcs] at per
  have hd := k.S_delta_sum hT cs hcs
  generalize ∑ j : Fin (P).J, ((S).elen j+(S).dlen j+2)=σ at per ⊢
  generalize ∑ j : Fin (P).J, k.δ hT cs hcs j=d at per hd
  rw [hJ] at per ⊢
  have hM : k.M0-k.b*k.b-1=k.b*k.b+3 := by unfold M0; omega
  have hM' : k.M0=2*(k.b*k.b)+4 := rfl
  rw [hM] at per
  rw [hM'] at hd
  have hb1 := k.b_pos
  unfold Lc
  set B2 := k.b*k.b with hB2
  have e1 : B2*(2*k.W+2)=2*(B2*k.W)+2*B2 := by ring
  have e2 : B2*(B2+3)=B2*B2+3*B2 := by ring
  have e3 : B2*(k.W+4+(2*B2+4))=B2*k.W+8*B2+2*(B2*B2) := by ring
  have e4 : B2*(4*(k.b-1))+4*B2=4*(B2*k.b) := by
    have : B2*(4*(k.b-1))+4*B2=B2*(4*(k.b-1)+4) := by ring
    rw [this,show 4*(k.b-1)+4=4*k.b by omega]; ring
  have e5 : B2*(2*B2+4*k.b+4)=2*(B2*B2)+4*(B2*k.b)+4*B2 := by ring
  have e6 : 2*k.b*(k.b-1)*T=2*(k.b*(k.b-1)*T) := by ring
  omega

theorem S_base (hb : ∀ j, k.Bud (k.kids hT cs hcs q sub hg j)) :
    (S).baseP≤2*dsum q (S).frame.cells+k.Kl*(T*T)+k.K0*(T*T)*(k.dep (k.child T)+1) := by
  have h1 := k.S_sum1 hT cs hcs q sub hg
  have h2 := k.S_sum2 hT cs hcs q sub hg hb
  have h3 := k.S_sum3 hT cs hcs q sub hg hb
  have hgeo := k.dsum_kids hT cs hcs q sub hg
  simp only [k.kid_card hT cs hcs q sub hg] at hgeo
  have hgeo2 : ∑ j, 2*((k.child T-k.W)*k.child T*k.δ hT cs hcs j)+
      ∑ j, 2*dsum (k.slot hT cs hcs q j) (k.kids hT cs hcs q sub hg j).R.cells≤2*dsum q (S).frame.cells := by
    rw [←sum_add_distrib]
    calc _=2*∑ j, (dsum (k.slot hT cs hcs q j) (k.kids hT cs hcs q sub hg j).R.cells+
          (k.child T-k.W)*k.child T*k.δ hT cs hcs j) := by
          rw [mul_sum]; apply sum_congr rfl; intro j _; ring
      _≤_ := Nat.mul_le_mul_left _ hgeo
  -- the remaining terms
  have hJ : (P).J=k.b*k.b := rfl
  have hcm : (S).cb*(P).J+(S).lw1*∑ j, (S).ρ1 j+(S).lw2*∑ j, (S).ρ2 j≤(k.cs0+4*T)*(k.b*k.b) :=
    k.S_cbase hT cs hcs q sub hg
  have hr := k.S_r hT cs hcs q sub hg
  have hMr : (S).frame.M+(S).frame.r≤T*T := by
    have h := Frame.cells_card (S).frame
    have h2 : (S).frame.cells=k.bodyCells q := (k.star hT cs hcs q sub hg).cells_eq
    rw [h2,k.card_bodyCells] at h
    have : (T-k.W)*T≤T*T := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    omega
  have hconn := k.S_conn hT cs hcs q sub hg
  have hw : (S).wrapCost*((S).frame.M+(S).frame.r)≤k.wrapC*(T*T) :=
    Nat.mul_le_mul (k.S_wrap hT cs hcs q sub hg) hMr
  have hdx : (S).dxCost*((S).frame.r-(S).stat.card)+∑ x∈(S).stat, (S).dw x+k.dk*k.crc*T+k.gq*(T*T)≤
      k.dk*k.cr*(T*T)+k.gl*T := by
    have h1 : (S).dxCost*(S).frame.r≤k.dk*T*(S).frame.r := by
      unfold StarSpec.dxCost; exact Nat.mul_le_mul_right _ (k.S_dcost hT cs hcs q sub hg)
    have h2 := k.S_r' hT cs hcs q sub hg
    have h3 : k.dk*T*((S).frame.r+k.crc)≤k.dk*T*(k.cr*T) := Nat.mul_le_mul_left _ h2
    have e1 : k.dk*T*((S).frame.r+k.crc)=k.dk*T*(S).frame.r+k.dk*k.crc*T := by ring
    have e2 : k.dk*T*(k.cr*T)=k.dk*k.cr*(T*T) := by ring
    -- the static cells: position cost plus gain is the full cost
    have hg' := k.S_stat_gain hT cs hcs q sub hg
    have hcard := k.S_stat_card hT cs hcs q sub hg
    have hsplit : ∑ x∈(S).stat, (S).dw x+∑ x∈(S).stat, ((S).dxCost-(S).dw x)=(S).stat.card*(S).dxCost := by
      rw [←sum_add_distrib,sum_congr rfl (fun x hx => Nat.add_sub_cancel' (k.S_dw_le hT cs hcs q sub hg hx)),
        sum_const,smul_eq_mul]
    have hsub : (S).dxCost*((S).frame.r-(S).stat.card)+(S).stat.card*(S).dxCost=(S).dxCost*(S).frame.r := by
      rw [Nat.mul_comm ((S).stat.card),←Nat.mul_add,Nat.sub_add_cancel hcard]
    omega
  have hres : (S).own.card+(S).childSpare.card=(S).frame.r := by
    change _=((S).own∪(S).childSpare).card
    rw [card_union_of_disjoint]
    exact (S).disjoint_own_childCells.mono_right (S).childSpare_sub
  have hmk : (S).markers.card=6 := (P).markers_card q
  have hfin := k.S_fin' hT cs hcs q sub hg
  have hc := k.child_ge hT
  have hmul := k.child_mul T
  have hT1 : 1≤T := by have := k.Tmin_six; have := k.Tmin_le_Tbig; omega
  have hcs0 : k.cs0≤k.lam*T := k.cs0_le hT
  have hbc : k.b*k.child T≤T := by omega
  have hcc : k.b*k.b*((k.child T-k.W)*k.child T)≤T*T := by
    have : (k.child T-k.W)*k.child T≤k.child T*k.child T := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    calc k.b*k.b*((k.child T-k.W)*k.child T)≤k.b*k.b*(k.child T*k.child T) := Nat.mul_le_mul_left _ this
      _=(k.b*k.child T)*(k.b*k.child T) := by ring
      _≤T*T := Nat.mul_le_mul hbc hbc
  have hx : k.b*k.b*k.child T≤k.b*T := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hbc
  have hrest := rest_arith (T:=T) (Tb:=k.Tbig) (x:=k.child T) (c:=(k.child T-k.W)*k.child T) (b:=k.b)
    (cs0:=k.cs0) (M0:=k.M0) (W:=k.W) (Kr:=k.Kr) (wrapC:=k.wrapC) (cr:=k.cr) (crc:=k.crc) (gq:=k.gq) (gl:=k.gl) (K0:=k.K0) (d:=k.dk) (Lc:=k.Lc)
    (al:=k.al) (fl:=k.fl) (sortT:=2*∑ x∈(S).resid, (S).fw x) (dxv:=(S).dxCost*((S).frame.r-(S).stat.card)+∑ x∈(S).stat, (S).dw x) (lq:=k.lq) (ll:=k.ll)
    hT1 hT (le_trans (by have := k.Tmin_six; omega) k.Tmin_le_Tbig) hcc hbc k.b_pos hfin hdx rfl
  have hbb : (k.b*k.child T)*(k.b*k.child T)≤T*T := Nat.mul_le_mul hbc hbc
  have hkid1 : k.b*k.b*(k.Kl*(k.child T*k.child T))≤k.Kl*(T*T) := by
    calc _=k.Kl*((k.b*k.child T)*(k.b*k.child T)) := by ring
      _≤_ := Nat.mul_le_mul_left _ hbb
  have hkid2 : k.b*k.b*(k.K0*(k.child T*k.child T)*k.dep (k.child T))≤
      k.K0*(T*T)*k.dep (k.child T) := by
    calc _=k.K0*((k.b*k.child T)*(k.b*k.child T))*k.dep (k.child T) := by ring
      _≤_ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hbb)
  have e2 : k.K0*(T*T)*(k.dep (k.child T)+1)=k.K0*(T*T)*k.dep (k.child T)+k.K0*(T*T) := by ring
  have e3 : k.b*k.b*(k.Kl*(k.child T*k.child T)+k.K0*(k.child T*k.child T)*k.dep (k.child T)+
      2*(k.M0+2+2*T))=k.b*k.b*(k.Kl*(k.child T*k.child T))+
      k.b*k.b*(k.K0*(k.child T*k.child T)*k.dep (k.child T))+k.b*k.b*(2*(k.M0+2+2*T)) := by ring
  have : 1≤k.M0 := by unfold M0; omega
  unfold StarSpec.baseP
  omega

theorem star_bud (hb : ∀ j, k.Bud (k.kids hT cs hcs q sub hg j)) : k.Bud (k.star hT cs hcs q sub hg) := by
  refine ⟨k.S_rate hT cs hcs q sub hg hb,?_⟩
  have h := k.S_base hT cs hcs q sub hg hb
  rw [k.dep_star hT]
  exact h

end Star

/-! ### The tree -/

theorem build_bud_aux (T : Nat) : ∀ [NeZero T] (hT : k.Tmin≤T) (cs : Nat) (hcs : 2*cs+1<k.W)
    (q : Placement T n) (hg : k.GoalOK G q), k.Bud (k.build T hT cs hcs q hg) := by
  induction T using Nat.strong_induction_on with
  | _ T ih =>
  intro _ hT cs hcs q hg
  by_cases h : k.Tbig≤T
  · have := k.child_ne h
    rw [k.build_star T hT cs hcs q hg h]
    apply k.star_bud
    intro j
    exact ih (k.child T) (k.child_lt h) (k.child_ge h) _ _ _ _
  · rw [k.build_leaf T hT cs hcs q hg h]
    exact k.leaf_bud _ _ cs hcs q hg h hT

/-- Every node of the tree meets the budget invariant. -/
theorem build_bud (T : Nat) [NeZero T] (hT : k.Tmin≤T) (cs : Nat) (hcs : 2*cs+1<k.W)
    (q : Placement T n) (hg : k.GoalOK G q) : k.Bud (k.build T hT cs hcs q hg) :=
  k.build_bud_aux T hT cs hcs q hg

end Consts

/-- `H₉ ≤ 2829/1000`, in the floor form. -/
theorem harm9 (B : Nat) : 1000*∑ t ∈ Ioc 0 9, B/t≤2829*B := by
  have hq : ((∑ t ∈ Ioc 0 9, B/t : Nat) : ℚ)≤∑ t ∈ Ioc (0:Nat) 9, (B:ℚ)/(t:ℚ) := by
    push_cast
    exact sum_le_sum (fun t _ => Nat.cast_div_le)
  have hH : ∑ t ∈ Ioc (0:Nat) 9, (1:ℚ)/(t:ℚ)≤2829/1000 := by
    rw [show Ioc (0:Nat) 9=(range 9).map ⟨(·+1),add_left_injective 1⟩ from by decide]
    simp only [sum_map,sum_range_succ,sum_range_zero]
    norm_num
  have e : ∑ t ∈ Ioc (0:Nat) 9, (B:ℚ)/(t:ℚ)=B*∑ t ∈ Ioc (0:Nat) 9, (1:ℚ)/(t:ℚ) := by
    rw [mul_sum]; exact sum_congr rfl (fun t _ => by ring)
  rw [e] at hq
  have h2 := hq.trans (mul_le_mul_of_nonneg_left hH (by positivity : (0:ℚ)≤B))
  have h3 : (1000:ℚ)*((∑ t ∈ Ioc 0 9, B/t : Nat) : ℚ)≤2829*B := by linarith
  exact_mod_cast h3

theorem harm_cast (B N : Nat) : ((∑ t ∈ Ioc 0 N, B/t : Nat) : ℚ)≤B*∑ t ∈ Ioc 0 N, (1:ℚ)/t := by
  push_cast
  rw [mul_sum]
  exact sum_le_sum (fun t _ => by rw [mul_one_div]; exact Nat.cast_div_le)

theorem harm_range (N : Nat) : ∑ t ∈ Ioc (0:Nat) N, (1:ℚ)/t=∑ i ∈ range N, (1:ℚ)/(i+1) := by
  rw [show Ioc (0:Nat) N=(range N).map ⟨(·+1),add_left_injective 1⟩ by
    ext x; simp [mem_Ioc]; constructor
    · rintro ⟨h1,h2⟩; exact ⟨x-1,by omega,by omega⟩
    · rintro ⟨a,h1,rfl⟩; omega]
  simp

/-- `H_N` for `N ≤ 8`, as a bound on the floor sum. -/
theorem harm_le_q (B N : Nat) : ((∑ t ∈ Ioc 0 N, B/t : Nat) : ℚ)≤
    B*(∑ i ∈ range N, (1:ℚ)/(i+1)) := by
  have := harm_cast B N; rwa [harm_range] at this

theorem harm1 (B : Nat) : ∑ t ∈ Ioc 0 1, B/t=B := by
  rw [show Ioc 0 1=({1} : Finset Nat) by decide]; simp

/-- Layered harmonic bound of the slot weights `row + col` for `b = 3`:
`H₈ + H₆ + H₃ + H₁ ≤ 8.002`. -/
theorem harm_layer1 (B : Nat) : 1000*Ledger.layered (fun j : Fin (3*3) => j.val/3+j.val%3) B≤8002*B := by
  have hs : (univ.sup fun j : Fin (3*3) => j.val/3+j.val%3)=4 := by decide
  unfold Ledger.layered
  rw [hs]
  simp only [sum_range_succ,sum_range_zero,zero_add]
  have c0 : (univ.filter fun j : Fin (3*3) => 0<j.val/3+j.val%3).card=8 := by decide
  have c1 : (univ.filter fun j : Fin (3*3) => 1<j.val/3+j.val%3).card=6 := by decide
  have c2 : (univ.filter fun j : Fin (3*3) => 2<j.val/3+j.val%3).card=3 := by decide
  have c3 : (univ.filter fun j : Fin (3*3) => 3<j.val/3+j.val%3).card=1 := by decide
  rw [c0,c1,c2,c3,harm1]
  have h8 := harm_le_q B 8; have h6 := harm_le_q B 6
  have h3 := harm_le_q B 3
  simp only [sum_range_succ,sum_range_zero] at h8 h6 h3
  norm_num at h8 h6 h3
  have : ((1000*(∑ t ∈ Ioc 0 8, B/t+∑ t ∈ Ioc 0 6, B/t+∑ t ∈ Ioc 0 3, B/t+B) : Nat) : ℚ)≤
      ((8002*B : Nat) : ℚ) := by
    push_cast at h8 h6 h3 ⊢
    have hB : (0:ℚ)≤B := by positivity
    linarith
  exact_mod_cast this

/-- Layered harmonic bound of the margin weights `J - 1 - j` for `b = 3`:
`H₁ + … + H₈ ≤ 16.461`. -/
theorem harm_layer2 (B : Nat) : 1000*Ledger.layered (fun j : Fin (3*3) => 3*3-1-j.val) B≤16461*B := by
  have hs : (univ.sup fun j : Fin (3*3) => 3*3-1-j.val)=8 := by decide
  unfold Ledger.layered
  rw [hs]
  simp only [sum_range_succ,sum_range_zero,zero_add]
  have c0 : (univ.filter fun j : Fin (3*3) => 0<3*3-1-j.val).card=8 := by decide
  have c1 : (univ.filter fun j : Fin (3*3) => 1<3*3-1-j.val).card=7 := by decide
  have c2 : (univ.filter fun j : Fin (3*3) => 2<3*3-1-j.val).card=6 := by decide
  have c3 : (univ.filter fun j : Fin (3*3) => 3<3*3-1-j.val).card=5 := by decide
  have c4 : (univ.filter fun j : Fin (3*3) => 4<3*3-1-j.val).card=4 := by decide
  have c5 : (univ.filter fun j : Fin (3*3) => 5<3*3-1-j.val).card=3 := by decide
  have c6 : (univ.filter fun j : Fin (3*3) => 6<3*3-1-j.val).card=2 := by decide
  have c7 : (univ.filter fun j : Fin (3*3) => 7<3*3-1-j.val).card=1 := by decide
  rw [c0,c1,c2,c3,c4,c5,c6,c7,harm1]
  have h8 := harm_le_q B 8; have h7 := harm_le_q B 7
  have h6 := harm_le_q B 6; have h5 := harm_le_q B 5
  have h4 := harm_le_q B 4; have h3 := harm_le_q B 3
  have h2 := harm_le_q B 2
  simp only [sum_range_succ,sum_range_zero] at h8 h7 h6 h5 h4 h3 h2
  norm_num at h8 h7 h6 h5 h4 h3 h2
  have : ((1000*(∑ t ∈ Ioc 0 8, B/t+∑ t ∈ Ioc 0 7, B/t+∑ t ∈ Ioc 0 6, B/t+∑ t ∈ Ioc 0 5, B/t+
      ∑ t ∈ Ioc 0 4, B/t+∑ t ∈ Ioc 0 3, B/t+∑ t ∈ Ioc 0 2, B/t+B) : Nat) : ℚ)≤((16461*B : Nat) : ℚ) := by
    push_cast at h8 h7 h6 h5 h4 h3 h2 ⊢
    have hB : (0:ℚ)≤B := by positivity
    linarith
  exact_mod_cast this

/-- The main parameters: `b = 3` (`J = 9`, `H₉ ≤ 2.829`), `Tmin = 107`. Chosen
to make the explicit constants small (see `Final`). -/
def std : Consts where
  b := 3
  hp := 2829
  hq := 1000
  Tmin := 107
  b_two := by norm_num
  hq_pos := by norm_num
  harm := harm9
  wp1 := 8002
  wp2 := 16461
  wharm1 := harm_layer1
  wharm2 := harm_layer2
  Tmin_band := by norm_num
  Tmin_six := by norm_num
  hJ_lt := by norm_num
  hb3 := by norm_num
  hq2 := by norm_num
  Tmin_lane := by norm_num
  Tmin_leaf := by norm_num

end SlidingPuzzle.NestedRouting.Corner
