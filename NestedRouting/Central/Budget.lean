import NestedRouting.Central.Tree

/-! The root's budget at lead one. Its lanes have constant length, so
everything but the quadrant trees costs `O(n²)`; each quadrant tree costs
twice its distance sum, at most `2T²(T-1)`, plus `Kl*T²+K0*T²*depth`. -/
namespace SlidingPuzzle.NestedRouting.Central
open Interface Placement Finset Corner

set_option linter.unusedSectionVars false

namespace CParams
variable {n : Nat} [NeZero n] (p : CParams n) (k : Consts) (hW : p.W=k.W) (hT : k.Tmin≤p.T)
  (G : Board n) (hG : ∀ y, y≠p.zP → G y≠0)

local notation "S" => p.rootSpec k hW hT G hG

theorem S_elen (j : Fin 4) : (S).elen j=2*p.m+1 := by
  change (p.exportLane j++[p.z j]).length=_
  unfold exportLane
  simp only [List.length_append,Seg.length_mk,List.length_singleton]
  have := p.AB; have := p.m_two; omega

theorem S_dlen (j : Fin 4) : (S).dlen j=2*p.m-1 := by
  change (p.e j :: p.deliveryLane j).length=_
  unfold deliveryLane
  simp only [List.length_cons,List.length_append,Seg.length_mk]
  have := p.AB; have := p.m_two; omega

theorem S_sc (j : Fin 4) : (S).serviceCost j=386+4*p.m := by
  unfold StarSpec.serviceCost
  have h1 : (S).L.hcost j=190 := rfl
  have h2 : ((S).L.accessTail j).length=2 := rfl
  have h3 := p.S_elen k hW hT G hG j
  have h4 := p.S_dlen k hW hT G hG j
  change 2*(S).L.hcost j+2*((S).L.accessTail j).length+(S).elen j+(S).dlen j+2=_
  rw [h1,h2,h3,h4]; have := p.m_two; omega

theorem S_cmax : (S).cmax≤386+4*p.m := by
  unfold StarSpec.cmax
  apply Finset.sup_le; intro j _; rw [p.S_sc k hW hT G hG j]

theorem kid_bud (j : Fin 4) : k.Bud (p.kid k hW hT G hG j) :=
  k.build_bud p.T hT 0 _ (p.quad j) _

theorem S_rmax : (S).rmax≤k.Kr*p.T := by
  unfold StarSpec.rmax
  apply Finset.sup_le; intro j _; exact (p.kid_bud k hW hT G hG j).1

theorem S_kidbase (j : Fin 4) : ((S).Q j).base≤2*(p.T*(p.T*(p.T-1)))+(k.Kl*(p.T*p.T)+k.K0*(p.T*p.T)*k.dep p.T) := by
  have h := (p.kid_bud k hW hT G hG j).2
  have hd := k.dsum_body_le (n:=n) (p.quad j)
  rw [←(p.kid k hW hT G hG j).cells_eq] at hd
  change (p.kid k hW hT G hG j).R.base≤_
  omega

theorem S_pop (j : Fin 4) : (S).pop j+6=(p.T-k.W)*p.T := by
  have h1 := Frame.cells_card (p.kid k hW hT G hG j).R.toFrame
  have h2 := (p.kid k hW hT G hG j).spare6
  have h3 := (p.kid k hW hT G hG j).cells_eq
  have h4 := k.card_bodyCells (n:=n) (p.quad j)
  change (p.kid k hW hT G hG j).R.M+(p.kid k hW hT G hG j).R.r+6=_
  rw [←h4,←h3]
  rw [h1]
  rw [h2]

theorem root_card : (S).frame.cells.card+2=n*n := by
  have h : (S).frame.cells=univ\{p.eP,p.zP} := by
    ext y
    have := p.root_cells k hW hT G hG (y:=y)
    change y∈(S).frame.cells ↔ _ at this
    rw [this]; simp
  have hez : p.eP≠p.zP := (S).eP_zP
  rw [h,card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_prod,Fintype.card_fin,
    card_pair hez]
  have : 2≤n*n := by have := p.N_le; have := p.T_big; nlinarith
  omega

def cR : Nat := 4*p.m+2*p.W+5

theorem r_root_arith {n T m W r : Nat} (hn1 : 2*T+2*m+1≤n) (hn2 : n≤2*T+2*m+2) (hWT : W≤T)
    (h : n*n=4*((T-W)*T-6)+r+6+2) (h6 : 6≤(T-W)*T) (h16 : 16≤n) : r≤(4*m+2*W+5)*n := by
  have hz : ((n*n : Nat) : Int)=4*(((T:Int)-W)*T-6)+r+8 := by
    rw [h]; push_cast [Nat.cast_sub h6,Nat.cast_sub hWT]; ring
  have a1 : ((n:Int)-2*T)*(n+2*T)≤(2*m+2)*(2*n) :=
    mul_le_mul (by omega) (by omega) (by positivity) (by positivity)
  have a2 : (4:Int)*W*T≤2*W*n := by
    have : (2*T:Int)≤n := by omega
    nlinarith [show (0:Int)≤W from by positivity]
  have a3 : (16:Int)≤n := by omega
  push_cast at hz
  suffices (r:Int)≤(4*m+2*W+5)*n by exact_mod_cast this
  nlinarith

theorem S_r (hn : n≤p.N+1) : (S).frame.r≤p.cR*n := by
  have h1 := Frame.cells_card (S).frame
  have h2 := p.root_card k hW hT G hG
  have h3 := (S).M_eq
  have hg6 : (S).frame.g=6 := p.markers_card
  have hp : ∀ j, (S).pop j=(p.T-k.W)*p.T-6 := by
    intro j; have := p.S_pop k hW hT G hG j; omega
  simp only [hp,sum_const,card_univ,Fintype.card_fin,smul_eq_mul] at h3
  have h6 : 6≤(p.T-p.W)*p.T := by
    have := p.T_big
    have : 12≤p.T-p.W := by omega
    nlinarith
  rw [hW] at h6
  unfold cR
  rw [hW]
  have := p.N_le; have := p.T_big
  exact r_root_arith (T:=p.T) (m:=p.m) (W:=k.W) (by unfold N at *; omega) (by unfold N at hn; omega)
    (by omega) (by omega) h6 (by unfold N at *; omega)

def X : Nat := 386+4*p.m
/-- The root's cost per board cell: one service per tile, the wrapper, direct
exchanges and the final sort of its own cells. -/
def Croot : Nat := p.X+374+8*p.cR+25*p.cR
/-- The root's cost per unit of side: rates, finishing slack and constants. -/
def Clin : Nat := 16*p.m*p.X+4*p.X+8*(2*p.m+3)+2+k.Kr*(16*p.m+12)+150+276*p.cR+3*p.X+3*k.Kr+658

theorem rate_aux (Y K n : Nat) (hn : 1≤n) : (Y+K*n)*3+(8*n+650)≤(3*Y+3*K+658)*n := by nlinarith

theorem root_budget (hn : n≤p.N+1) :
    (p.root k hW hT G hG).budget 1≤8*(p.T*(p.T*(p.T-1)))+4*((k.Kl*(p.T*p.T)+k.K0*(p.T*p.T)*k.dep p.T))+
      p.Croot*(n*n)+p.Clin k*n := by
  have hT1 : 1≤p.T := by have := p.T_big; omega
  have hTn : p.T≤n := by have := p.N_le; unfold N at *; omega
  have hn1 : 1≤n := by omega
  have hnn : n≤n*n := Nat.le_mul_of_pos_right n hn1
  have hTT : p.T*p.T≤n*n := Nat.mul_le_mul hTn hTn
  have h1n : 1≤n*n := by nlinarith
  have hED (j : Fin 4) : (S).elen j+(S).dlen j=4*p.m := by
    rw [p.S_elen k hW hT G hG j,p.S_dlen k hW hT G hG j]; have := p.m_two; omega
  have hpop (j : Fin 4) : (S).pop j≤p.T*p.T := by
    have := p.S_pop k hW hT G hG j
    have : (p.T-k.W)*p.T≤p.T*p.T := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    omega
  -- productive and service terms
  have hMr : (S).frame.M+(S).frame.r≤n*n := by
    have := Frame.cells_card (S).frame; have := p.root_card k hW hT G hG; omega
  have t1 : ∑ j, (S).serviceCost j*((S).pop j+(S).elen j+(S).dlen j)≤p.X*(n*n)+16*p.m*p.X*n := by
    calc _=∑ j : Fin 4, (p.X*(S).pop j+p.X*(4*p.m)) := by
          apply sum_congr rfl; intro j _
          rw [p.S_sc k hW hT G hG j,Nat.add_assoc,hED j]; unfold X; ring
      _=p.X*∑ j, (S).pop j+16*p.m*p.X := by rw [sum_add_distrib,←mul_sum]; simp; ring
      _≤p.X*(n*n)+16*p.m*p.X*n := by
          have hM := (S).M_eq
          have : ∑ j, (S).pop j≤n*n := by omega
          have := Nat.mul_le_mul_left p.X this
          have := Nat.le_mul_of_pos_right (16*p.m*p.X) (show 0<n by omega)
          omega
  have hzero : (S).lw1*∑ j, (S).ρ1 j+(S).lw2*∑ j, (S).ρ2 j=0 := by
    have : (S).lw1=0 := rfl; have : (S).lw2=0 := rfl; simp [*]
  have t2 : (S).cb*4≤4*p.X*n := by
    have := (S).cb_le_cmax.trans (p.S_cmax k hW hT G hG)
    calc (S).cb*4≤p.X*4 := Nat.mul_le_mul_right _ this
      _≤p.X*4*n := Nat.le_mul_of_pos_right _ (by omega)
      _=_ := by ring
  have t3 : ∑ j, (((S).Q j).base+2*(((S).L.accessTail j).length+((S).L.exportQ j).length))≤
      8*(p.T*(p.T*(p.T-1)))+4*((k.Kl*(p.T*p.T)+k.K0*(p.T*p.T)*k.dep p.T))+8*(2*p.m+3)*n := by
    calc _≤∑ _j : Fin 4, (2*(p.T*(p.T*(p.T-1)))+(k.Kl*(p.T*p.T)+k.K0*(p.T*p.T)*k.dep p.T)+2*(2+(2*p.m+1))) := by
          apply sum_le_sum; intro j _
          have := p.S_kidbase k hW hT G hG j
          have e1 : ((S).L.accessTail j).length=2 := rfl
          have e2 : ((S).L.exportQ j).length=2*p.m+1 := p.S_elen k hW hT G hG j
          rw [e1,e2]; omega
      _=4*(2*(p.T*(p.T*(p.T-1)))+(k.Kl*(p.T*p.T)+k.K0*(p.T*p.T)*k.dep p.T)+2*(2+(2*p.m+1))) := by simp
      _≤_ := by
          have : 4*(2*(2+(2*p.m+1)))≤8*(2*p.m+3)*n := by nlinarith
          omega
  have t4 : (S).rmax*(4+∑ j, ((S).elen j+(S).dlen j+2))≤k.Kr*(16*p.m+12)*n := by
    have hs : ∑ j : Fin 4, ((S).elen j+(S).dlen j+2)=4*(4*p.m+2) := by
      simp only [hED]; simp
    rw [hs]
    calc (S).rmax*(4+4*(4*p.m+2))≤k.Kr*p.T*(16*p.m+12) :=
          Nat.mul_le_mul (p.S_rmax k hW hT G hG) (by omega)
      _≤k.Kr*n*(16*p.m+12) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hTn)
      _=_ := by ring
  have hr := p.S_r k hW hT G hG hn
  have t5 : (S).wrapCost*((S).frame.M+(S).frame.r)≤374*(n*n) := by
    have : (S).wrapCost=374 := rfl
    rw [this]; omega
  have hdc : (S).dcost≤8*n+276 := by
    change 16*(n-p.c)+260≤_
    have := p.N_le; unfold N c at *; omega
  have t6 : (S).dxCost*(S).frame.r≤8*p.cR*(n*n)+276*p.cR*n := by
    have : (S).dxCost=(S).dcost := rfl
    rw [this]
    calc (S).dcost*(S).frame.r≤(8*n+276)*(p.cR*n) := Nat.mul_le_mul hdc (by omega)
      _=_ := by ring
  have t7 : 2*(S).connTail.length≤2*n := by
    have : (S).connTail.length=1 := rfl
    rw [this]; omega
  have hres : (S).own.card+(S).childSpare.card=(S).frame.r := by
    change _=((S).own∪(S).childSpare).card
    rw [card_union_of_disjoint]
    exact (S).disjoint_own_childCells.mono_right (S).childSpare_sub
  have hmk : (S).markers.card=6 := p.markers_card
  have t8 : 2*∑ x∈(S).resid, (S).fw x≤25*p.cR*(n*n)+150*n := by
    rw [show (S).fw=fun _ => rfw (n:=n) from rfl,sum_const,smul_eq_mul]
    have h2 := (S).resid_card
    rw [hres,hmk] at h2
    have hw : 2*rfw (n:=n)≤25*n := by unfold rfw; have := p.N_le; have := p.T_big; unfold N at *; omega
    have : (S).resid.card*(2*rfw (n:=n))≤(p.cR*n+6)*(25*n) :=
      Nat.mul_le_mul (by omega) hw
    have e : (p.cR*n+6)*(25*n)=25*p.cR*(n*n)+150*n := by ring
    have e2 : 2*((S).resid.card*rfw (n:=n))=(S).resid.card*(2*rfw (n:=n)) := by ring
    omega
  have trate : (S).rateP≤(3*p.X+3*k.Kr+658)*n := by
    unfold StarSpec.rateP StarSpec.dxCost
    have hwc : (S).wrapCost=374 := rfl
    have hc := (S).cb_le_cmax.trans (p.S_cmax k hW hT G hG)
    have l1 : (S).lw1=0 := rfl
    have l2 : (S).lw2=0 := rfl
    rw [l1,l2]
    have hm := p.S_rmax k hW hT G hG
    have h3 : (S).hp=3 := rfl
    have h1 : (S).hq=1 := rfl
    rw [h3,h1]
    simp only [Ledger.cdiv,Nat.add_sub_cancel,Nat.div_one]
    have hKT : k.Kr*p.T≤k.Kr*n := Nat.mul_le_mul_left _ hTn
    have hX : p.X≤p.X*n := Nat.le_mul_of_pos_right _ (by omega)
    unfold X at hX ⊢
    rw [hwc]
    simp only [Nat.zero_mul,Nat.add_zero]
    have k1 : (S).cb*3+(S).rmax*3+((S).dcost+374)≤((386+4*p.m)+k.Kr*n)*3+(8*n+650) := by
      have := Nat.mul_le_mul_right 3 (Nat.add_le_add hc (hm.trans hKT)); omega
    exact k1.trans (rate_aux _ _ _ (by omega))
  change (S).baseP+(S).rateP*1≤_
  unfold StarSpec.baseP
  have hstat : (S).dxCost*((S).frame.r-(S).stat.card)+∑ x∈(S).stat, (S).dw x=(S).dxCost*(S).frame.r := by
    have : (S).stat=∅ := rfl
    rw [this]; simp
  have e : p.Croot*(n*n)+p.Clin k*n=p.X*(n*n)+374*(n*n)+8*p.cR*(n*n)+25*p.cR*(n*n)+
      16*p.m*p.X*n+4*p.X*n+8*(2*p.m+3)*n+2*n+k.Kr*(16*p.m+12)*n+150*n+276*p.cR*n+
      (3*p.X+3*k.Kr+658)*n := by
    unfold Croot Clin; ring
  have hJ4 : ((4 : Nat) : Nat)=4 := rfl
  omega

end CParams
end SlidingPuzzle.NestedRouting.Central
