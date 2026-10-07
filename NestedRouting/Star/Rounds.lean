import NestedRouting.Star.InnerService

/-! Helper rounds: from a token carrier, serve least-credit active spokes
until a core source arrives. Every token popped from an active spoke is an
early one, so the rounds terminate. Costs are kept as a potential
`ledCost = Σ_j serviceCost j · k_j`. -/
namespace SlidingPuzzle.NestedRouting.Interface
open Finset TileRoles
open SlidingPuzzle.NestedRouting.ReservePolicy

variable {n : Nat} [NeZero n] {J : Nat}

namespace StarSpec
variable (P : StarSpec n J)

def ledCost (led : Fin J → Ledger.Counter) : Nat := ∑ j, P.serviceCost j*(led j).k

/-- The cells services may change: lanes, children and the carrier. -/
def foot (y : Cell n) : Prop :=
  (∃ j, y∈P.L.exportQ j ∨ y∈P.L.deliveryQ j ∨ y∈(P.Q j).cells) ∨ y=P.L.hub P.L.K

theorem ledCost_update (led : Fin J → Ledger.Counter) (j : Fin J) (c : Ledger.Counter)
    (hk : c.k=(led j).k+1) :
    P.ledCost (Function.update led j c)=P.ledCost led+P.serviceCost j := by
  unfold ledCost
  rw [←add_sum_erase _ _ (mem_univ j),←add_sum_erase _ _ (mem_univ j)]
  have rest : ∑ x ∈ univ.erase j, P.serviceCost x*(Function.update led j c x).k=
      ∑ x ∈ univ.erase j, P.serviceCost x*(led x).k := by
    apply sum_congr rfl
    intro x hx
    rw [Function.update_of_ne (ne_of_mem_erase hx)]
  rw [rest,Function.update_self,hk]
  ring

theorem foot_cells {y : Cell n} (hy : P.foot y) : y∈P.frame.cells := by
  rcases hy with ⟨j,h | h | h⟩ | rfl
  · exact P.own_sub_cells (P.loop_own j y (P.L.mem_loop_of_exportQ h))
  · exact P.own_sub_cells (P.loop_own j y (P.L.mem_loop_of_deliveryQ h))
  · exact P.child_sub_cells j h
  · exact P.own_sub_cells P.K_own

theorem exportQ_cells (j : Fin J) {y : Cell n} (hy : y∈P.L.exportQ j) : y∈P.frame.cells :=
  P.own_sub_cells (P.loop_own j y (P.L.mem_loop_of_exportQ hy))

theorem totalCredit_update (led : Fin J → Ledger.Counter) (j : Fin J) (c : Ledger.Counter)
    (hc : c.credit=(led j).credit) : Ledger.totalCredit (Function.update led j c)=Ledger.totalCredit led := by
  unfold Ledger.totalCredit
  rw [←add_sum_erase _ _ (mem_univ j),←add_sum_erase _ _ (mem_univ j)]
  have rest : ∑ x ∈ univ.erase j, (Function.update led j c x).credit=∑ x ∈ univ.erase j, (led x).credit := by
    apply sum_congr rfl
    intro x hx
    rw [Function.update_of_ne (ne_of_mem_erase hx)]
  rw [rest,Function.update_self,hc]

namespace Inner
variable {P} {B : Board n} {r : Roles n} {led : Fin J → Ledger.Counter}
  {ch : (j : Fin J) → (P.Q j).Rec} {cap ecNow acNow : Nat} {cs cr : Bool}

/-- A token at the export head of an active spoke is an early one. -/
theorem early_of_token (h : P.Inner B r led ch cap ecNow acNow cs cr) (j : Fin J)
    (hact : (led j).S<P.pop j) (htok : B (P.ehead j)∉r .coreSource) : (led j).k<P.elen j := by
  by_contra hk
  have hk' : P.elen j≤(led j).k := by omega
  have ceB := P.ce_cons B j
  have hlen : 0<(P.ce B j).length := by rw [ceB]; simp
  have h0 : (P.ce B j)[0]=B (P.ehead j) := by simp [ceB]
  obtain ⟨sl,rest⟩ := h.entered j 0 hlen (by simp [ce,elen] at hk' ⊢; omega) (by rw [h0]; exact htok)
  have zero : (P.ce B j).countP (fun t => t∈r .coreSource)=0 := by
    rw [List.countP_eq_zero]
    intro t ht
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp ht
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simpa [h0] using htok
    · simpa using rest i hi hpos
  have bS := h.bridgeS j
  rw [zero] at bS
  obtain ⟨s1,s2⟩ := sl
  unfold pop at hact
  omega

/-- A service, with its receipt in potential form and its footprint in P. -/
theorem service' (h : P.Inner B r led ch cap ecNow acNow false cr)
    (atW : blank B=P.L.hub P.L.w) (j : Fin J) (real : Bool) (hcr : cr=real)
    (carrierReal : real=true → B (P.L.hub P.L.K)∈r .coreFinal ∧ B (P.L.hub P.L.K)∈P.homeGoals j)
    (carrierTok : real=false → B (P.L.hub P.L.K)∉r .coreSource ∧ B (P.L.hub P.L.K)∉r .coreFinal)
    (spoke : real=false → (led j).S<P.pop j →
      ∀ i∈Ledger.active P.pop led, (led j).credit≤(led i).credit)
    (capOk : Ledger.totalCredit led≤cap) :
    ∃ C : Board n, ∃ path : Path B C, ∃ ch' : (j : Fin J) → (P.Q j).Rec,
      blank C=P.L.hub P.L.w ∧
      P.Inner C r (Function.update led j (Ledger.serve (led j) (P.pop j) real
          (decide (B (P.ehead j)∈r .coreSource)))) ch' cap
        (ecNow+(if B (P.ehead j)∈r .coreSource then 1 else 0)) (acNow+(if real then 1 else 0))
        (decide (B (P.ehead j)∈r .coreSource)) false ∧
      C (P.L.hub P.L.K)=B (P.ehead j) ∧
      (∀ y, ¬P.foot y → C y=B y) ∧
      path.length+P.totalWork ch+P.ledCost led≤P.totalWork ch'+
        P.ledCost (Function.update led j (Ledger.serve (led j) (P.pop j) real
          (decide (B (P.ehead j)∈r .coreSource)))) := by
  obtain ⟨C,path,ch',blankC,inner,CK,_,fixC,cost⟩ :=
    h.service atW j real hcr carrierReal carrierTok spoke capOk
  refine ⟨C,path,ch',blankC,inner,CK,?_,?_⟩
  · intro y hy
    apply fixC y
    · exact fun he => hy (Or.inl ⟨j,Or.inl he⟩)
    · exact fun hd => hy (Or.inl ⟨j,Or.inr (Or.inl hd)⟩)
    · exact fun hq => hy (Or.inl ⟨j,Or.inr (Or.inr hq)⟩)
    · exact fun hk => hy (Or.inr hk)
  · rw [P.ledCost_update led j _ (Ledger.serve_k _ _ _ _)]
    omega

end Inner

namespace Inner
variable {P} {r : Roles n} {cap ecNow acNow : Nat}

theorem idle_serve_active (led : Fin J → Ledger.Counter) (j : Fin J) (real source : Bool)
    (hact : (led j).S<P.pop j) :
    ∀ i, (Function.update led j (Ledger.serve (led j) (P.pop j) real source) i).idle=(led i).idle := by
  intro i
  by_cases hij : i=j
  · subst hij; simp [Ledger.serve_idle,hact]
  · simp [Function.update_of_ne hij]

theorem measure_drop (led : Fin J → Ledger.Counter) (j : Fin J) (c : Ledger.Counter)
    (hk : c.k=(led j).k+1) (hlt : (led j).k<P.elen j) :
    ∑ i, (P.elen i-(Function.update led j c i).k)+1≤∑ i, (P.elen i-(led i).k) := by
  rw [←add_sum_erase _ _ (mem_univ j),←add_sum_erase _ _ (mem_univ j)]
  have rest : ∑ x ∈ univ.erase j, (P.elen x-(Function.update led j c x).k)=
      ∑ x ∈ univ.erase j, (P.elen x-(led x).k) := by
    apply sum_congr rfl
    intro x hx
    rw [Function.update_of_ne (ne_of_mem_erase hx)]
  rw [rest,Function.update_self,hk]
  omega

theorem active_nonempty {led : Fin J → Ledger.Counter} (sumS : ∑ j, (led j).S=ecNow)
    (need : ecNow<P.frame.M) : (Ledger.active P.pop led).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have all : ∀ j, P.pop j≤(led j).S := by
    intro j
    by_contra hj
    have : j∈Ledger.active P.pop led := by simp [Ledger.active]; omega
    rw [hne] at this
    simp at this
  have := sum_le_sum (s:=univ) (fun j _ => all j)
  rw [P.M_eq] at need
  omega

/-- Helper rounds until a core source is in the carrier. -/
theorem rounds (m : Nat) : ∀ {B : Board n} {led : Fin J → Ledger.Counter} {ch : (j : Fin J) → (P.Q j).Rec},
    ∑ j, (P.elen j-(led j).k)≤m →
    P.Inner B r led ch cap ecNow acNow false false → blank B=P.L.hub P.L.w →
    ecNow<P.frame.M → Ledger.totalCredit led≤cap →
    B (P.L.hub P.L.K)∉r .coreSource → B (P.L.hub P.L.K)∉r .coreFinal →
    ∃ C : Board n, ∃ path : Path B C, ∃ led' : Fin J → Ledger.Counter,
      ∃ ch' : (j : Fin J) → (P.Q j).Rec,
      blank C=P.L.hub P.L.w ∧ P.Inner C r led' ch' cap (ecNow+1) acNow true false ∧
      (∀ y, ¬P.foot y → C y=B y) ∧ C (P.L.hub P.L.K)∈r .coreSource ∧ (∀ i, (led' i).idle=(led i).idle) ∧
      path.length+P.totalWork ch+P.ledCost led≤P.totalWork ch'+P.ledCost led' := by
  induction m with
  | zero =>
    intro B led ch hm h atW need capOk hKs hKf
    obtain ⟨j,hj,least⟩ := exists_min_image _ (fun i => (led i).credit) (active_nonempty h.sumS need)
    obtain ⟨C,path,ch',blankC,inner,CK,fixC,cost⟩ :=
      h.service' atW j false rfl (by simp) (fun _ => ⟨hKs,hKf⟩) (fun _ _ => least) capOk
    by_cases hsrc : B (P.ehead j)∈r .coreSource
    · rw [if_pos hsrc,decide_eq_true hsrc] at inner
      rw [decide_eq_true hsrc] at cost
      have hact : (led j).S<P.pop j := by simpa [Ledger.active] using hj
      exact ⟨C,path,_,ch',blankC,by simpa using inner,fixC,CK ▸ hsrc,
        idle_serve_active (P:=P) led j false true hact,cost⟩
    · have hact : (led j).S<P.pop j := by simpa [Ledger.active] using hj
      have := h.early_of_token j hact hsrc
      have hpos : 0<P.elen j-(led j).k := by omega
      have : P.elen j-(led j).k≤∑ i, (P.elen i-(led i).k) :=
        single_le_sum (f:=fun i => P.elen i-(led i).k) (fun _ _ => Nat.zero_le _) (mem_univ j)
      omega
  | succ m ih =>
    intro B led ch hm h atW need capOk hKs hKf
    obtain ⟨j,hj,least⟩ := exists_min_image _ (fun i => (led i).credit) (active_nonempty h.sumS need)
    obtain ⟨C,path,ch',blankC,inner,CK,fixC,cost⟩ :=
      h.service' atW j false rfl (by simp) (fun _ => ⟨hKs,hKf⟩) (fun _ _ => least) capOk
    by_cases hsrc : B (P.ehead j)∈r .coreSource
    · rw [if_pos hsrc,decide_eq_true hsrc] at inner
      rw [decide_eq_true hsrc] at cost
      have hact : (led j).S<P.pop j := by simpa [Ledger.active] using hj
      exact ⟨C,path,_,ch',blankC,by simpa using inner,fixC,CK ▸ hsrc,
        idle_serve_active (P:=P) led j false true hact,cost⟩
    · rw [if_neg hsrc,decide_eq_false hsrc] at inner
      rw [decide_eq_false hsrc] at cost
      simp only [Nat.add_zero,Bool.false_eq_true,if_false] at inner
      have hact : (led j).S<P.pop j := by simpa [Ledger.active] using hj
      have early := h.early_of_token j hact hsrc
      have drop := measure_drop (P:=P) led j (Ledger.serve (led j) (P.pop j) false false) (Ledger.serve_k _ _ _ _) early
      have capOk' : Ledger.totalCredit (Function.update led j
          (Ledger.serve (led j) (P.pop j) false false))≤cap := by
        rw [totalCredit_update]
        · exact capOk
        · rw [Ledger.serve_credit]; simp
      have hKs' : C (P.L.hub P.L.K)∉r .coreSource := by rw [CK]; exact hsrc
      have hKf' : C (P.L.hub P.L.K)∉r .coreFinal := by
        rw [CK]; exact h.exp_fin j _ (by rw [P.ce_cons]; exact List.mem_cons_self)
      obtain ⟨C2,path2,led2,ch2,blank2,inner2,fix2,src2,idle2,cost2⟩ :=
        ih (by omega) inner blankC (by simpa using need) capOk' hKs' hKf'
      refine ⟨C2,path.append path2,led2,ch2,blank2,inner2,
        fun y hy => (fix2 y hy).trans (fixC y hy),src2,
        fun i => (idle2 i).trans (idle_serve_active (P:=P) led j false false hact i),?_⟩
      rw [Path.length_append]
      omega

end Inner

end StarSpec
end SlidingPuzzle.NestedRouting.Interface
