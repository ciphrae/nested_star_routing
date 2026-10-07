import NestedRouting.Star.Node

/-! Requests of a star node. -/
namespace SlidingPuzzle.NestedRouting.Interface
open Finset TileRoles
open SlidingPuzzle.NestedRouting.ReservePolicy

variable {n : Nat} [NeZero n] {J : Nat}

namespace StarSpec
variable {P : StarSpec n J}

theorem idle_serve_real (led : Fin J → Ledger.Counter) (j : Fin J) (source : Bool) :
    ∀ i, (Function.update led j (Ledger.serve (led j) (P.pop j) true source) i).idle=(led i).idle := by
  intro i
  by_cases hij : i=j
  · subst hij; simp [Ledger.serve_idle]
  · simp [Function.update_of_ne hij]

omit [NeZero n] in
theorem mem_updateRoles_iff {r : Roles n} {y t x : Tile n} {ρ i : Role} (hyt : y≠t) :
    x∈updateRoles r y t ρ i ↔ x≠y ∧ x∈insertRole r t ρ i := by
  rw [mem_updateRoles,mem_insertRole]
  constructor
  · rintro (⟨hi,rfl⟩ | ⟨hx,hm⟩)
    · exact ⟨fun e => hyt e.symm,Or.inl ⟨hi,rfl⟩⟩
    · exact ⟨hx,Or.inr hm⟩
  · rintro ⟨hx,⟨hi,rfl⟩ | hm⟩
    · exact Or.inl ⟨hi,rfl⟩
    · exact Or.inr ⟨hx,hm⟩

theorem home_of_goal {t : Tile n} (ht : t∈P.frame.coreGoals) : ∃ j, t∈P.homeGoals j := by
  simp only [Frame.coreGoals,frame,homeCells,mem_image,mem_biUnion,mem_univ,true_and] at ht
  obtain ⟨x,⟨j,hx⟩,rfl⟩ := ht
  refine ⟨j,?_⟩
  simp only [homeGoals,Frame.coreGoals,Frame.reserveGoals,mem_union,mem_image]
  rw [P.goal_child j]
  simp only [mem_union] at hx
  rcases hx with hx | hx
  · exact Or.inl ⟨x,hx,rfl⟩
  · exact Or.inr ⟨x,hx,rfl⟩

namespace Inner
variable {B : Board n} {r : Roles n} {led : Fin J → Ledger.Counter}
  {ch : (j : Fin J) → (P.Q j).Rec} {cap ecNow acNow : Nat}

theorem cap_sum {cs cr : Bool} (h : P.Inner B r led ch cap ecNow acNow cs cr) :
    Ledger.totalCredit led=(ecNow : Int)-acNow := by
  unfold Ledger.totalCredit Ledger.Counter.credit
  rw [sum_sub_distrib,←Nat.cast_sum,←Nat.cast_sum,h.sumS,h.sumG]

theorem src_short {cs cr : Bool} (h : P.Inner B r led ch cap ecNow acNow cs cr) : ecNow≤P.frame.M := by
  rw [P.M_eq,←h.sumS]
  exact sum_le_sum (fun j _ => h.ledger.S_le j)

end Inner

/-- The wrapper around an optional real service and helper rounds: the
input `t` at `eP` (role `ρ`) is taken in, a P core source `y` comes out. -/
theorem wrappedSource {B : Board n} {r : Roles n} {led : Fin J → Ledger.Counter}
    {ch : (j : Fin J) → (P.Q j).Rec} {cap ec ac : Nat}
    (h : P.Inner B r led ch cap ec ac false false) (atZ : blank B=P.zP)
    (fresh : ∀ i, B P.eP∉r i) (ρ : Role) (real : Bool) (hρ : real=true ↔ ρ=.coreFinal)
    (hρs : ρ≠.coreSource) (home : real=true → ∃ j0, B P.eP∈P.homeGoals j0)
    (need : ec<P.frame.M) (capOk : Ledger.totalCredit led≤cap)
    (capReal : real=true → (ec : Int)-(ac+1)≤cap) :
    ∃ C : Board n, ∃ path : Path B C, ∃ led' : Fin J → Ledger.Counter,
      ∃ ch' : (j : Fin J) → (P.Q j).Rec,
      C P.eP∈r .coreSource ∧ C P.eP≠B P.eP ∧
      P.Inner C (updateRoles r (C P.eP) (B P.eP) ρ) led' ch' cap (ec+1) (ac+(if real then 1 else 0)) false false ∧
      (∀ i, (led' i).idle=(led i).idle) ∧ blank C=P.zP ∧ (∀ x, x∉P.frame.cells → x≠P.eP → C x=B x) ∧
      (∀ x, ¬P.foot x → x≠P.eP → C x=B x) ∧
      path.length+P.totalWork ch+P.ledCost led≤P.wrapCost+P.totalWork ch'+P.ledCost led' := by
  classical
  set t := B P.eP with ht
  set rm := insertRole r t ρ with hrm
  have tok := h.carrier_token
  have tokF := h.carrier_token_fin
  -- what the inner operation achieves
  let Φ : Board n → Nat → Prop := fun D len => ∃ led' : Fin J → Ledger.Counter,
    ∃ ch' : (j : Fin J) → (P.Q j).Rec,
    P.Inner D rm led' ch' cap (ec+1) (ac+(if real then 1 else 0)) true false ∧
    D (P.L.hub P.L.K)∈rm .coreSource ∧ (∀ i, (led' i).idle=(led i).idle) ∧
    len+P.totalWork ch+P.ledCost led≤P.totalWork ch'+P.ledCost led'
  have inner : ∀ B2 : Board n, Path B B2 → blank B2=P.L.hub P.L.w →
      (∀ y, P.foot y → y≠P.L.hub P.L.K → B2 y=B y) → B2 (P.L.hub P.L.K)=B P.eP →
      ∃ D : Board n, ∃ q : Path B2 D, blank D=P.L.hub P.L.w ∧ (∀ y, ¬P.foot y → D y=B2 y) ∧
        Φ D q.length := by
    intro B2 p2 blank2 agree hK2
    have h2 := h.start p2 agree hK2 fresh ρ hρs
    have crEq : decide (ρ=.coreFinal)=real := by
      cases real <;> simp_all
    rw [crEq] at h2
    -- rounds from a token carrier
    have roundsFrom : ∀ {D1 : Board n} {led1 : Fin J → Ledger.Counter} {ch1 : (j : Fin J) → (P.Q j).Rec},
        P.Inner D1 rm led1 ch1 cap ec (ac+(if real then 1 else 0)) false false →
        blank D1=P.L.hub P.L.w → Ledger.totalCredit led1≤cap →
        D1 (P.L.hub P.L.K)∉rm .coreSource → D1 (P.L.hub P.L.K)∉rm .coreFinal →
        ∃ D : Board n, ∃ q : Path D1 D, ∃ led2 : Fin J → Ledger.Counter,
          ∃ ch2 : (j : Fin J) → (P.Q j).Rec,
          blank D=P.L.hub P.L.w ∧ P.Inner D rm led2 ch2 cap (ec+1) (ac+(if real then 1 else 0)) true false ∧
          (∀ y, ¬P.foot y → D y=D1 y) ∧ D (P.L.hub P.L.K)∈rm .coreSource ∧
          (∀ i, (led2 i).idle=(led1 i).idle) ∧
          q.length+P.totalWork ch1+P.ledCost led1≤P.totalWork ch2+P.ledCost led2 :=
      fun h1 b1 c1 s1 f1 => Inner.rounds _ le_rfl h1 b1 need c1 s1 f1
    cases real with
    | false =>
      -- helper input: rounds only
      have tokS : B2 (P.L.hub P.L.K)∉rm .coreSource := by
        rw [hK2,hrm,mem_insertRole]; rintro (⟨h1,_⟩ | h1)
        · exact hρs h1.symm
        · exact fresh _ h1
      have tokF : B2 (P.L.hub P.L.K)∉rm .coreFinal := by
        rw [hK2,hrm,mem_insertRole]; rintro (⟨h1,_⟩ | h1)
        · exact absurd h1.symm (by simpa using hρ)
        · exact fresh _ h1
      obtain ⟨D,q,led2,ch2,bD,hD,fD,sD,iD,cost⟩ := roundsFrom (by simpa using h2) blank2 capOk tokS tokF
      exact ⟨D,q,bD,fD,led2,ch2,by simpa using hD,sD,iD,cost⟩
    | true =>
      have hρ' : ρ=.coreFinal := hρ.mp rfl
      obtain ⟨j0,home0⟩ := home rfl
      have carrierReal : B2 (P.L.hub P.L.K)∈rm .coreFinal ∧ B2 (P.L.hub P.L.K)∈P.homeGoals j0 := by
        rw [hK2]; exact ⟨by rw [hrm,mem_insertRole]; exact Or.inl ⟨hρ'.symm,rfl⟩,home0⟩
      obtain ⟨D1,q1,ch1,b1,h1,K1,f1,cost1⟩ :=
        h2.service' blank2 j0 true rfl (fun _ => carrierReal) (by simp) (by simp) capOk
      set led1 := Function.update led j0 (Ledger.serve (led j0) (P.pop j0) true
        (decide (B2 (P.ehead j0)∈rm .coreSource))) with hled1
      by_cases hsrc : B2 (P.ehead j0)∈rm .coreSource
      · rw [if_pos hsrc,decide_eq_true hsrc] at h1
        refine ⟨D1,q1,b1,f1,led1,ch1,by simpa using h1,by rw [K1]; exact hsrc,idle_serve_real led j0 _,?_⟩
        simpa using cost1
      · rw [if_neg hsrc,decide_eq_false hsrc] at h1
        have capOk1 : Ledger.totalCredit led1≤cap := by
          rw [h1.cap_sum]; have := capReal rfl; push_cast at this ⊢; simpa using this
        have s1 : D1 (P.L.hub P.L.K)∉rm .coreSource := by rw [K1]; exact hsrc
        have fK1 : D1 (P.L.hub P.L.K)∉rm .coreFinal := by
          rw [K1]; exact h2.exp_fin j0 _ (by rw [P.ce_cons]; exact List.mem_cons_self)
        obtain ⟨D,q,led2,ch2,bD,hD,fD,sD,iD,cost⟩ := roundsFrom (by simpa using h1) b1 capOk1 s1 fK1
        refine ⟨D,q1.append q,bD,fun y hy => (fD y hy).trans (f1 y hy),led2,ch2,hD,sD,
          fun i => (iD i).trans (idle_serve_real led j0 _ i),?_⟩
        rw [Path.length_append]
        omega
  obtain ⟨C,path,D,len,pDC,⟨led',ch',hD,sD,iD,cost⟩,blankC,Ce,CK,agreeF,agreeN,lenC⟩ :=
    P.exists_wrapped atZ Φ inner
  have yNe : D (P.L.hub P.L.K)≠t := by
    intro e
    rw [e,hrm,mem_insertRole] at sD
    rcases sD with ⟨h1,_⟩ | h1
    · exact hρs h1.symm
    · exact fresh _ h1
  have ySrc : D (P.L.hub P.L.K)∈r .coreSource := by
    rw [hrm,mem_insertRole] at sD
    rcases sD with ⟨h1,_⟩ | h1
    · exact absurd h1.symm hρs
    · exact h1
  have seedNe : B (P.L.hub P.L.K)≠t := fun e => P.eP_cells (B.injective e ▸ P.own_sub_cells P.K_own)
  have hC := hD.finishWrap pDC agreeF
    (by rw [CK,hrm,mem_insertRole]; rintro (⟨_,e⟩ | h1); exact seedNe e; exact tok h1)
    (by rw [CK,hrm,mem_insertRole]; rintro (⟨_,e⟩ | h1); exact seedNe e; exact tokF h1)
    (r'':=updateRoles r (D (P.L.hub P.L.K)) t ρ) (fun i x => mem_updateRoles_iff yNe)
  refine ⟨C,path,led',ch',by rw [Ce]; exact ySrc,by rw [Ce]; exact yNe,by rw [Ce]; exact hC,iD,blankC,?_,agreeN,?_⟩
  · intro x hx he
    exact agreeN x (fun hf => hx (P.foot_cells hf)) he
  · omega

/-- The core data of a star node, with its budget constants as parameters. -/
def core (P : StarSpec n J) (base rate : Nat) (Prepared : Board n → Prop) : Core n :=
  { P.frame with
    Rec := P.StarRec
    Holds := fun β s B => P.Holds β s B
    roles := fun s => s.roles
    counts := fun s => s.counts
    work := fun s => s.work
    base := base
    rate := rate
    Prepared := Prepared }

/-- Every request exports a core or a reserve source, or is charged late. -/
theorem tally_select (M r : Nat) (c : Counts) (input : Arrival) :
    c.ec+c.er+1≤(advance c input (select M r c input)).ec+(advance c input (select M r c input)).er+
      lateCharge M r c input := by
  unfold advance lateCharge select
  cases input <;> split_ifs <;> simp_all

/-- Package a completed request. -/
theorem respond {β : Nat} {s : P.StarRec} {B : Board n} (hs : P.Holds β s B) (atZ : blank B=P.zP)
    (input : Arrival)
    (label : P.frame.Label input (B P.eP))
    (guard : RequestGuard P.frame.M P.frame.r s.counts input)
    (lead' : Lead β (advance s.counts input (select P.frame.M P.frame.r s.counts input)))
    {C : Board n} (path : Path B C) {led' : Fin J → Ledger.Counter}
    {ch' : (j : Fin J) → (P.Q j).Rec} {nreq' ndx' nf' : Nat} {fresh' : Finset (Cell n)}
    (out : C P.eP∈s.roles (select P.frame.M P.frame.r s.counts input).role)
    (inner : P.Inner C (updateRoles s.roles (C P.eP) (B P.eP) input.role) led' ch' β
      (advance s.counts input (select P.frame.M P.frame.r s.counts input)).ec
      (advance s.counts input (select P.frame.M P.frame.r s.counts input)).ac false false)
    (blankC : blank C=P.zP) (fixC : ∀ x, x∉P.frame.cells → x≠P.eP → C x=B x)
    (hreq : nreq'≤s.nreq+1)
    (hdx : ndx'+s.nf≤s.ndx+nf'+lateCharge P.frame.M P.frame.r s.counts input)
    (hfs : fresh'⊆s.fresh) (hfC : ∀ x∈fresh', C x=B x)
    (hnf : nf'+(P.stat.card-fresh'.card)≤s.nf+(P.stat.card-s.fresh.card)+
      (if select P.frame.M P.frame.r s.counts input=.reserve then 1 else 0))
    (hnz : fresh'.Nonempty → nf'=0)
    (work : s.work+path.length≤P.totalWork ch'+P.ledCost led'+P.wrapCost*nreq'+P.dxCost*ndx'+
      ∑ x∈P.stat \ fresh', P.dw x)
    (idle' : ∀ j, (led' j).idle=0) (base rate : Nat) (Prep : Board n → Prop) :
    Nonempty (Response (P.core base rate Prep) β s B input P.eP) := by
  classical
  set c' := advance s.counts input (select P.frame.M P.frame.r s.counts input)
  have fresh : ∀ i, B P.eP∉s.roles i := outside_fresh hs.sound.toState.inventory P.eP_cells
  have outMem : C P.eP∈P.frame.cells.image B := by
    rw [hs.sound.inventory.exact]; exact mem_biUnion.mpr ⟨_,mem_univ _,out⟩
  have hne : C P.eP≠B P.eP := fun e => fresh _ (e ▸ out)
  have physical := image_exchange P.frame.cells P.eP_cells fixC hne
  have sound' := hs.sound.exchange input guard out fresh label physical
  have late' := late_invariant_step hs.sound.valid input guard hs.lateInv lead'
  let next : P.StarRec := ⟨updateRoles s.roles (C P.eP) (B P.eP) input.role,c',s.work+path.length,
    led',ch',nreq',ndx',s.late+lateCharge P.frame.M P.frame.r s.counts input,fresh',nf'⟩
  obtain ⟨st1,st2,st3,st4⟩ := hs.statInv
  have holds : P.Holds β next C := by
    refine ⟨sound',inner,lead',late',?_,?_,?_,?_,idle'⟩
    · have := hs.ndx_le
      simp only [next]
      omega
    · refine ⟨hfs.trans st1,?_,?_,hnz⟩
      · intro x hx
        have hxc : x∈P.frame.cells := P.own_sub_cells (P.stat_own x (st1 (hfs hx)))
        have hxe : x≠P.eP := fun e => P.eP_cells (e ▸ hxc)
        change C x∈updateRoles s.roles (C P.eP) (B P.eP) input.role .reserveSource
        rw [hfC x hx,mem_updateRoles]
        refine Or.inr ⟨?_,st2 x (hfs hx)⟩
        intro e
        rw [←hfC x hx] at e
        exact hxe (C.injective e)
      · have e1 : (advance s.counts input (select P.frame.M P.frame.r s.counts input)).er=
            s.counts.er+(if select P.frame.M P.frame.r s.counts input=.reserve then 1 else 0) := by
          unfold advance; rfl
        change nf'+(P.stat.card-fresh'.card)≤c'.er
        rw [e1]
        omega
    · have := hs.nreq_le
      have := tally_select P.frame.M P.frame.r s.counts input
      simp only [next,c']
      omega
    · exact work
  exact ⟨⟨C,path,next,holds,blankC.trans atZ.symm,fixC,out,rfl,rfl,le_refl _⟩⟩

namespace Inner
variable {B : Board n} {r : Roles n} {led : Fin J → Ledger.Counter}
  {ch : (j : Fin J) → (P.Q j).Rec} {cap ecNow acNow : Nat}

/-- The invariant sees roles only through core sources, core finals and disjointness. -/
theorem roles_congr {cs cr : Bool} (h : P.Inner B r led ch cap ecNow acNow cs cr) {r' : Roles n}
    (hS : r' .coreSource=r .coreSource) (hF : r' .coreFinal=r .coreFinal)
    (disj : ∀ i i', i≠i' → Disjoint (r' i) (r' i')) :
    P.Inner B r' led ch cap ecNow acNow cs cr :=
  h.congr (Equiv.refl _) (fun _ _ => rfl) (fun _ _ => rfl) hS hF disj
    (fun j => by simp) (fun j => by simp) rfl (fun j => h.child j) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

/-- A direct exchange of two tokens at the inner level. -/
theorem directStep (h : P.Inner B r led ch cap ecNow acNow false false) (atZ : blank B=P.zP)
    {q : Cell n} (hq : q∈P.frame.cells) (qtok : B q∉r .coreSource ∧ B q∉r .coreFinal)
    (_etok : B P.eP∉r .coreSource ∧ B P.eP∉r .coreFinal) :
    ∃ C : Board n, ∃ path : Path B C, ∃ ch' : (j : Fin J) → (P.Q j).Rec,
      blank C=P.zP ∧ C P.eP=B q ∧ (∃ x∈P.frame.cells, C x=B P.eP) ∧
      P.Inner C r led ch' cap ecNow acNow false false ∧
      (∀ x, x∉P.frame.cells → x≠P.eP → C x=B x) ∧ path.length≤P.dxCost ∧
      P.totalWork ch'=P.totalWork ch ∧ (∀ x, x≠P.eP → x≠q → ¬P.park x → C x=B x) := by
  obtain ⟨C,path,p1,h1,n1,blankC,se,sq,s1,fix,len⟩ := P.exists_direct atZ hq
  obtain ⟨ch',hC,hw⟩ := h.direct path hq h1 n1 atZ se sq s1 fix qtok
  refine ⟨C,path,ch',blankC,se,⟨p1,P.park_cells h1,s1⟩,hC,?_,len,?_,?_⟩
  · intro x hx he
    exact fix x he (fun e => hx (e ▸ hq)) (fun e => hx (e ▸ P.park_cells h1))
  · unfold totalWork; exact sum_congr rfl (fun j _ => hw j)
  · intro x he hq' hp
    exact fix x he hq' (fun e => hp (e ▸ h1))

/-- A direct exchange with a static cell, charged by its position. -/
theorem directStepW (h : P.Inner B r led ch cap ecNow acNow false false) (atZ : blank B=P.zP)
    {q : Cell n} (hq : q∈P.stat) (qtok : B q∉r .coreSource ∧ B q∉r .coreFinal)
    (_etok : B P.eP∉r .coreSource ∧ B P.eP∉r .coreFinal) :
    ∃ C : Board n, ∃ path : Path B C, ∃ ch' : (j : Fin J) → (P.Q j).Rec,
      blank C=P.zP ∧ C P.eP=B q ∧ (∃ x∈P.frame.cells, C x=B P.eP) ∧
      P.Inner C r led ch' cap ecNow acNow false false ∧
      (∀ x, x∉P.frame.cells → x≠P.eP → C x=B x) ∧ path.length≤P.dw q ∧
      P.totalWork ch'=P.totalWork ch ∧ (∀ x, x≠P.eP → x≠q → ¬P.park x → C x=B x) := by
  have hqc : q∈P.frame.cells := P.own_sub_cells (P.stat_own q hq)
  obtain ⟨C,path,p1,h1,n1,blankC,se,sq,s1,fix,len⟩ := P.dXw B q atZ hq
  obtain ⟨ch',hC,hw⟩ := h.direct path hqc h1 n1 atZ se sq s1 fix qtok
  refine ⟨C,path,ch',blankC,se,⟨p1,P.park_cells h1,s1⟩,hC,?_,len,?_,?_⟩
  · intro x hx he
    exact fix x he (fun e => hx (e ▸ hqc)) (fun e => hx (e ▸ P.park_cells h1))
  · unfold totalWork; exact sum_congr rfl (fun j _ => hw j)
  · intro x he hq' hp
    exact fix x he hq' (fun e => hp (e ▸ h1))

end Inner

/-- A core arrival after core exhaustion: one real service; a token comes out. -/
theorem wrappedToken {B : Board n} {r : Roles n} {led : Fin J → Ledger.Counter}
    {ch : (j : Fin J) → (P.Q j).Rec} {cap ec ac : Nat}
    (h : P.Inner B r led ch cap ec ac false false) (atZ : blank B=P.zP)
    (fresh : ∀ i, B P.eP∉r i) (j0 : Fin J) (home : B P.eP∈P.homeGoals j0)
    (done : ec=P.frame.M) (capOk : Ledger.totalCredit led≤cap) :
    ∃ C : Board n, ∃ path : Path B C, ∃ led' : Fin J → Ledger.Counter,
      ∃ ch' : (j : Fin J) → (P.Q j).Rec,
      (∃ x∈P.frame.cells, B x=C P.eP) ∧ C P.eP∉r .coreSource ∧ C P.eP∉r .coreFinal ∧
      P.Inner C (insertRole r (B P.eP) .coreFinal) led' ch' cap ec (ac+1) false false ∧
      (∀ i, (led' i).idle=(led i).idle) ∧ blank C=P.zP ∧ (∀ x, x∉P.frame.cells → x≠P.eP → C x=B x) ∧
      (∀ x, ¬P.foot x → x≠P.eP → C x=B x) ∧
      path.length+P.totalWork ch+P.ledCost led≤P.wrapCost+P.totalWork ch'+P.ledCost led' := by
  classical
  set t := B P.eP with ht
  set rm := insertRole r t .coreFinal with hrm
  have tok := h.carrier_token
  have tokF := h.carrier_token_fin
  have rmS : rm .coreSource=r .coreSource := by simp [rm,insertRole]
  let Φ : Board n → Nat → Prop := fun D len => ∃ led' : Fin J → Ledger.Counter,
    ∃ ch' : (j : Fin J) → (P.Q j).Rec,
    P.Inner D rm led' ch' cap ec (ac+1) false false ∧ D (P.L.hub P.L.K)=B (P.ehead j0) ∧
    (∀ i, (led' i).idle=(led i).idle) ∧
    len+P.totalWork ch+P.ledCost led≤P.totalWork ch'+P.ledCost led'
  have inner : ∀ B2 : Board n, Path B B2 → blank B2=P.L.hub P.L.w →
      (∀ y, P.foot y → y≠P.L.hub P.L.K → B2 y=B y) → B2 (P.L.hub P.L.K)=B P.eP →
      ∃ D : Board n, ∃ q : Path B2 D, blank D=P.L.hub P.L.w ∧ (∀ y, ¬P.foot y → D y=B2 y) ∧
        Φ D q.length := by
    intro B2 p2 blank2 agree hK2
    have h2 := h.start p2 agree hK2 fresh .coreFinal (by decide)
    simp only [decide_true] at h2
    have carrierReal : B2 (P.L.hub P.L.K)∈rm .coreFinal ∧ B2 (P.L.hub P.L.K)∈P.homeGoals j0 := by
      rw [hK2]; exact ⟨by rw [hrm,mem_insertRole]; exact Or.inl ⟨rfl,rfl⟩,home⟩
    obtain ⟨D1,q1,ch1,b1,h1,K1,f1,cost1⟩ :=
      h2.service' blank2 j0 true rfl (fun _ => carrierReal) (by simp) (by simp) capOk
    have notSrc : B2 (P.ehead j0)∉rm .coreSource := by
      intro hs
      rw [if_pos hs] at h1
      have := h1.src_short
      omega
    rw [if_neg notSrc,decide_eq_false notSrc] at h1
    rw [decide_eq_false notSrc] at cost1
    have eh : B2 (P.ehead j0)=B (P.ehead j0) := by
      apply agree
      · exact Or.inl ⟨j0,Or.inl (List.head_mem _)⟩
      · intro e
        exact (P.L.hub_loop j0).1 (e ▸ P.L.mem_loop_of_exportQ (List.head_mem _))
    exact ⟨D1,q1,b1,f1,_,ch1,by simpa using h1,K1.trans eh,idle_serve_real led j0 _,cost1⟩
  obtain ⟨C,path,D,len,pDC,⟨led',ch',hD,DK,iD,cost⟩,blankC,Ce,CK,agreeF,agreeN,lenC⟩ :=
    P.exists_wrapped atZ Φ inner
  have y0src : D (P.L.hub P.L.K)∉rm .coreSource := hD.carrier_token
  have y0fin : D (P.L.hub P.L.K)∉rm .coreFinal := hD.carrier_token_fin
  have seedNe : B (P.L.hub P.L.K)≠t := fun e => P.eP_cells (B.injective e ▸ P.own_sub_cells P.K_own)
  obtain ⟨ce',cd',cells'⟩ := Inner.lanes_agree agreeF
  have hC : P.Inner C rm led' ch' cap ec (ac+1) false false := by
    apply hD.recarrier hD.disjoint ce' cd' cells' (fun j => (P.Q j).transport (hD.child j) pDC (cells' j))
    · exact fun _ _ _ => Iff.rfl
    · exact fun _ _ _ => Iff.rfl
    · intro hs; rw [CK,rmS] at hs; exact absurd hs tok
    · intro hs; rw [CK,hrm,mem_insertRole] at hs
      rcases hs with ⟨_,e⟩ | hs
      · exact absurd e seedNe
      · exact absurd hs tokF
    · intro hs; exact absurd hs y0src
    · intro hs; exact absurd hs y0fin
  refine ⟨C,path,led',ch',⟨P.ehead j0,P.exportQ_cells j0 (List.head_mem _),by rw [Ce,DK]⟩,?_,?_,hC,
    iD,blankC,fun x hx he => agreeN x (fun hf => hx (P.foot_cells hf)) he,agreeN,by omega⟩
  · rw [Ce]; rw [rmS] at y0src; exact y0src
  · rw [Ce]; intro hf; exact y0fin (by rw [hrm,mem_insertRole]; exact Or.inr hf)

end StarSpec
end SlidingPuzzle.NestedRouting.Interface
