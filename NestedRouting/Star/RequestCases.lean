import NestedRouting.Star.Request

/-! The request law of a star node, case by case (the policy of `ReservePolicy`). -/
namespace SlidingPuzzle.NestedRouting.Interface
open Finset TileRoles
open SlidingPuzzle.NestedRouting.ReservePolicy

variable {n : Nat} [NeZero n] {J : Nat}

namespace StarSpec
variable {P : StarSpec n J}

omit [NeZero n] in
theorem updateRoles_disjoint {r : Roles n} (disj : ∀ i i', i≠i' → Disjoint (r i) (r i'))
    {y t : Tile n} (fresh : ∀ i, t∉r i) (ρ : Role) :
    ∀ i i', i≠i' → Disjoint (updateRoles r y t ρ i) (updateRoles r y t ρ i') := by
  intro i i' hii
  apply disjoint_left.mpr
  intro x h1 h2
  rw [mem_updateRoles] at h1 h2
  rcases h1 with ⟨hi,rfl⟩ | ⟨_,h1⟩ <;> rcases h2 with ⟨hi',hx⟩ | ⟨_,h2⟩
  · exact hii (hi.trans hi'.symm)
  · exact fresh i' h2
  · exact fresh i (hx ▸ h1)
  · exact disjoint_left.mp (disj i i' hii) h1 h2

omit [NeZero n] in
theorem updateRoles_src {r : Roles n} {y t : Tile n} {ρ : Role} (hρ : ρ≠.coreSource)
    (hy : y∉r .coreSource) : updateRoles r y t ρ .coreSource=r .coreSource := by
  ext x
  rw [mem_updateRoles]
  constructor
  · rintro (⟨h,_⟩ | ⟨_,hx⟩)
    · exact absurd h.symm hρ
    · exact hx
  · intro hx; exact Or.inr ⟨fun e => hy (e ▸ hx),hx⟩

omit [NeZero n] in
theorem updateRoles_fin {r : Roles n} {y t : Tile n} {ρ : Role} (hρ : ρ≠.coreFinal)
    (hy : y∉r .coreFinal) : updateRoles r y t ρ .coreFinal=r .coreFinal := by
  ext x
  rw [mem_updateRoles]
  constructor
  · rintro (⟨h,_⟩ | ⟨_,hx⟩)
    · exact absurd h.symm hρ
    · exact hx
  · intro hx; exact Or.inr ⟨fun e => hy (e ▸ hx),hx⟩

omit [NeZero n] in
theorem updateRoles_fin_core {r : Roles n} {y t : Tile n} (hy : y∉r .coreFinal) :
    updateRoles r y t .coreFinal .coreFinal=insertRole r t .coreFinal .coreFinal := by
  ext x
  rw [mem_updateRoles,mem_insertRole]
  constructor
  · rintro (h | ⟨_,hx⟩)
    · exact Or.inl h
    · exact Or.inr hx
  · rintro (h | hx)
    · exact Or.inl h
    · exact Or.inr ⟨fun e => hy (e ▸ hx),hx⟩

omit [NeZero n] in
theorem insertRole_src {r : Roles n} {t : Tile n} {ρ : Role} (hρ : ρ≠.coreSource) :
    insertRole r t ρ .coreSource=r .coreSource := by
  simp [insertRole,Ne.symm hρ]

/-- After one exchange at `eP`, every other tile of P is still in P. -/
theorem locate {B C : Board n} (fix : ∀ x, x∉P.frame.cells → x≠P.eP → C x=B x)
    {c : Tile n} (hc : c∈P.frame.cells.image B) (hne : c≠C P.eP) (hne' : C P.eP≠B P.eP) :
    ∃ q∈P.frame.cells, C q=c := by
  have h := image_exchange P.frame.cells P.eP_cells fix hne'
  have : c∈P.frame.cells.image C := by
    rw [h]; exact mem_insert_of_mem (mem_erase.mpr ⟨hne,hc⟩)
  simpa using this

theorem stat_cells {x : Cell n} (hx : x∈P.stat) : x∈P.frame.cells := P.own_sub_cells (P.stat_own x hx)

theorem stat_ne_eP {x : Cell n} (hx : x∈P.stat) : x≠P.eP := fun e => P.eP_cells (e ▸ stat_cells hx)

theorem stat_not_foot {x : Cell n} (hx : x∈P.stat) : ¬P.foot x :=
  P.not_foot (P.stat_loop x hx) (fun j hj => disjoint_left.mp (P.own_child j) (P.stat_own x hx) hj) (P.stat_K x hx)

/-- A response that exports no static reserve source: the static ledger is unchanged. -/
theorem respondKeep {β : Nat} {s : P.StarRec} {B : Board n} (hs : P.Holds β s B) (atZ : blank B=P.zP)
    (input : Arrival)
    (label : P.frame.Label input (B P.eP))
    (guard : RequestGuard P.frame.M P.frame.r s.counts input)
    (lead' : Lead β (advance s.counts input (select P.frame.M P.frame.r s.counts input)))
    {C : Board n} (path : Path B C) {led' : Fin J → Ledger.Counter}
    {ch' : (j : Fin J) → (P.Q j).Rec} {nreq' ndx' : Nat}
    (out : C P.eP∈s.roles (select P.frame.M P.frame.r s.counts input).role)
    (inner : P.Inner C (updateRoles s.roles (C P.eP) (B P.eP) input.role) led' ch' β
      (advance s.counts input (select P.frame.M P.frame.r s.counts input)).ec
      (advance s.counts input (select P.frame.M P.frame.r s.counts input)).ac false false)
    (blankC : blank C=P.zP) (fixC : ∀ x, x∉P.frame.cells → x≠P.eP → C x=B x)
    (hreq : nreq'≤s.nreq+1)
    (hdx : ndx'≤s.ndx+lateCharge P.frame.M P.frame.r s.counts input)
    (hfC : ∀ x∈s.fresh, C x=B x)
    (work : s.work+path.length≤P.totalWork ch'+P.ledCost led'+P.wrapCost*nreq'+P.dxCost*ndx'+
      ∑ x∈P.stat \ s.fresh, P.dw x)
    (idle' : ∀ j, (led' j).idle=0) (base rate : Nat) (Prep : Board n → Prop) :
    Nonempty (Response (P.core base rate Prep) β s B input P.eP) :=
  respond hs atZ input label guard lead' path out inner blankC fixC (nf':=s.nf) (fresh':=s.fresh) hreq
    (by omega) subset_rfl hfC (Nat.le_add_right _ _) hs.statInv.2.2.2 work idle' base rate Prep

/-- Export a reserve source by one direct exchange: from a fresh static cell
when one is left, at its position's cost; otherwise any reserve source. -/
theorem exportReserve {B : Board n} {r : Roles n} {led : Fin J → Ledger.Counter}
    {ch : (j : Fin J) → (P.Q j).Rec} {cap ecN acN : Nat}
    (h : P.Inner B r led ch cap ecN acN false false) (atZ : blank B=P.zP)
    (etok : B P.eP∉r .coreSource ∧ B P.eP∉r .coreFinal)
    {F : Finset (Cell n)} (hF : F⊆P.stat) (hFrs : ∀ x∈F, B x∈r .reserveSource)
    {c0 : Tile n} (hc0 : c0∈r .reserveSource) (hq0 : ∃ q∈P.frame.cells, B q=c0) :
    ∃ C : Board n, ∃ path : Path B C, ∃ ch' : (j : Fin J) → (P.Q j).Rec, ∃ F' : Finset (Cell n), ∃ d : Nat,
      blank C=P.zP ∧ C P.eP∈r .reserveSource ∧ P.Inner C r led ch' cap ecN acN false false ∧
      (∀ x, x∉P.frame.cells → x≠P.eP → C x=B x) ∧ P.totalWork ch'=P.totalWork ch ∧
      F'⊆F ∧ (∀ x∈F', C x=B x) ∧ (F.Nonempty → d=0) ∧ F'.card+1=F.card+d ∧
      path.length+∑ x∈P.stat \ F, P.dw x≤P.dxCost*d+∑ x∈P.stat \ F', P.dw x := by
  classical
  have disj := h.disjoint
  have rsNot {t : Tile n} (ht : t∈r .reserveSource) : t∉r .coreSource ∧ t∉r .coreFinal :=
    ⟨fun h' => disjoint_left.mp (disj _ _ (by decide)) ht h',fun h' => disjoint_left.mp (disj _ _ (by decide)) ht h'⟩
  by_cases hne : F.Nonempty
  · obtain ⟨q,hq⟩ := hne
    have hqs := hF hq
    have hrs := hFrs q hq
    obtain ⟨C,path,ch',bC,eC,_,innerC,fixC,len,w,fixN⟩ := h.directStepW atZ hqs (rsNot hrs) etok
    refine ⟨C,path,ch',F.erase q,0,bC,by rw [eC]; exact hrs,innerC,fixC,w,erase_subset _ _,?_,
      fun _ => rfl,?_,?_⟩
    · intro x hx
      obtain ⟨hxq,hxF⟩ := mem_erase.mp hx
      exact fixN x (stat_ne_eP (hF hxF)) hxq (P.stat_park x (hF hxF))
    · rw [card_erase_of_mem hq]; have := card_pos.mpr ⟨q,hq⟩; omega
    · have e : P.stat \ F.erase q=insert q (P.stat \ F) := by
        ext x; by_cases hx : x=q
        · subst hx; simp [hqs]
        · simp [hx]
      rw [e,sum_insert (by simp [hq])]
      omega
  · obtain ⟨q,hq,Bq⟩ := hq0
    obtain ⟨C,path,ch',bC,eC,_,innerC,fixC,len,w,_⟩ := h.directStep atZ hq (by rw [Bq]; exact rsNot hc0) etok
    refine ⟨C,path,ch',F,1,bC,by rw [eC,Bq]; exact hc0,innerC,fixC,w,subset_rfl,
      fun x hx => absurd ⟨x,hx⟩ hne,fun h' => absurd h' hne,rfl,?_⟩
    have : P.dxCost=P.dcost := rfl
    omega

/-- A request answered by one direct exchange exporting a reserve source. -/
theorem directReserve {β : Nat} {s : P.StarRec} {B : Board n} (hs : P.Holds β s B) (atZ : blank B=P.zP)
    (input : Arrival) (label : P.frame.Label input (B P.eP))
    (guard : RequestGuard P.frame.M P.frame.r s.counts input)
    (lead' : Lead β (advance s.counts input (select P.frame.M P.frame.r s.counts input)))
    (sel : select P.frame.M P.frame.r s.counts input=.reserve) (her : s.counts.er<P.frame.r)
    (hinS : input.role≠.coreSource) (hinF : input.role≠.coreFinal)
    (base rate : Nat) (Prep : Board n → Prop) :
    Nonempty (Response (P.core base rate Prep) β s B input P.eP) := by
  classical
  have fresh : ∀ i, B P.eP∉s.roles i := outside_fresh hs.sound.toState.inventory P.eP_cells
  have disj := hs.inner.disjoint
  have wl := hs.work_le
  obtain ⟨st1,st2,st3,st4⟩ := hs.statInv
  obtain ⟨c0,hc0⟩ := hs.sound.toState.source_reserve.mpr her
  have hq0 : ∃ q∈P.frame.cells, B q=c0 := by
    simpa using role_present hs.sound.inventory _ hc0
  obtain ⟨C,path,ch',F',d,bC,eC,innerC,fixC,wC,hF',hFC,hd0,hcard,hcost⟩ :=
    exportReserve hs.inner atZ ⟨fresh _,fresh _⟩ st1 st2 hc0 hq0
  have cS : C P.eP∉s.roles .coreSource := fun h => disjoint_left.mp (disj _ _ (by decide)) eC h
  have cF : C P.eP∉s.roles .coreFinal := fun h => disjoint_left.mp (disj _ _ (by decide)) eC h
  have advEc : (advance s.counts input (select P.frame.M P.frame.r s.counts input)).ec=s.counts.ec := by
    rw [sel]; simp [advance]
  have advAc : (advance s.counts input (select P.frame.M P.frame.r s.counts input)).ac=s.counts.ac := by
    cases input <;> simp_all [Arrival.role,advance]
  have lc : lateCharge P.frame.M P.frame.r s.counts input=0 := by simp [lateCharge,sel]
  have hsub := card_le_card st1
  have hsub' := card_le_card (hF'.trans st1)
  refine respond hs atZ input label guard lead' path (by rw [sel]; exact eC) ?_ bC fixC
    (led':=s.led) (ch':=ch') (nreq':=s.nreq) (ndx':=s.ndx+d) (nf':=s.nf+d) (fresh':=F') (by omega)
    (by omega) hF' (fun x hx => hFC x hx) (by rw [sel]; simp; omega)
    (fun hn => by have := hd0 (hn.mono hF'); have := st4 (hn.mono hF'); omega) ?_ hs.idle0 base rate Prep
  · rw [advEc,advAc]
    exact innerC.roles_congr (updateRoles_src hinS cS) (updateRoles_fin hinF cF)
      (updateRoles_disjoint disj fresh _)
  · rw [wC,Nat.mul_add]; omega

/-- A request answered by one direct exchange exporting a helper. -/
theorem directHelper {β : Nat} {s : P.StarRec} {B : Board n} (hs : P.Holds β s B) (atZ : blank B=P.zP)
    (input : Arrival) (label : P.frame.Label input (B P.eP))
    (guard : RequestGuard P.frame.M P.frame.r s.counts input)
    (lead' : Lead β (advance s.counts input (select P.frame.M P.frame.r s.counts input)))
    (sel : select P.frame.M P.frame.r s.counts input=.helper)
    (hinS : input.role≠.coreSource) (hinF : input.role≠.coreFinal)
    (base rate : Nat) (Prep : Board n → Prop) :
    Nonempty (Response (P.core base rate Prep) β s B input P.eP) := by
  classical
  have fresh : ∀ i, B P.eP∉s.roles i := outside_fresh hs.sound.toState.inventory P.eP_cells
  have disj := hs.inner.disjoint
  have wl := hs.work_le
  have six : 6≤P.frame.g := P.six
  have hpos : 0<(s.roles .helper).card :=
    lt_of_lt_of_le (by norm_num) (hs.sound.toState.helper_population six)
  obtain ⟨c0,hc0⟩ := card_pos.mp hpos
  have c0In : c0∈P.frame.cells.image B := role_present hs.sound.inventory _ hc0
  obtain ⟨q,hq,Bq⟩ : ∃ q∈P.frame.cells, B q=c0 := by simpa using c0In
  have c0S : c0∉s.roles .coreSource := fun h => disjoint_left.mp (disj _ _ (by decide)) hc0 h
  have c0F : c0∉s.roles .coreFinal := fun h => disjoint_left.mp (disj _ _ (by decide)) hc0 h
  obtain ⟨C,path,ch',bC,eC,_,innerC,fixC,lenC,wC,fixN⟩ := hs.inner.directStep atZ hq
    ⟨by rw [Bq]; exact c0S,by rw [Bq]; exact c0F⟩ ⟨fresh _,fresh _⟩
  have advEc : (advance s.counts input (select P.frame.M P.frame.r s.counts input)).ec=s.counts.ec := by
    rw [sel]; simp [advance]
  have advAc : (advance s.counts input (select P.frame.M P.frame.r s.counts input)).ac=s.counts.ac := by
    cases input <;> simp_all [Arrival.role,advance]
  have lc : lateCharge P.frame.M P.frame.r s.counts input=1 := by simp [lateCharge,sel]
  obtain ⟨st1,st2,_,_⟩ := hs.statInv
  refine respondKeep hs atZ input label guard lead' path (by rw [sel,eC,Bq]; exact hc0) ?_ bC fixC
    (led':=s.led) (ch':=ch') (nreq':=s.nreq) (ndx':=s.ndx+1) (by omega) (by omega) ?_ ?_ hs.idle0 base rate Prep
  · rw [advEc,advAc,eC,Bq]
    exact innerC.roles_congr (updateRoles_src hinS c0S) (updateRoles_fin hinF c0F)
      (updateRoles_disjoint disj fresh _)
  · intro x hx
    refine fixN x (stat_ne_eP (st1 hx)) ?_ (P.stat_park x (st1 hx))
    rintro rfl
    exact disjoint_left.mp (disj _ _ (by decide)) (st2 x hx) (Bq ▸ hc0)
  · rw [wC,Nat.mul_add,Nat.mul_one]; omega

/-- The request law of a star node. -/
theorem request {β : Nat} {s : P.StarRec} {B : Board n} (hs : P.Holds β s B) (input : Arrival)
    (atZ : blank B=P.zP) (label : P.frame.Label input (B P.eP))
    (guard : RequestGuard P.frame.M P.frame.r s.counts input)
    (lead' : Lead β (advance s.counts input (select P.frame.M P.frame.r s.counts input)))
    (base rate : Nat) (Prep : Board n → Prop) :
    Nonempty (Response (P.core base rate Prep) β s B input P.eP) := by
  classical
  have fresh : ∀ i, B P.eP∉s.roles i := outside_fresh hs.sound.toState.inventory P.eP_cells
  have capOk := P.cap_ok hs
  have hv := hs.sound.valid
  have hl := hs.lead
  simp only [Counts.Valid] at hv
  unfold Lead at hl
  have wl := hs.work_le
  have disj := hs.inner.disjoint
  obtain ⟨st1,st2,st3,st4⟩ := hs.statInv
  have tS : B P.eP∉s.roles .coreSource := fresh _
  have tF : B P.eP∉s.roles .coreFinal := fresh _
  have srcFin : ∀ x, x∈s.roles .coreSource → x∉s.roles .coreFinal :=
    fun x h1 h2 => disjoint_left.mp (disj _ _ (by decide)) h1 h2
  -- fresh cells are not foot, so wrapped services keep them
  have keepN {C : Board n} (fixN : ∀ x, ¬P.foot x → x≠P.eP → C x=B x) : ∀ x∈s.fresh, C x=B x :=
    fun x hx => fixN x (stat_not_foot (st1 hx)) (stat_ne_eP (st1 hx))
  cases input with
  | core =>
    obtain ⟨j0,home⟩ := home_of_goal (P:=P) label
    by_cases hec : s.counts.ec<P.frame.M
    · have sel : select P.frame.M P.frame.r s.counts .core=.core := by simp [select,hec]
      obtain ⟨C,path,led',ch',ySrc,yne,innerC,idleC,blankC,fixC,fixN,cost⟩ :=
        wrappedSource hs.inner atZ fresh .coreFinal true (by simp) (by decide) (fun _ => ⟨j0,home⟩)
          hec capOk (fun _ => by omega)
      refine respondKeep hs atZ .core label guard lead' path (by rw [sel]; exact ySrc) ?_ blankC fixC
        (led':=led') (ch':=ch') (nreq':=s.nreq+1) (ndx':=s.ndx) (le_refl _) (by omega) (keepN fixN) ?_
        (fun j => (idleC j).trans (hs.idle0 j)) base rate Prep
      · simp only [sel,advance,if_true,Arrival.role]; simpa using innerC
      · rw [Nat.mul_add,Nat.mul_one]; omega
    · have hec' : s.counts.ec=P.frame.M := by omega
      obtain ⟨C1,path1,led1,ch1,⟨x,hx,eqx⟩,y0S,y0F,inner1,idle1,blank1,fix1,fixN1,cost1⟩ :=
        wrappedToken hs.inner atZ fresh j0 home hec' capOk
      have keep1 := keepN fixN1
      have xe : x≠P.eP := fun e => P.eP_cells (e ▸ hx)
      have yne : C1 P.eP≠B P.eP := by rw [←eqx]; exact fun e => xe (B.injective e)
      have yIn : C1 P.eP∈P.frame.cells.image B := by rw [←eqx]; exact mem_image_of_mem B hx
      set rm := insertRole s.roles (B P.eP) .coreFinal with hrm
      have rmS : rm .coreSource=s.roles .coreSource := insertRole_src (by decide)
      have rmR : rm .reserveSource=s.roles .reserveSource := by simp [rm,insertRole]
      -- finishing with the exported tile `X` in place of `y0`
      have congrOut {X : Tile n} {C : Board n} {led' : Fin J → Ledger.Counter}
          {ch' : (j : Fin J) → (P.Q j).Rec} (hX : X∉s.roles .coreSource) (hXF : X∉s.roles .coreFinal)
          (hI : P.Inner C rm led' ch' β s.counts.ec (s.counts.ac+1) false false) :
          P.Inner C (updateRoles s.roles X (B P.eP) .coreFinal) led' ch' β s.counts.ec (s.counts.ac+1)
            false false :=
        hI.roles_congr ((updateRoles_src (by decide) hX).trans rmS.symm) (updateRoles_fin_core hXF)
          (updateRoles_disjoint disj fresh _)
      have etok : C1 P.eP∉rm .coreSource ∧ C1 P.eP∉rm .coreFinal :=
        ⟨by rw [rmS]; exact y0S,by rw [hrm,mem_insertRole]; rintro (⟨_,e⟩ | h); exact yne e; exact y0F h⟩
      have yS' : C1 P.eP∉s.roles .coreSource := y0S
      have yF' : C1 P.eP∉s.roles .coreFinal := y0F
      by_cases her : s.counts.er<P.frame.r
      · have sel : select P.frame.M P.frame.r s.counts .core=.reserve := by simp [select,hec',her]
        have lc : lateCharge P.frame.M P.frame.r s.counts .core=0 := by simp [lateCharge,sel]
        by_cases hy : C1 P.eP∈s.roles .reserveSource
        · refine respondKeep hs atZ .core label guard lead' path1 (by rw [sel]; exact hy) ?_ blank1 fix1
            (led':=led1) (ch':=ch1) (nreq':=s.nreq+1) (ndx':=s.ndx) (le_refl _) (by omega) keep1 ?_
            (fun j => (idle1 j).trans (hs.idle0 j)) base rate Prep
          · simp only [sel,advance,Arrival.role]; simpa using congrOut yS' yF' inner1
          · rw [Nat.mul_add,Nat.mul_one]; omega
        · -- export a reserve source, from a fresh static cell if one is left
          obtain ⟨c0,hc0⟩ := hs.sound.toState.source_reserve.mpr her
          have c0In : c0∈P.frame.cells.image B := role_present hs.sound.inventory _ hc0
          have hq0 : ∃ q∈P.frame.cells, C1 q=c0 := locate fix1 c0In (fun e => hy (e ▸ hc0)) yne
          obtain ⟨C2,path2,ch2,F',d,b2,e2,inner2,fix2,w2,hF',hFC,hd0,hcard,hcost⟩ :=
            exportReserve inner1 blank1 etok st1 (fun x hx => by rw [keep1 x hx,rmR]; exact st2 x hx)
              (by rw [rmR]; exact hc0) hq0
          rw [rmR] at e2
          have c0S : C2 P.eP∉s.roles .coreSource := fun h => disjoint_left.mp (disj _ _ (by decide)) e2 h
          have c0F : C2 P.eP∉s.roles .coreFinal := fun h => disjoint_left.mp (disj _ _ (by decide)) e2 h
          have hsub := card_le_card st1
          have hsub' := card_le_card (hF'.trans st1)
          refine respond hs atZ .core label guard lead' (path1.append path2)
            (by rw [sel]; exact e2) ?_ b2 (fun x hx he => (fix2 x hx he).trans (fix1 x hx he))
            (led':=led1) (ch':=ch2) (nreq':=s.nreq+1) (ndx':=s.ndx+d) (nf':=s.nf+d) (fresh':=F') (le_refl _)
            (by omega) hF' (fun x hx => (hFC x hx).trans (keep1 x (hF' hx))) (by rw [sel]; simp; omega)
            (fun hn => by have := hd0 (hn.mono hF'); have := st4 (hn.mono hF'); omega) ?_
            (fun j => (idle1 j).trans (hs.idle0 j)) base rate Prep
          · simp only [sel,advance,Arrival.role]; simpa using congrOut c0S c0F inner2
          · rw [Path.length_append,w2,Nat.mul_add,Nat.mul_one,Nat.mul_add]; omega
      · have sel : select P.frame.M P.frame.r s.counts .core=.helper := by simp [select,hec',her]
        have lc : lateCharge P.frame.M P.frame.r s.counts .core=1 := by simp [lateCharge,sel]
        by_cases hy : C1 P.eP∈s.roles .helper
        · refine respondKeep hs atZ .core label guard lead' path1 (by rw [sel]; exact hy) ?_ blank1 fix1
            (led':=led1) (ch':=ch1) (nreq':=s.nreq+1) (ndx':=s.ndx) (le_refl _) (by omega) keep1 ?_
            (fun j => (idle1 j).trans (hs.idle0 j)) base rate Prep
          · simp only [sel,advance,Arrival.role]; simpa using congrOut yS' yF' inner1
          · rw [Nat.mul_add,Nat.mul_one]; omega
        · have six : 6≤P.frame.g := P.six
          have ne : 0<(s.roles .helper).card :=
            lt_of_lt_of_le (by norm_num) (hs.sound.toState.helper_population six)
          obtain ⟨c0,hc0⟩ := card_pos.mp ne
          have c0In : c0∈P.frame.cells.image B := role_present hs.sound.inventory _ hc0
          obtain ⟨q,hq,Cq⟩ := locate fix1 c0In (fun e => hy (e ▸ hc0)) yne
          have c0S : c0∉s.roles .coreSource := fun h => disjoint_left.mp (disj _ _ (by decide)) hc0 h
          have c0F : c0∉s.roles .coreFinal := fun h => disjoint_left.mp (disj _ _ (by decide)) hc0 h
          have c0t : c0≠B P.eP := fun e => fresh _ (e ▸ hc0)
          obtain ⟨C2,path2,ch2,b2,se2,_,inner2,fix2,len2,w2,fixN2⟩ := inner1.directStep blank1 hq
            ⟨by rw [Cq,rmS]; exact c0S,by rw [Cq,hrm,mem_insertRole]; rintro (⟨_,e⟩ | h); exact c0t e; exact c0F h⟩
            etok
          refine respondKeep hs atZ .core label guard lead' (path1.append path2)
            (by rw [sel,se2,Cq]; exact hc0) ?_ b2 (fun x hx he => (fix2 x hx he).trans (fix1 x hx he))
            (led':=led1) (ch':=ch2) (nreq':=s.nreq+1) (ndx':=s.ndx+1) (le_refl _) (by omega) ?_ ?_
            (fun j => (idle1 j).trans (hs.idle0 j)) base rate Prep
          · simp only [sel,advance,Arrival.role,se2,Cq]; simpa using congrOut c0S c0F inner2
          · intro x hx
            refine (fixN2 x (stat_ne_eP (st1 hx)) ?_ (P.stat_park x (st1 hx))).trans (keep1 x hx)
            rintro rfl
            have := st2 x hx
            rw [←keep1 x hx,Cq] at this
            exact disjoint_left.mp (disj _ _ (by decide)) this hc0
          · rw [Path.length_append,w2,Nat.mul_add,Nat.mul_one,Nat.mul_add,Nat.mul_one]
            have : P.dxCost=P.dcost := rfl
            omega
  | helper =>
    by_cases hec : s.counts.ec<P.frame.M
    · have sel : select P.frame.M P.frame.r s.counts .helper=.core := by simp [select,hec]
      obtain ⟨C,path,led',ch',ySrc,yne,innerC,idleC,blankC,fixC,fixN,cost⟩ :=
        wrappedSource hs.inner atZ fresh .helper false (by simp) (by decide) (by simp)
          hec capOk (by simp)
      refine respondKeep hs atZ .helper label guard lead' path (by rw [sel]; exact ySrc) ?_ blankC fixC
        (led':=led') (ch':=ch') (nreq':=s.nreq+1) (ndx':=s.ndx) (le_refl _) (by omega) (keepN fixN) ?_
        (fun j => (idleC j).trans (hs.idle0 j)) base rate Prep
      · simp only [sel,advance,Arrival.role]; simpa using innerC
      · rw [Nat.mul_add,Nat.mul_one]; omega
    · -- core sources exhausted: a direct exchange with a reserve source
      have her : s.counts.er<P.frame.r := by
        change s.counts.ec<P.frame.M ∨ s.counts.er<P.frame.r at guard; omega
      have sel : select P.frame.M P.frame.r s.counts .helper=.reserve := by simp [select,hec]
      exact directReserve hs atZ .helper label guard lead' sel her (by decide) (by decide) base rate Prep
  | reserve =>
    by_cases her : s.counts.er<P.frame.r
    · have sel : select P.frame.M P.frame.r s.counts .reserve=.reserve := by simp [select,her]
      exact directReserve hs atZ .reserve label guard lead' sel her (by decide) (by decide) base rate Prep
    · have six : 6≤P.frame.g := P.six
      have hpos : 0<(s.roles .helper).card :=
        lt_of_lt_of_le (by norm_num) (hs.sound.toState.helper_population six)
      obtain ⟨h0,hh0⟩ := card_pos.mp hpos
      by_cases hec : s.counts.ec<P.frame.M
      · -- staging: park the reserve goal in place of a helper, then route the helper
        have sel : select P.frame.M P.frame.r s.counts .reserve=.core := by simp [select,her,hec]
        have lc : lateCharge P.frame.M P.frame.r s.counts .reserve=1 := by simp [lateCharge,sel]
        have h0In : h0∈P.frame.cells.image B := role_present hs.sound.inventory _ hh0
        obtain ⟨q,hq,Bq⟩ : ∃ q∈P.frame.cells, B q=h0 := by simpa using h0In
        have h0S : h0∉s.roles .coreSource := fun h => disjoint_left.mp (disj _ _ (by decide)) hh0 h
        have h0F : h0∉s.roles .coreFinal := fun h => disjoint_left.mp (disj _ _ (by decide)) hh0 h
        have h0t : h0≠B P.eP := fun e => fresh _ (e ▸ hh0)
        obtain ⟨C1,path1,ch1,b1,e1,q1,inner1,fix1,len1,w1,fixN1⟩ := hs.inner.directStep atZ hq
          ⟨by rw [Bq]; exact h0S,by rw [Bq]; exact h0F⟩ ⟨tS,tF⟩
        have keep1 : ∀ x∈s.fresh, C1 x=B x := by
          intro x hx
          refine fixN1 x (stat_ne_eP (st1 hx)) ?_ (P.stat_park x (st1 hx))
          rintro rfl
          exact disjoint_left.mp (disj _ _ (by decide)) (st2 x hx) (Bq ▸ hh0)
        set r1 := updateRoles s.roles h0 (B P.eP) .reserveFinal with hr1
        have r1S : r1 .coreSource=s.roles .coreSource := updateRoles_src (by decide) h0S
        have r1F : r1 .coreFinal=s.roles .coreFinal := updateRoles_fin (by decide) h0F
        have inner1' := inner1.roles_congr r1S r1F (updateRoles_disjoint disj fresh _)
        have fresh1 : ∀ i, C1 P.eP∉r1 i := by
          intro i hm
          rw [e1,Bq,hr1,mem_updateRoles] at hm
          rcases hm with ⟨_,e⟩ | ⟨ne,_⟩
          · exact h0t e
          · exact ne rfl
        obtain ⟨C2,path2,led2,ch2,ySrc,yne,inner2,idle2,b2,fix2,fixN2,cost2⟩ :=
          wrappedSource inner1' b1 fresh1 .helper false (by simp) (by decide) (by simp) hec capOk (by simp)
        have ySrc' : C2 P.eP∈s.roles .coreSource := by rw [←r1S]; exact ySrc
        have yF : C2 P.eP∉s.roles .coreFinal := srcFin _ ySrc'
        refine respondKeep hs atZ .reserve label guard lead' (path1.append path2) (by rw [sel]; exact ySrc')
          ?_ b2 (fun x hx he => (fix2 x hx he).trans (fix1 x hx he))
          (led':=led2) (ch':=ch2) (nreq':=s.nreq+1) (ndx':=s.ndx+1) (le_refl _) (by omega)
          (fun x hx => (fixN2 x (stat_not_foot (st1 hx)) (stat_ne_eP (st1 hx))).trans (keep1 x hx)) ?_
          (fun j => (idle2 j).trans (hs.idle0 j)) base rate Prep
        · simp only [sel,advance,Arrival.role,reduceCtorEq,if_false,if_true,Nat.add_zero]
          have target : updateRoles s.roles (C2 P.eP) (B P.eP) .reserveFinal .coreSource=
              updateRoles r1 (C2 P.eP) (C1 P.eP) .helper .coreSource := by
            ext x; simp only [mem_updateRoles,hr1]; constructor
            · rintro (⟨h,_⟩ | ⟨hx,hm⟩)
              · cases h
              · refine Or.inr ⟨hx,Or.inr ⟨?_,hm⟩⟩
                rintro rfl; exact h0S hm
            · rintro (⟨h,_⟩ | ⟨hx,⟨h,_⟩ | ⟨_,hm⟩⟩)
              · cases h
              · cases h
              · exact Or.inr ⟨hx,hm⟩
          have targetF : updateRoles s.roles (C2 P.eP) (B P.eP) .reserveFinal .coreFinal=
              updateRoles r1 (C2 P.eP) (C1 P.eP) .helper .coreFinal := by
            ext x; simp only [mem_updateRoles,hr1]; constructor
            · rintro (⟨h,_⟩ | ⟨hx,hm⟩)
              · cases h
              · refine Or.inr ⟨hx,Or.inr ⟨?_,hm⟩⟩
                rintro rfl; exact h0F hm
            · rintro (⟨h,_⟩ | ⟨hx,⟨h,_⟩ | ⟨_,hm⟩⟩)
              · cases h
              · cases h
              · exact Or.inr ⟨hx,hm⟩
          exact inner2.roles_congr target targetF (updateRoles_disjoint disj fresh _)
        · rw [Path.length_append,Nat.mul_add,Nat.mul_one,Nat.mul_add,Nat.mul_one]
          have : P.totalWork ch1=P.totalWork s.ch := w1
          have : P.dxCost=P.dcost := rfl
          omega
      · have sel : select P.frame.M P.frame.r s.counts .reserve=.helper := by simp [select,her,hec]
        exact directHelper hs atZ .reserve label guard lead' sel (by decide) (by decide) base rate Prep

end StarSpec
end SlidingPuzzle.NestedRouting.Interface
