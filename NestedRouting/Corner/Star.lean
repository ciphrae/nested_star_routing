import NestedRouting.Corner.Layout

/-! The corner layout as a `StarLayout`. -/
namespace SlidingPuzzle.NestedRouting.Corner
open Interface Placement

namespace Params
variable (p : Params) {n : Nat} [NeZero n] (q : Placement p.T n) [NeZero p.T]

omit [NeZero n] [NeZero p.T] in
theorem hub_adj : ∀ a b, gridDistance a b=1 → gridDistance (p.hub q a) (p.hub q b)=1 := by
  intro a b h
  unfold hub; rw [Placement.distance]; exact h

omit [NeZero n] in
/-- Equal local cells have equal coordinates. -/
theorem coords {r c r' c' : Nat} (hr : r<p.T) (hc : c<p.T) (hr' : r'<p.T) (hc' : c'<p.T)
    (h : q.loc r c=q.loc r' c') : r=r' ∧ c=c' := q.loc_inj hr hc hr' hc' h

omit [NeZero n] in
theorem hubK : p.hub q p.K=q.loc (p.W+1) 1 := by unfold K; rw [hub_loc]
omit [NeZero n] in
theorem hubU : p.hub q p.u=q.loc (p.W+1) (p.M0+2) := by unfold u; rw [hub_loc]
omit [NeZero n] in
theorem hubV : p.hub q p.v=q.loc (p.W+1) (p.M0+3) := by unfold v; rw [hub_loc]
omit [NeZero n] in
theorem hubW : p.hub q p.w=q.loc p.W 2 := by unfold w; rw [hub_loc]; simp
omit [NeZero n] in
theorem hubU2 : p.hub q p.u2=q.loc (p.W+1) (p.M0+4) := by unfold u2; rw [hub_loc]

omit [NeZero p.T] in
theorem hub_bound : p.W+1<p.T ∧ p.M0+4<p.T := by
  have := p.hub_fit; unfold W M0 J at *; constructor <;> omega

omit [NeZero n] in
theorem adjH {r c c' : Nat} (hr : r<p.T) (hc : c<p.T) (hc' : c'<p.T) (h : c'=c+1 ∨ c=c'+1) :
    gridDistance (q.loc r c) (q.loc r c')=1 := by
  rw [q.loc_dist hr hc hr hc']; rcases h with rfl | rfl <;> simp [Nat.dist]

omit [NeZero n] in
theorem adjV {r r' c : Nat} (hr : r<p.T) (hr' : r'<p.T) (hc : c<p.T) (h : r'=r+1 ∨ r=r'+1) :
    gridDistance (q.loc r c) (q.loc r' c)=1 := by
  rw [q.loc_dist hr hc hr' hc]; rcases h with rfl | rfl <;> simp [Nat.dist]

omit [NeZero n] in
theorem chained_single (x : Cell n) : Chained [x] := List.isChain_singleton x

omit [NeZero n] in
theorem access_chain (j : Fin p.J) : Chained (p.hub q p.w :: p.accessTail q j) := by
  have hb := p.bounds j.isLt
  have ha := hb.a_eq; have hm := hb.M0_le
  have hW : p.W+2<p.T := by omega
  have ha4 := hb.a_ge
  rw [hubW]
  change Chained ([q.loc p.W 2]++(_++_))
  apply Seg.chained_append (chained_single _)
  · apply Seg.chained_append (Seg.chained_right q (by omega) (by omega))
      (Seg.chained_down q (by omega) (by omega))
    intro a b ha' hb'
    rw [Seg.getLast?_mk _ _ (by omega)] at ha'
    rw [Seg.head?_mk _ _ (by omega)] at hb'
    cases ha'; cases hb'
    have e1 : 3+(p.a j-2-1)=p.a j := by omega
    rw [e1,Nat.add_zero]
    exact p.adjV q (by omega) (by omega) (by omega) (Or.inl rfl)
  · intro a b ha' hb'
    simp only [List.getLast?_singleton,Option.some.injEq] at ha'
    rw [List.head?_append,Seg.head?_mk _ _ (by omega)] at hb'
    simp only [Option.some_or,Option.some.injEq] at hb'
    subst ha'; subst hb'
    exact p.adjH q (by omega) (by omega) (by omega) (Or.inl (by omega))

omit [NeZero n] in
theorem out_chain (j : Fin p.J) : Chained (p.x q j :: (p.exportLane q j++[p.z q j])) := by
  have hb := p.bounds j.isLt
  have ha := hb.a_eq; have hm := hb.M0_le; have hy := hb.y_ge; have yb := hb.y_band
  have hf := hb.f_ge; have hfl := hb.f_le; have hR := hb.R_le
  have hW : p.W<p.T' := by unfold W; have := p.band_fit; omega
  unfold x exportLane z
  change Chained ([q.loc (p.W+2) (p.a j)]++((_++_)++[_]))
  apply Seg.chained_append (chained_single _)
  · apply Seg.chained_append
    · apply Seg.chained_append (Seg.chained_down q (by omega) (by omega))
        (Seg.chained_right q (by omega) (by omega))
      intro a b ha' hb'
      rw [Seg.getLast?_mk _ _ (by omega)] at ha'
      rw [Seg.head?_mk _ _ (by omega)] at hb'
      cases ha'; cases hb'
      have e1 : p.W+3+(p.y j-p.W-1-1)=p.y j+1 := by omega
      rw [e1,Nat.add_zero]
      exact p.adjH q (by omega) (by omega) (by omega) (Or.inl rfl)
    · exact chained_single _
    · intro a b ha' hb'
      rw [List.getLast?_append,Seg.getLast?_mk _ _ (by omega)] at ha'
      simp only [Option.some_or,Option.some.injEq,List.head?_cons] at ha' hb'
      cases ha'; cases hb'
      have e1 : p.a j+1+(p.f j-p.a j-1-1)=p.f j-1 := by omega
      rw [e1]
      exact p.adjH q (by omega) (by omega) (by omega) (Or.inl (by omega))
  · intro a b ha' hb'
    simp only [List.getLast?_singleton,Option.some.injEq] at ha'
    rw [List.head?_append,List.head?_append,Seg.head?_mk _ _ (by omega)] at hb'
    simp only [Option.some_or,Option.some.injEq] at hb'
    subst ha'; subst hb'
    rw [Nat.add_zero]
    exact p.adjV q (by omega) (by omega) (by omega) (Or.inl rfl)

omit [NeZero n] in
theorem back_chain (j : Fin p.J) :
    Chained (p.z q j :: (p.e q j :: p.deliveryLane q j++[p.hub q (p.H j),p.x q j])) := by
  have hb := p.bounds j.isLt
  have ha := hb.a_eq; have hm := hb.M0_le; have hy := hb.y_ge; have yb := hb.y_band
  have hf := hb.f_ge; have hfl := hb.f_le; have hR := hb.R_le
  have hW : p.W<p.T' := by unfold W; have := p.band_fit; omega
  rw [hubH]
  unfold x deliveryLane z e
  change Chained ([q.loc (p.y j+1) (p.f j)]++([q.loc (p.y j) (p.f j)]++((_++_)++
    [q.loc (p.W+2) (p.a j+1),q.loc (p.W+2) (p.a j)])))
  have tailC : Chained [q.loc (p.W+2) (p.a j+1),q.loc (p.W+2) (p.a j)] := by
    apply List.isChain_cons_cons.mpr
    exact ⟨p.adjH q (by omega) (by omega) (by omega) (Or.inr rfl),List.isChain_singleton _⟩
  apply Seg.chained_append (chained_single _)
  · apply Seg.chained_append (chained_single _)
    · apply Seg.chained_append
      · apply Seg.chained_append (Seg.chained_left q (by omega) (by omega) (by omega))
          (Seg.chained_up q (by omega) (by omega) (by omega))
        intro a b ha' hb'
        rw [Seg.getLast?_mk _ _ (by omega)] at ha'
        rw [Seg.head?_mk _ _ (by omega)] at hb'
        cases ha'; cases hb'
        have e1 : p.f j-1-(p.f j-p.a j-1-1)=p.a j+1 := by omega
        rw [e1,Nat.sub_zero]
        exact p.adjV q (by omega) (by omega) (by omega) (Or.inr (by omega))
      · exact tailC
      · intro a b ha' hb'
        rw [List.getLast?_append,Seg.getLast?_mk _ _ (by omega)] at ha'
        simp only [Option.some_or,Option.some.injEq,List.head?_cons] at ha' hb'
        cases ha'; cases hb'
        have e1 : p.y j-1-(p.y j-p.W-3-1)=p.W+3 := by omega
        rw [e1]
        exact p.adjV q (by omega) (by omega) (by omega) (Or.inr rfl)
    · intro a b ha' hb'
      simp only [List.getLast?_singleton,Option.some.injEq] at ha'
      rw [List.head?_append,List.head?_append,Seg.head?_mk _ _ (by omega)] at hb'
      simp only [Option.some_or,Option.some.injEq] at hb'
      subst ha'; subst hb'
      rw [Nat.sub_zero]
      exact p.adjH q (by omega) (by omega) (by omega) (Or.inr (by omega))
  · intro a b ha' hb'
    simp only [List.getLast?_singleton,Option.some.injEq,List.head?_cons,List.head?_append,
      Option.some_or] at ha' hb'
    subst ha'; subst hb'
    exact p.adjV q (by omega) (by omega) (by omega) (Or.inr rfl)

omit [NeZero n] in
theorem nodup_down {r0 c len : Nat} (hr : r0+len≤p.T) (hc : c<p.T) :
    (Seg.mk (fun i => q.loc (r0+i) c) len).Nodup :=
  Seg.nodup_mk (fun i hi j hj e => by have := (p.coords q (by omega) hc (by omega) hc e).1; omega)

omit [NeZero n] in
theorem nodup_right {r c0 len : Nat} (hr : r<p.T) (hc : c0+len≤p.T) :
    (Seg.mk (fun i => q.loc r (c0+i)) len).Nodup :=
  Seg.nodup_mk (fun i hi j hj e => by have := (p.coords q hr (by omega) hr (by omega) e).2; omega)

omit [NeZero n] in
theorem nodup_left {r c0 len : Nat} (hr : r<p.T) (hc : c0<p.T) (hl : len≤c0+1) :
    (Seg.mk (fun i => q.loc r (c0-i)) len).Nodup :=
  Seg.nodup_mk (fun i hi j hj e => by have := (p.coords q hr (by omega) hr (by omega) e).2; omega)

omit [NeZero n] in
theorem nodup_up {r0 c len : Nat} (hr : r0<p.T) (hc : c<p.T) (hl : len≤r0+1) :
    (Seg.mk (fun i => q.loc (r0-i) c) len).Nodup :=
  Seg.nodup_mk (fun i hi j hj e => by have := (p.coords q (by omega) hc (by omega) hc e).1; omega)

omit [NeZero n] in
theorem access_nodup (j : Fin p.J) : (p.hub q p.w :: p.accessTail q j).Nodup := by
  have hb := p.bounds j.isLt
  have ha := hb.a_eq; have hm := hb.M0_le; have ha4 := hb.a_ge
  rw [hubW]
  unfold accessTail
  rw [List.nodup_cons,List.nodup_append]
  refine ⟨?_,p.nodup_right q (by omega) (by omega),p.nodup_down q (by omega) (by omega),?_⟩
  · rw [List.mem_append,Seg.mem_right,Seg.mem_down]
    rintro (⟨c,h1,h2,e⟩ | ⟨r,h1,h2,e⟩)
    · have := (p.coords q (by omega) (by omega) (by omega) (by omega) e).2; omega
    · have := (p.coords q (by omega) (by omega) (by omega) (by omega) e).1; omega
  · intro a ha' b hb' e
    rw [Seg.mem_right] at ha'
    rw [Seg.mem_down] at hb'
    obtain ⟨c,_,_,rfl⟩ := ha'
    obtain ⟨r,h1,_,rfl⟩ := hb'
    have := (p.coords q (by omega) (by omega) (by omega) (by omega) e).1; omega

omit [NeZero n] in
theorem exportQ_nodup (j : Fin p.J) : (p.exportLane q j++[p.z q j]).Nodup := by
  have hb := p.bounds j.isLt
  have ha := hb.a_eq; have hy := hb.y_ge; have yb := hb.y_band
  have hf := hb.f_ge; have hfl := hb.f_le; have hR := hb.R_le
  have hW : p.W<p.T' := by unfold W; have := p.band_fit; omega
  unfold exportLane z
  rw [List.nodup_append,List.nodup_append]
  refine ⟨⟨p.nodup_down q (by omega) (by omega),p.nodup_right q (by omega) (by omega),?_⟩,
    List.nodup_singleton _,?_⟩
  · intro a ha' b hb' e
    rw [Seg.mem_down] at ha'; rw [Seg.mem_right] at hb'
    obtain ⟨r,_,_,rfl⟩ := ha'; obtain ⟨c,_,_,rfl⟩ := hb'
    have := (p.coords q (by omega) (by omega) (by omega) (by omega) e).2; omega
  · intro a ha' b hb' e
    rw [List.mem_singleton] at hb'; subst hb'
    rw [List.mem_append,Seg.mem_down,Seg.mem_right] at ha'
    rcases ha' with ⟨r,_,_,rfl⟩ | ⟨c,_,_,rfl⟩
    · have := (p.coords q (by omega) (by omega) (by omega) (by omega) e).2; omega
    · have := (p.coords q (by omega) (by omega) (by omega) (by omega) e).2; omega

omit [NeZero n] in
theorem deliveryQ_nodup (j : Fin p.J) : (p.e q j :: p.deliveryLane q j).Nodup := by
  have hb := p.bounds j.isLt
  have ha := hb.a_eq; have hy := hb.y_ge; have yb := hb.y_band
  have hf := hb.f_ge; have hfl := hb.f_le; have hR := hb.R_le
  have hW : p.W<p.T' := by unfold W; have := p.band_fit; omega
  unfold deliveryLane e
  rw [List.nodup_cons,List.nodup_append]
  refine ⟨?_,p.nodup_left q (by omega) (by omega) (by omega),p.nodup_up q (by omega) (by omega) (by omega),?_⟩
  · rw [List.mem_append,Seg.mem_left q (by omega),Seg.mem_up q (by omega)]
    rintro (⟨c,h1,h2,e⟩ | ⟨r,h1,h2,e⟩)
    · have := (p.coords q (by omega) (by omega) (by omega) (by omega) e).2; omega
    · have := (p.coords q (by omega) (by omega) (by omega) (by omega) e).1; omega
  · intro a ha' b hb' e
    rw [Seg.mem_left q (by omega)] at ha'; rw [Seg.mem_up q (by omega)] at hb'
    obtain ⟨c,_,_,rfl⟩ := ha'; obtain ⟨r,_,_,rfl⟩ := hb'
    have := (p.coords q (by omega) (by omega) (by omega) (by omega) e).1; omega

omit [NeZero n] in
theorem loop_nodup (j : Fin p.J) :
    (loopOf (p.x q j) (p.exportLane q j) (p.z q j) (p.e q j) (p.deliveryLane q j) (p.hub q (p.H j))).Nodup := by
  have hb := p.bounds j.isLt
  have ha := hb.a_eq; have hy := hb.y_ge; have yb := hb.y_band
  have hf := hb.f_ge; have hfl := hb.f_le; have hR := hb.R_le
  have hW : p.W<p.T' := by unfold W; have := p.band_fit; omega
  have split : loopOf (p.x q j) (p.exportLane q j) (p.z q j) (p.e q j) (p.deliveryLane q j)
      (p.hub q (p.H j))=[p.x q j]++(p.exportLane q j++[p.z q j])++(p.e q j :: p.deliveryLane q j)++
        [p.hub q (p.H j)] := by simp [loopOf]
  have expLt {r c : Nat} (h : p.expP j r c) : r<p.T ∧ c<p.T := p.loopP_lt j.isLt (Or.inr (Or.inl h))
  have delLt {r c : Nat} (h : p.delP j r c) : r<p.T ∧ c<p.T := p.loopP_lt j.isLt (Or.inr (Or.inr h))
  rw [split,hubH]
  unfold x
  rw [List.nodup_append,List.nodup_append,List.nodup_append]
  refine ⟨⟨⟨List.nodup_singleton _,p.exportQ_nodup q j,?_⟩,p.deliveryQ_nodup q j,?_⟩,List.nodup_singleton _,?_⟩
  · intro a ha' b hb' e
    rw [List.mem_singleton] at ha'; subst ha'
    obtain ⟨r,c,hp,rfl⟩ := (p.mem_exportQ q j).mp hb'
    have := expLt hp
    have := p.coords q (by omega) (by omega) this.1 this.2 e
    unfold expP at hp; omega
  · intro a ha' b hb' e
    obtain ⟨r',c',hp',rfl⟩ := (p.mem_deliveryQ q j).mp hb'
    have l' := delLt hp'
    rw [List.mem_append,List.mem_singleton] at ha'
    rcases ha' with rfl | ha'
    · have := p.coords q (by omega) (by omega) l'.1 l'.2 e
      unfold delP at hp'; omega
    · obtain ⟨r,c,hp,rfl⟩ := (p.mem_exportQ q j).mp ha'
      have l := expLt hp
      have := p.coords q l.1 l.2 l'.1 l'.2 e
      unfold expP at hp; unfold delP at hp'; omega
  · intro a ha' b hb' e
    rw [List.mem_singleton] at hb'; subst hb'
    rw [List.mem_append,List.mem_append,List.mem_singleton] at ha'
    rcases ha' with (rfl | ha') | ha'
    · have := p.coords q (by omega) (by omega) (by omega) (by omega) e; omega
    · obtain ⟨r,c,hp,rfl⟩ := (p.mem_exportQ q j).mp ha'
      have l := expLt hp
      have := p.coords q l.1 l.2 (by omega) (by omega) e
      unfold expP at hp; omega
    · obtain ⟨r,c,hp,rfl⟩ := (p.mem_deliveryQ q j).mp ha'
      have l := delLt hp
      have := p.coords q l.1 l.2 (by omega) (by omega) e
      unfold delP at hp; omega

variable (Q : Fin p.J → Region n)
  (hcells : ∀ j x, x∈(Q j).cells → ∃ r c, p.bodyP j r c ∧ q.loc r c=x)
  (hentry : ∀ j, (Q j).Entry (p.e q j) (p.z q j))

/-- The corner geometry over children sitting in their slot bodies. -/
def geom : StarGeom n p.J Q where
  h := p.hubSide
  hub := p.hub q
  hub_adj := p.hub_adj q
  hub_side := by unfold hubSide M0; omega
  K := p.K
  u := p.u
  v := p.v
  w := p.w
  K_u := by intro h; simp only [K,u,hcell,Prod.mk.injEq,Fin.mk.injEq] at h; omega
  K_v := by intro h; simp only [K,v,hcell,Prod.mk.injEq,Fin.mk.injEq] at h; omega
  u_v := by intro h; simp only [u,v,hcell,Prod.mk.injEq,Fin.mk.injEq] at h; omega
  w_K := by intro h; simp only [w,K,hcell,Prod.mk.injEq,Fin.mk.injEq] at h; omega
  w_u := by intro h; simp only [w,u,hcell,Prod.mk.injEq,Fin.mk.injEq] at h; omega
  w_v := by intro h; simp only [w,v,hcell,Prod.mk.injEq,Fin.mk.injEq] at h; omega
  H := p.H
  H_K := fun j h => by simp only [H,K,hcell,Prod.mk.injEq,Fin.mk.injEq] at h; omega
  H_u := fun j h => by simp only [H,u,hcell,Prod.mk.injEq,Fin.mk.injEq] at h; omega
  H_v := fun j h => by simp only [H,v,hcell,Prod.mk.injEq,Fin.mk.injEq] at h; omega
  H_w := fun j h => by simp only [H,w,hcell,Prod.mk.injEq,Fin.mk.injEq] at h; omega
  H_inj := by
    intro j j' h
    simp only [H,hcell,Prod.mk.injEq,Fin.mk.injEq] at h
    have := p.a_lt j.isLt; have := p.a_lt j'.isLt
    exact Fin.ext (by omega)
  accessTail := p.accessTail q
  x := p.x q
  exportLane := p.exportLane q
  z := p.z q
  e := p.e q
  deliveryLane := p.deliveryLane q
  access_last := by
    intro j
    rw [hubW]
    simp [accessTail,Seg.mk,List.range_succ,x]
  access_chain := p.access_chain q
  out_chain := p.out_chain q
  back_chain := p.back_chain q
  access_nodup := p.access_nodup q
  loop_nodup := p.loop_nodup q
  access_loop := by
    intro j c h1 h2
    obtain ⟨r,c',hp,rfl⟩ := (p.mem_access q j).mp h1
    obtain ⟨r',c'',hp',e⟩ := (p.mem_loop q j).mp h2
    have l := p.accP_lt j.isLt hp
    have l' := p.loopP_lt j.isLt hp'
    have := p.coords q l'.1 l'.2 l.1 l.2 e
    have hb := p.bounds j.isLt
    have := hb.a_eq; have := hb.y_ge; have := hb.f_ge
    unfold x
    unfold accP at hp; unfold loopP expP delP at hp'
    congr 1 <;> omega
  hub_access := by
    intro j
    have hub := p.hub_bound
    refine ⟨?_,?_,?_⟩ <;> intro h <;> obtain ⟨r,c,hp,e⟩ := (p.mem_access q j).mp h <;>
      have l := p.accP_lt j.isLt hp <;>
      have hb := p.bounds j.isLt <;> have := hb.a_eq <;> have := hb.a_ge
    · rw [hubK] at e; have := p.coords q l.1 l.2 (by omega) (by omega) e; unfold accP at hp; omega
    · rw [hubU] at e; have := p.coords q l.1 l.2 (by omega) (by omega) e; unfold accP at hp; omega
    · rw [hubV] at e; have := p.coords q l.1 l.2 (by omega) (by omega) e; unfold accP at hp; omega
  hub_loop := by
    intro j
    have hub := p.hub_bound
    refine ⟨?_,?_,?_⟩ <;> intro h <;> obtain ⟨r,c,hp,e⟩ := (p.mem_loop q j).mp h <;>
      have l := p.loopP_lt j.isLt hp <;>
      have hb := p.bounds j.isLt <;> have := hb.a_eq <;> have := hb.y_ge <;> have := hb.f_ge
    · rw [hubK] at e; have := p.coords q l.1 l.2 (by omega) (by omega) e
      unfold loopP expP delP at hp; omega
    · rw [hubU] at e; have := p.coords q l.1 l.2 (by omega) (by omega) e
      unfold loopP expP delP at hp; omega
    · rw [hubV] at e; have := p.coords q l.1 l.2 (by omega) (by omega) e
      unfold loopP expP delP at hp; omega
  entry := hentry
  loop_child := by
    intro j j' c h1 h2
    obtain ⟨r,c',hp,rfl⟩ := (p.mem_loop q j).mp h1
    obtain ⟨r',c'',hp',e⟩ := hcells j' _ h2
    have l := p.loopP_lt j.isLt hp
    have l' := p.bodyP_lt j'.isLt hp'
    have := p.coords q l'.1 l'.2 l.1 l.2 e
    obtain ⟨rfl,rfl⟩ := this
    exact p.loopP_body j.isLt j'.isLt hp hp'
  access_child := by
    intro j c h1 h2
    obtain ⟨r,c',hp,rfl⟩ := (p.mem_access q j).mp h1
    obtain ⟨r',c'',hp',e⟩ := hcells j _ h2
    have l := p.accP_lt j.isLt hp
    have l' := p.bodyP_lt j.isLt hp'
    have := p.coords q l'.1 l'.2 l.1 l.2 e
    have hR : p.W+4≤p.R (p.rowOf j) := by unfold R; omega
    unfold accP at hp; unfold bodyP at hp'; omega
  hub_child := by
    intro j
    have hub := p.hub_bound
    have hR : p.W+4≤p.R (p.rowOf j) := by unfold R; omega
    refine ⟨?_,?_,?_⟩ <;> intro h <;> obtain ⟨r,c,hp,e⟩ := hcells j _ h <;>
      have l := p.bodyP_lt j.isLt hp
    · rw [hubK] at e; have := p.coords q l.1 l.2 (by omega) (by omega) e; unfold bodyP at hp; omega
    · rw [hubU] at e; have := p.coords q l.1 l.2 (by omega) (by omega) e; unfold bodyP at hp; omega
    · rw [hubV] at e; have := p.coords q l.1 l.2 (by omega) (by omega) e; unfold bodyP at hp; omega
  children_disjoint := by
    intro j j' hjj
    rw [Finset.disjoint_left]
    intro x h1 h2
    obtain ⟨r,c,hp,rfl⟩ := hcells j _ h1
    obtain ⟨r',c',hp',e⟩ := hcells j' _ h2
    have l := p.bodyP_lt j.isLt hp
    have l' := p.bodyP_lt j'.isLt hp'
    obtain ⟨rfl,rfl⟩ := p.coords q l'.1 l'.2 l.1 l.2 e
    have hW : p.W<p.T' := by unfold W; have := p.band_fit; omega
    unfold bodyP at hp hp'
    exact p.slot_disjoint j.isLt j'.isLt (fun h => hjj (Fin.ext h)) ⟨by omega,hp.2.1,hp.2.2⟩ ⟨by omega,hp'.2.1,hp'.2.2⟩
  loops_disjoint := by
    intro j j' hjj c h1 h2
    obtain ⟨r,c',hp,rfl⟩ := (p.mem_loop q j).mp h1
    obtain ⟨r',c'',hp',e⟩ := (p.mem_loop q j').mp h2
    have l := p.loopP_lt j.isLt hp
    have l' := p.loopP_lt j'.isLt hp'
    obtain ⟨rfl,rfl⟩ := p.coords q l'.1 l'.2 l.1 l.2 e
    rcases Nat.lt_or_gt_of_ne (fun h => hjj (Fin.ext h)) with hl | hl
    · exact p.loopP_disjoint j.isLt j'.isLt hl hp hp'
    · exact p.loopP_disjoint j'.isLt j.isLt hl hp' hp


omit [NeZero p.T] in
theorem hubFrame_fit : p.W+1+3≤p.T := by have := p.hub_fit; unfold W at *; omega

/-- The hub exchange frame: rows down from `W+1`, columns right from `1`;
its block is `p = K`, `q = (W+1,2)`, `s = (W+2,1)`, `z = (W+2,2)`. -/
def hubFrame : Routes.Frame n :=
  q.rect (p.W+1) 1 3 p.M0 false false (by have := p.hubFrame_fit; omega)
    (by have := p.hub_bound; omega) (by simp) (fun _ => p.hubFrame_fit) (by simp)
    (fun _ => by have := p.hub_bound; omega)

omit [NeZero n] in
theorem hubFrame_loc (r c : Nat) : (p.hubFrame q).loc r c=q.loc (p.W+1+r) (1+c) := by
  simp [hubFrame,Placement.rect_loc,Routes.ax]

/-- The third cell of the hub exchange. -/
def hubZ : Cell n := q.loc (p.W+2) 2

/-- The hub exchange of spoke `j` by one `t`-cycle: `t_{H j}` in the hub frame. -/
theorem hub_exchange (j : Fin p.J) (plus : Bool) (B : Board n) (hB : blank B=p.hub q p.w) :
    ∃ C : Board n, ∃ path : Path B C, path.length≤Cycle3.tw 1 (p.a j)+4 ∧
      blank C=p.hub q p.w ∧
      Cycle3.IsCycle B C (p.hub q (p.H j)) (if plus then p.hub q p.K else p.hubZ q)
        (if plus then p.hubZ q else p.hub q p.K) := by
  have hb := p.hub_bound
  have ha := p.a_lt j.isLt
  have hW := p.hubFrame_fit
  have hR : 3≤(p.hubFrame q).R := le_refl _
  have hC : 6≤(p.hubFrame q).C := by change 6≤p.M0; unfold M0; omega
  have ha4 := (p.bounds j.isLt).a_ge
  have e00 : (p.hubFrame q).loc 0 0=p.hub q p.K := by rw [hubFrame_loc,hubK]
  have e11 : (p.hubFrame q).loc 1 1=p.hubZ q := by rw [hubFrame_loc]; unfold hubZ; congr 1
  have eH : (p.hubFrame q).loc 1 (p.a j)=p.hub q (p.H j) := by
    rw [hubFrame_loc,hubH]; congr 1; omega
  have ew : p.hub q p.w=q.loc p.W 2 := p.hubW q
  have ne {r c r' c' : Nat} (h1 : r<p.T) (h2 : c<p.T) (h3 : r'<p.T) (h4 : c'<p.T) (h : r≠r' ∨ c≠c') :
      q.loc r c≠q.loc r' c' := fun e => by have := p.coords q h1 h2 h3 h4 e; omega
  obtain ⟨C,path,len,bC,cyc⟩ := Cycle3.tcycle_w_at (p.hubFrame q) hR hC (p.hub q p.w)
    (by rw [ew,hubFrame_loc]; exact p.adjV q (by omega) (by omega) (by omega) (by omega))
    (by rw [ew,hubFrame_loc]; exact ne (by omega) (by omega) (by omega) (by omega) (by omega))
    (by rw [ew,hubFrame_loc]; exact ne (by omega) (by omega) (by omega) (by omega) (by omega))
    B hB 1 (p.a j) (by omega) (by change _<p.M0; omega) (by omega)
    (by rw [ew,hubFrame_loc]; exact ne (by omega) (by omega) (by omega) (by omega) (by omega)) plus
  rw [e00,e11,eH] at cyc
  exact ⟨C,path,len,bC,cyc⟩

/-- The corner layout over children sitting in their slot bodies: the hub
exchange is one `t`-cycle. -/
def layout : StarLayout n p.J Q :=
  { p.geom q Q hcells hentry with
    hc := fun _ => p.hubZ q
    hcost := fun j => Cycle3.tw 1 (p.a j)+4
    hX := fun j B hB => by
      have := p.hub_exchange q j true B hB
      simp only [if_true] at this
      exact this
    hX' := fun j B hB => by
      obtain ⟨C,path,len,bC,cyc⟩ := p.hub_exchange q j false B hB
      simp only [Bool.false_eq_true,if_false] at cyc
      exact ⟨C,path,len,bC,cyc.rotate.rotate⟩
    hc_access := by
      intro j h
      obtain ⟨r,c,hp,e⟩ := (p.mem_access q j).mp h
      have l := p.accP_lt j.isLt hp
      have hb := p.bounds j.isLt; have := hb.a_eq; have := hb.a_ge; have := p.hubFrame_fit; have := p.hub_bound
      unfold hubZ at e
      have := p.coords q l.1 l.2 (by omega) (by omega) e; unfold accP at hp; omega
    hc_loop := by
      intro j h
      obtain ⟨r,c,hp,e⟩ := (p.mem_loop q j).mp h
      have l := p.loopP_lt j.isLt hp
      have hb := p.bounds j.isLt; have := hb.a_eq; have := hb.y_ge; have := hb.f_ge; have := hb.a_ge
      have := p.hubFrame_fit; have := p.hub_bound
      unfold hubZ at e
      have := p.coords q l.1 l.2 (by omega) (by omega) e
      unfold loopP expP delP at hp; omega
    hc_child := by
      intro j h
      obtain ⟨r,c,hp,e⟩ := hcells j _ h
      have l := p.bodyP_lt j.isLt hp
      have hR : p.W+4≤p.R (p.rowOf j) := by unfold R; omega
      have := p.hubFrame_fit; have := p.hub_bound
      unfold hubZ at e
      have := p.coords q l.1 l.2 (by omega) (by omega) e; unfold bodyP at hp; omega
    hc_K := fun _ => by
      have := p.hub_bound; have := p.hubFrame_fit
      change p.hubZ q≠p.hub q p.K
      rw [hubK]; unfold hubZ
      intro e; have := p.coords q (by omega) (by omega) (by omega) (by omega) e; omega }

end Params
end SlidingPuzzle.NestedRouting.Corner
