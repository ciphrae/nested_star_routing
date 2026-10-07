import NestedRouting.Star.Laws
import NestedRouting.Moves.GoalCompletion

/-! Finishing a star node: drain the delivery lanes, finish every child,
sort P's own homes. -/
namespace SlidingPuzzle.NestedRouting.Interface
open Finset TileRoles
open SlidingPuzzle.NestedRouting.ReservePolicy

variable {n : Nat} [NeZero n] {J : Nat}

namespace StarSpec
variable (P : StarSpec n J)

/-- Walk to the hub, run an operation that keeps the connector, walk back. -/
theorem exists_hubbed {B : Board n} (atZ : blank B=P.zP) (Φ : Board n → Nat → Prop)
    (inner : ∀ B2 : Board n, Path B B2 → blank B2=P.L.hub P.L.w →
      (∀ y, y∉P.conn → B2 y=B y) →
      ∃ D : Board n, ∃ q : Path B2 D, blank D=P.L.hub P.L.w ∧ (∀ y∈P.conn, D y=B2 y) ∧
        Φ D q.length) :
    ∃ C : Board n, ∃ path : Path B C, ∃ D : Board n, ∃ len : Nat, ∃ _ : Path D C,
      Φ D len ∧ blank C=P.zP ∧ (∀ y, y∉P.conn → C y=D y) ∧ (∀ y∈P.conn, C y=B y) ∧
      path.length=2*P.connTail.length+len := by
  classical
  obtain ⟨B2,p2,len2,eff2⟩ := exists_walk P.zP P.connTail P.conn_chain B atZ
  have blank2 : blank B2=P.L.hub P.L.w := (walk_blank _ _ eff2 atZ).trans P.conn_last
  obtain ⟨D,q,blankD,fixD,phi⟩ := inner B2 p2 blank2 (fun y hy => walk_fixed _ eff2 hy)
  obtain ⟨E,r,lenr,blankE,effE⟩ := Path.exists_unstaged p2 q (blankD.trans blank2.symm)
  set σ := P.conn.formPerm with hσ
  have preimage (y : Cell n) : B2.symm (B y)=σ⁻¹ y := by
    apply B2.symm_apply_eq.mpr
    rw [eff2]
    change B y=B (σ (σ⁻¹ y))
    simp
  refine ⟨E,r,D,q.length,((p2.append q).reverse).append r,phi,blankE.trans atZ,?_,?_,?_⟩
  · intro y hy
    rw [effE,preimage]
    congr 1
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact (List.formPerm_apply_of_notMem hy).symm
  · intro y hy
    rw [effE,preimage]
    have hm : σ⁻¹ y∈P.conn := by
      rw [←List.formPerm_mem_iff_mem (l:=P.conn)]
      change σ (σ⁻¹ y)∈P.conn
      simpa using hy
    rw [fixD _ hm,eff2]
    change B (σ (σ⁻¹ y))=B y
    simp
  · rw [lenr,len2]

namespace Inner
variable {P} {r : Roles n} {cap ec ac : Nat}

/-- A retired spoke has no core source left in its export lane. -/
theorem retired_head {B : Board n} {led : Fin J → Ledger.Counter} {ch : (j : Fin J) → (P.Q j).Rec}
    {cs cr : Bool} (h : P.Inner B r led ch cap ec ac cs cr) (j : Fin J) (hS : (led j).S=P.pop j) :
    B (P.ehead j)∉r .coreSource := by
  intro hm
  have bS := h.bridgeS j
  rw [P.ce_cons,countP_cons,if_pos hm] at bS
  have hv := ((P.Q j).sound (h.child j)).valid
  simp only [Counts.Valid] at hv
  unfold pop at hS
  omega

theorem drainSpoke (j : Fin J) (k : Nat) : ∀ {B : Board n} {led : Fin J → Ledger.Counter}
    {ch : (j : Fin J) → (P.Q j).Rec}, k≤(P.L.deliveryQ j).length →
    P.Inner B r led ch cap ec ac false false → blank B=P.L.hub P.L.w →
    (∀ i, (led i).S=P.pop i) → Ledger.totalCredit led≤cap →
    B (P.L.hub P.L.K)∉r .coreSource → B (P.L.hub P.L.K)∉r .coreFinal →
    ∃ C : Board n, ∃ path : Path B C, ∃ led' : Fin J → Ledger.Counter,
      ∃ ch' : (j : Fin J) → (P.Q j).Rec,
      blank C=P.L.hub P.L.w ∧ P.Inner C r led' ch' cap ec ac false false ∧
      C (P.L.hub P.L.K)∉r .coreSource ∧ C (P.L.hub P.L.K)∉r .coreFinal ∧
      (∀ i (hi : i<(P.cd C j).length), (P.cd C j).length ≤ i+k → (P.cd C j)[i]∉r .coreFinal) ∧
      (∀ i, (led' i).S=(led i).S) ∧ (∀ i, (led' i).idle=(led i).idle+(if i=j then k else 0)) ∧
      Ledger.totalCredit led'=Ledger.totalCredit led ∧
      (∀ i, i≠j → P.cd C i=P.cd B i) ∧
      (∀ y, y∉P.L.exportQ j → y∉P.L.deliveryQ j → y∉(P.Q j).cells → y≠P.L.hub P.L.K → C y=B y) ∧
      path.length+P.totalWork ch+P.ledCost led≤P.totalWork ch'+P.ledCost led' := by
  induction k with
  | zero =>
    intro B led ch _ h atW _ capOk hKs hKf
    refine ⟨B,.nil B,led,ch,atW,h,hKs,hKf,?_,fun _ => rfl,fun _ => by simp,rfl,fun _ _ => rfl,
      fun _ _ _ _ _ => rfl,by simp⟩
    intro i hi hlen; omega
  | succ k ih =>
    intro B led ch hk h atW allS capOk hKs hKf
    obtain ⟨C1,p1,led1,ch1,b1,h1,s1,f1,last1,S1,idle1,tc1,oth1,fix1,cost1⟩ :=
      ih (by omega) h atW allS capOk hKs hKf
    have allS1 : ∀ i, (led1 i).S=P.pop i := fun i => (S1 i).trans (allS i)
    have capOk1 : Ledger.totalCredit led1≤cap := by rw [tc1]; exact capOk
    have hd := h1.retired_head j (allS1 j)
    obtain ⟨C,p2,ch2,b2,h2,K2,cd2,fix2,cost2⟩ :=
      h1.service b1 j false rfl (by simp) (fun _ => ⟨s1,f1⟩)
        (fun _ hact => absurd hact (by rw [allS1 j]; omega)) capOk1
    rw [if_neg hd,decide_eq_false hd] at h2
    simp only [Nat.add_zero,Bool.false_eq_true,if_false] at h2
    set c' := Ledger.serve (led1 j) (P.pop j) false false with hc'
    have retired1 : ¬(led1 j).S<P.pop j := by rw [allS1 j]; omega
    have others := fun {i : Fin J} (hij : i≠j) => other_fixed (P:=P) (B:=C1) j fix2 hij
    refine ⟨C,p1.append p2,Function.update led1 j c',ch2,b2,h2,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [K2]; exact hd
    · rw [K2]; exact h1.exp_fin j _ (by rw [P.ce_cons]; exact List.mem_cons_self)
    · intro i hi hlen
      have lenEq : (P.cd C j).length=(P.cd C1 j).length := by
        rw [cd2]
        have : (P.cd C1 j)≠[] := by rw [P.cd_cons]; simp
        simp only [List.length_append,List.length_tail,List.length_singleton]
        have := List.length_pos_of_ne_nil this
        omega
      have get : (P.cd C j)[i]=((P.cd C1 j).tail++[C1 (P.L.hub P.L.K)])[i]'(by rw [←cd2]; exact hi) :=
        List.getElem_of_eq cd2 hi
      rw [get]
      by_cases hl : i<(P.cd C1 j).tail.length
      · rw [List.getElem_append_left hl,List.getElem_tail]
        exact last1 (i+1) (by rw [List.length_tail] at hl; omega) (by rw [List.length_tail] at hl; omega)
      · have : i=(P.cd C1 j).tail.length := by
          have hi' : i<(P.cd C1 j).length := lenEq ▸ hi
          have := List.length_tail (l:=P.cd C1 j)
          omega
        simp only [this,List.getElem_concat_length]
        exact f1
    · intro i
      by_cases hij : i=j
      · subst hij; simp [hc',Ledger.serve_S,S1]
      · simp [Function.update_of_ne hij,S1]
    · intro i
      by_cases hij : i=j
      · subst hij; simp [hc',Ledger.serve_idle,retired1,idle1]; omega
      · simp [idle1,hij]
    · rw [totalCredit_update]
      · exact tc1
      · rw [Ledger.serve_credit]; simp
    · intro i hij
      rw [(others hij).2.1,oth1 i hij]
    · intro y h1' h2' h3' h4'
      rw [fix2 y h1' h2' h3' h4',fix1 y h1' h2' h3' h4']
    · rw [Path.length_append,P.ledCost_update led1 j c' (Ledger.serve_k _ _ _ _)]
      omega

end Inner

namespace Inner
variable {P} {r : Roles n} {cap ec ac : Nat}

/-- Drain the spokes with index below `m`. -/
theorem drainAll (m : Nat) : ∀ {B : Board n} {led : Fin J → Ledger.Counter}
    {ch : (j : Fin J) → (P.Q j).Rec}, m≤J →
    P.Inner B r led ch cap ec ac false false → blank B=P.L.hub P.L.w →
    (∀ i, (led i).S=P.pop i) → Ledger.totalCredit led≤cap →
    B (P.L.hub P.L.K)∉r .coreSource → B (P.L.hub P.L.K)∉r .coreFinal →
    ∃ C : Board n, ∃ path : Path B C, ∃ led' : Fin J → Ledger.Counter,
      ∃ ch' : (j : Fin J) → (P.Q j).Rec,
      blank C=P.L.hub P.L.w ∧ P.Inner C r led' ch' cap ec ac false false ∧
      C (P.L.hub P.L.K)∉r .coreSource ∧ C (P.L.hub P.L.K)∉r .coreFinal ∧
      (∀ j : Fin J, j.val<m → ∀ t∈P.cd C j, t∉r .coreFinal) ∧
      (∀ i, (led' i).S=(led i).S) ∧
      (∀ i, (led' i).idle=(led i).idle+(if i.val<m then (P.L.deliveryQ i).length else 0)) ∧
      Ledger.totalCredit led'=Ledger.totalCredit led ∧
      (∀ y, ¬P.foot y → C y=B y) ∧
      path.length+P.totalWork ch+P.ledCost led≤P.totalWork ch'+P.ledCost led' := by
  induction m with
  | zero =>
    intro B led ch _ h atW _ _ hKs hKf
    exact ⟨B,.nil B,led,ch,atW,h,hKs,hKf,fun j hj => absurd hj (by omega),fun _ => rfl,
      fun _ => by simp,rfl,fun _ _ => rfl,by simp⟩
  | succ m ih =>
    intro B led ch hm h atW allS capOk hKs hKf
    obtain ⟨C1,p1,led1,ch1,b1,h1,s1,f1,free1,S1,idle1,tc1,fix1,cost1⟩ :=
      ih (by omega) h atW allS capOk hKs hKf
    set j : Fin J := ⟨m,by omega⟩ with hj
    obtain ⟨C,p2,led2,ch2,b2,h2,s2,f2,last2,S2,idle2,tc2,oth2,fix2,cost2⟩ :=
      h1.drainSpoke j (P.L.deliveryQ j).length le_rfl b1 (fun i => (S1 i).trans (allS i))
        (by rw [tc1]; exact capOk) s1 f1
    refine ⟨C,p1.append p2,led2,ch2,b2,h2,s2,f2,?_,fun i => (S2 i).trans (S1 i),?_,tc2.trans tc1,?_,?_⟩
    · intro i hi t ht
      by_cases hij : i=j
      · subst hij
        obtain ⟨k,hk,rfl⟩ := List.mem_iff_getElem.mp ht
        apply last2 k hk
        simp [cd]
      · have hi' : i.val<m := by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | h'
          · exact h'
          · exact absurd (Fin.ext h') hij
        rw [oth2 i hij] at ht
        exact free1 i hi' t ht
    · intro i
      rw [idle2,idle1]
      by_cases hij : i=j
      · subst hij; simp [hj]
      · have : i.val≠m := fun e => hij (Fin.ext e)
        simp only [hij,if_false]
        by_cases hlt : i.val<m
        · simp [hlt,show i.val<m+1 by omega]
        · simp [hlt,show ¬i.val<m+1 by omega]
    · intro y hy
      have hy' : y∉P.L.exportQ j ∧ y∉P.L.deliveryQ j ∧ y∉(P.Q j).cells ∧ y≠P.L.hub P.L.K :=
        ⟨fun e => hy (Or.inl ⟨j,Or.inl e⟩),fun e => hy (Or.inl ⟨j,Or.inr (Or.inl e)⟩),
          fun e => hy (Or.inl ⟨j,Or.inr (Or.inr e)⟩),fun e => hy (Or.inr e)⟩
      rw [fix2 y hy'.1 hy'.2.1 hy'.2.2.1 hy'.2.2.2,fix1 y hy]
    · rw [Path.length_append]; omega

end Inner

/-- Access, an operation keeping the accessed set, and reversed access. -/
theorem exists_conj {B C2 D : Board n} (p : Path B C2) (q : Path C2 D) (hblank : blank D=blank C2)
    (W : Set (Cell n)) (fixP : ∀ y, y∉W → C2 y=B y) (fixQ : ∀ y∈W, D y=C2 y) :
    ∃ E : Board n, ∃ r : Path B E, r.length=2*p.length+q.length ∧ blank E=blank B ∧
      (∀ y∈W, E y=B y) ∧ (∀ y, y∉W → E y=D y) := by
  obtain ⟨E,r,len,blankE,effE⟩ := Path.exists_unstaged p q hblank
  refine ⟨E,r,len,blankE,?_,?_⟩
  · intro y hy
    rw [effE]
    by_cases hw : C2.symm (B y)∈W
    · rw [fixQ _ hw]; simp
    · have h1 := fixP _ hw
      rw [C2.apply_symm_apply] at h1
      have : C2.symm (B y)=y := B.injective h1.symm
      exact absurd (this ▸ hw) (fun h => h hy)
  · intro y hy
    rw [effE]
    have : C2.symm (B y)=y := by
      apply C2.symm_apply_eq.mpr
      exact (fixP y hy).symm
    rw [this]

namespace Inner
variable {P} {r : Roles n} {cap ec ac : Nat}

/-- After draining, every child has received all its goals. -/
theorem child_complete {B : Board n} {led : Fin J → Ledger.Counter} {ch : (j : Fin J) → (P.Q j).Rec}
    (h : P.Inner B r led ch cap ec P.frame.M false false)
    (free : ∀ j : Fin J, ∀ t∈P.cd B j, t∉r .coreFinal) (j : Fin J) :
    ((P.Q j).counts (ch j)).ac=(P.Q j).M ∧ ((P.Q j).counts (ch j)).ar=(P.Q j).r := by
  have allG : ∀ i, (led i).G=P.pop i := by
    have hsum : ∑ i, (led i).G=∑ i, P.pop i := by rw [h.sumG,P.M_eq]
    have hle : ∀ i∈univ, (led i).G≤P.pop i := fun i _ => h.ledger.G_le i
    exact fun i => (sum_eq_sum_iff_of_le hle).mp hsum i (mem_univ i)
  have bG := h.bridgeG j
  have zero : (P.cd B j).countP (fun t => t∈r .coreFinal)=0 := by
    rw [List.countP_eq_zero]; intro t ht; simpa using free j t ht
  rw [zero,allG j] at bG
  have hv := ((P.Q j).sound (h.child j)).valid
  simp only [Counts.Valid] at hv
  unfold pop at bG
  omega

end Inner

/-- Finish child `j` from the hub. -/
theorem finishChild (j : Fin J) {β : Nat} {s : (P.Q j).Rec} {B : Board n} (atW : blank B=P.L.hub P.L.w)
    (hs : (P.Q j).Holds β s B) (core : ((P.Q j).counts s).ac=(P.Q j).M)
    (res : ((P.Q j).counts s).ar=(P.Q j).r) :
    ∃ E : Board n, ∃ path : Path B E, blank E=P.L.hub P.L.w ∧
      (∀ x∈(P.Q j).coreCells∪(P.Q j).reserveCells, E x=P.goal x) ∧
      (∀ y, y∉(P.Q j).cells → y∉(P.Q j).strip → E y=B y) ∧
      path.length+(P.Q j).work s≤2*((P.L.accessTail j).length+(P.L.exportQ j).length)+
        (P.Q j).toCore.budget β := by
  classical
  obtain ⟨C1,p1,len1,eff1⟩ := exists_walk (P.L.hub P.L.w) (P.L.accessTail j) (P.L.access_chain j) B atW
  have blank1 : blank C1=P.L.x j := (walk_blank _ _ eff1 atW).trans (P.L.access_last j)
  obtain ⟨C2,p2,len2,eff2⟩ := exists_walk (P.L.x j) (P.L.exportQ j) (P.L.out_chain j) C1 blank1
  have blank2 : blank C2=P.L.z j := (walk_blank _ _ eff2 blank1).trans (P.L.getLast_out j)
  let W : Set (Cell n) := {y | y∈P.L.hub P.L.w :: P.L.accessTail j ∨ y∈P.L.x j :: P.L.exportQ j}
  have fixP : ∀ y, y∉W → C2 y=B y := by
    intro y hy
    simp only [W,Set.mem_ofPred_eq,not_or] at hy
    rw [walk_fixed _ eff2 hy.2,walk_fixed _ eff1 hy.1]
  have Wnot : ∀ y∈W, y∉(P.Q j).cells := by
    rintro y (hy | hy)
    · exact P.L.access_child j y hy
    · exact P.L.loop_child j j y (P.L.out_sub_loop j hy)
  have hs2 : (P.Q j).Holds β s C2 :=
    (P.Q j).transport hs (p1.append p2) (fun x hx => fixP x (fun hw => Wnot x hw hx))
  obtain ⟨F⟩ := (P.Q j).finish hs2 (P.L.entry j) blank2 core res
  have fixQ : ∀ y∈W, F.board y=C2 y := by
    intro y hy
    by_cases hz : y=P.L.z j
    · have h1 : F.board y=0 := by rw [hz,←blank2,←F.blank]; simp [blank,position]
      have h2 : C2 y=0 := by rw [hz,←blank2]; simp [blank,position]
      rw [h1,h2]
    · apply F.fixed y (Wnot y hy)
      intro hst
      exact hz (P.strip_walk j y hy hst)
  obtain ⟨E,r,lenr,blankE,onW,offW⟩ := exists_conj (p1.append p2) F.path F.blank W fixP fixQ
  refine ⟨E,r,blankE.trans atW,?_,?_,?_⟩
  · intro x hx
    rw [offW x (fun hw => Wnot x hw (P.home_sub j hx)),F.placed x hx,P.goal_child j]
  · intro y hq hst
    by_cases hw : y∈W
    · exact onW y hw
    · rw [offW y hw,F.fixed y hq hst,fixP y hw]
  · have := F.cost
    rw [lenr,Path.length_append,len1,len2]
    simp only [Core.budget] at this ⊢
    omega

/-- Finish the children with index below `m`, one after another. -/
theorem finishChildren (β : Fin J → Nat) (ch : (j : Fin J) → (P.Q j).Rec) (m : Nat) :
    ∀ {B : Board n}, m≤J → blank B=P.L.hub P.L.w →
    (∀ j, (P.Q j).Holds (β j) (ch j) B) →
    (∀ j, ((P.Q j).counts (ch j)).ac=(P.Q j).M ∧ ((P.Q j).counts (ch j)).ar=(P.Q j).r) →
    ∃ E : Board n, ∃ path : Path B E, blank E=P.L.hub P.L.w ∧
      (∀ j : Fin J, j.val<m → ∀ x∈(P.Q j).coreCells∪(P.Q j).reserveCells, E x=P.goal x) ∧
      (∀ j : Fin J, m≤j.val → (P.Q j).Holds (β j) (ch j) E) ∧
      (∀ y, (∀ j : Fin J, j.val<m → y∉(P.Q j).cells ∧ y∉(P.Q j).strip) → E y=B y) ∧
      path.length+∑ j, (if j.val<m then (P.Q j).work (ch j) else 0)≤
        ∑ j, (if j.val<m then 2*((P.L.accessTail j).length+(P.L.exportQ j).length)+
          (P.Q j).toCore.budget (β j) else 0) := by
  induction m with
  | zero =>
    intro B _ atW hold _
    exact ⟨B,.nil B,atW,fun j hj => absurd hj (by omega),fun j _ => hold j,fun _ _ => rfl,by simp⟩
  | succ m ih =>
    intro B hm atW hold comp
    obtain ⟨E1,p1,b1,placed1,hold1,fix1,cost1⟩ := ih (by omega) atW hold comp
    set j : Fin J := ⟨m,by omega⟩ with hj
    obtain ⟨E,p2,b2,placed2,fix2,cost2⟩ :=
      P.finishChild j b1 (hold1 j (by simp [hj])) (comp j).1 (comp j).2
    -- cells of child `j` and its strip are disjoint from other children
    have away {i : Fin J} (hij : i≠j) {x : Cell n} (hx : x∈(P.Q i).cells) :
        x∉(P.Q j).cells ∧ x∉(P.Q j).strip :=
      ⟨fun h => disjoint_left.mp (P.L.children_disjoint i j hij) hx h,
        fun h => disjoint_left.mp (P.own_child i) (P.strip_own j h) hx⟩
    refine ⟨E,p1.append p2,b2,?_,?_,?_,?_⟩
    · intro i hi x hx
      by_cases hij : i=j
      · subst hij; exact placed2 x hx
      · have hi' : i.val<m := by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | h'
          · exact h'
          · exact absurd (Fin.ext h') hij
        have hxQ := P.home_sub i hx
        rw [fix2 x (away hij hxQ).1 (away hij hxQ).2]
        exact placed1 i hi' x hx
    · intro i hi
      have hij : i≠j := fun e => by rw [e] at hi; simp [hj] at hi
      exact (P.Q i).transport (hold1 i (by omega)) p2
        (fun x hx => fix2 x (away hij hx).1 (away hij hx).2)
    · intro y hy
      rw [fix2 y (hy j (by simp [hj])).1 (hy j (by simp [hj])).2]
      exact fix1 y (fun i hi => hy i (by omega))
    · rw [Path.length_append]
      have split (f : Fin J → Nat) : ∑ i, (if i.val<m+1 then f i else 0)=
          ∑ i, (if i.val<m then f i else 0)+f j := by
        rw [←sum_erase_add _ _ (mem_univ j),←sum_erase_add _ _ (mem_univ j)]
        have : ∑ x ∈ univ.erase j, (if x.val<m+1 then f x else 0)=
            ∑ x ∈ univ.erase j, (if x.val<m then f x else 0) := by
          apply sum_congr rfl
          intro x hx
          have : x.val≠m := fun e => ne_of_mem_erase hx (Fin.ext e)
          by_cases hlt : x.val<m
          · simp [hlt,show x.val<m+1 by omega]
          · simp [hlt,show ¬x.val<m+1 by omega]
        rw [this]
        have hjm : j.val=m := rfl
        simp [hjm]
      rw [split (fun i => (P.Q i).work (ch i)),
        split (fun i => 2*((P.L.accessTail i).length+(P.L.exportQ i).length)+(P.Q i).toCore.budget (β i))]
      omega

open Classical in
/-- The cells the final sort works on: P's cells off the children's homes. -/
noncomputable def resid : Finset (Cell n) := P.frame.cells.filter (fun a => a∉P.homeCells)

theorem mem_resid {x : Cell n} : x∈P.resid ↔ x∈P.frame.cells ∧ x∉P.homeCells := by
  classical
  unfold resid; rw [mem_filter]

theorem resid_card : P.resid.card≤P.own.card+P.childSpare.card+P.markers.card := by
  classical
  have sub : P.resid⊆P.own∪P.childSpare∪P.markers := by
    intro x hx
    obtain ⟨hc,hh⟩ := P.mem_resid.mp hx
    rw [frame_cells] at hc
    simp only [mem_union] at hc ⊢
    rcases hc with (hc | hc) | hc
    · simp only [childCells,mem_biUnion,mem_univ,true_and] at hc
      obtain ⟨j,hj⟩ := hc
      simp only [Frame.cells,mem_union] at hj
      rcases hj with (hj | hj) | hj
      · exact absurd (by simp only [homeCells,mem_biUnion,mem_univ,true_and,mem_union]; exact ⟨j,Or.inl hj⟩) hh
      · exact absurd (by simp only [homeCells,mem_biUnion,mem_univ,true_and,mem_union]; exact ⟨j,Or.inr hj⟩) hh
      · exact Or.inl (Or.inr (by simp only [childSpare,mem_biUnion,mem_univ,true_and]; exact ⟨j,hj⟩))
    · exact Or.inl (Or.inl hc)
    · exact Or.inr hc
  have h1 := card_le_card sub
  have h2 := card_union_le (P.own∪P.childSpare) P.markers
  have h3 := card_union_le P.own P.childSpare
  omega

/-- Sort P's own homes, leaving the children's homes alone. -/
theorem finalSort {B : Board n} (atZ : blank B=P.zP)
    (present : ∀ x∈P.frame.reserveCells, ∃ y∈P.frame.cells, y∉P.homeCells ∧ B y=P.goal x) :
    ∃ C : Board n, ∃ path : Path B C, blank C=P.zP ∧
      (∀ x∈P.frame.reserveCells, C x=P.goal x) ∧ (∀ y, y∉P.frame.cells → C y=B y) ∧
      (∀ y∈P.homeCells, C y=B y) ∧
      path.length≤2*∑ x∈P.resid, P.fw x := by
  classical
  set R : Finset (Cell n) := P.resid with hRdef
  have resCells (x : Cell n) (hx : x∈P.frame.reserveCells) : x∈P.frame.cells ∧ x∉P.homeCells := by
    refine ⟨by simp [Frame.cells,hx],fun hh => disjoint_left.mp P.frame.core_reserve hh hx⟩
  have inside : P.frame.reserveCells⊆R := by
    intro a ha
    exact P.mem_resid.mpr (resCells _ ha)
  have hR : ∀ x∈R, (∃ j, x∈(P.Q j).cells) ∨ x∈P.own ∨ x∈P.markers := by
    intro x hx
    have hc := (P.mem_resid.mp hx).1
    rw [frame_cells] at hc
    simp only [childCells,mem_union,mem_biUnion,mem_univ,true_and] at hc
    tauto
  have room : P.frame.reserveCells.card+3≤R.card := by
    have disj : Disjoint P.frame.reserveCells P.markers := P.frame.reserve_spare
    have sub : P.frame.reserveCells∪P.markers⊆R := by
      intro a ha
      apply P.mem_resid.mpr
      rcases mem_union.mp ha with ha | ha
      · exact resCells _ ha
      · refine ⟨by simp [Frame.cells,frame,ha],fun hh => ?_⟩
        exact disjoint_left.mp P.frame.core_spare hh ha
    have := card_le_card sub
    rw [card_union_of_disjoint disj] at this
    have := P.six
    omega
  have noHome : ∀ x∈R, ∀ j, x∉(P.Q j).coreCells ∧ x∉(P.Q j).reserveCells := by
    intro x hx j
    have hh := (P.mem_resid.mp hx).2
    constructor <;> intro hm <;> apply hh <;>
      simp only [homeCells,mem_biUnion,mem_univ,true_and,mem_union] <;> exact ⟨j,by tauto⟩
  obtain ⟨C,path,len,blankC,outside,placed⟩ := P.fsort B P.goal R P.frame.reserveCells atZ hR noHome inside
    (fun x hx => P.frame.goal_nonzero _ (mem_union_right _ hx))
    (fun x hx => by
      obtain ⟨y,hy,hyh,eq⟩ := present _ hx
      exact ⟨y,P.mem_resid.mpr ⟨hy,hyh⟩,eq⟩) room
  refine ⟨C,path,blankC.trans atZ,placed,?_,?_,?_⟩
  · intro y hy
    exact outside y (fun hm => hy (P.mem_resid.mp hm).1)
  · intro y hy
    exact outside y (fun hm => (P.mem_resid.mp hm).2 hy)
  · exact len

def cmax : Nat := univ.sup P.serviceCost
/-- The part of a service cost not carried by the weights. -/
def cb : Nat := univ.sup (fun j => P.serviceCost j-P.lw1*P.ρ1 j-P.lw2*P.ρ2 j)

theorem cb_le_cmax : P.cb≤P.cmax := by
  unfold cb cmax
  apply Finset.sup_le
  intro j _
  exact (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans (le_sup (f:=P.serviceCost) (mem_univ j)))

theorem cost_le_cb (j : Fin J) : P.serviceCost j≤P.cb+P.lw1*P.ρ1 j+P.lw2*P.ρ2 j := by
  have := le_sup (f:=fun j => P.serviceCost j-P.lw1*P.ρ1 j-P.lw2*P.ρ2 j) (mem_univ j)
  unfold cb; omega
def rmax : Nat := univ.sup (fun j => (P.Q j).rate)

def dlen (j : Fin J) : Nat := (P.L.deliveryQ j).length

/-- The node's base budget. -/
noncomputable def baseP : Nat :=
  ∑ j, P.serviceCost j*(P.pop j+P.elen j+P.dlen j)+(P.cb*J+P.lw1*∑ j, P.ρ1 j+P.lw2*∑ j, P.ρ2 j)+
  ∑ j, ((P.Q j).base+2*((P.L.accessTail j).length+(P.L.exportQ j).length))+
  P.rmax*(J+∑ j, (P.elen j+P.dlen j+2))+P.wrapCost*(P.frame.M+P.frame.r)+
  (P.dxCost*(P.frame.r-P.stat.card)+∑ x∈P.stat, P.dw x)+2*P.connTail.length+2*∑ x∈P.resid, P.fw x

/-- The node's budget rate per unit of lead allowance. -/
def rateP : Nat := (Ledger.cdiv (P.cb*P.hp) P.hq+Ledger.cdiv (P.lw1*P.wp1) P.hq+Ledger.cdiv (P.lw2*P.wp2) P.hq)+
  Ledger.cdiv (P.rmax*P.hp) P.hq+(P.dxCost+P.wrapCost)

theorem peak_toNat_sum {led : Fin J → Ledger.Counter} {β : Nat} (h : Ledger.Good P.pop P.elen β led) :
    P.hq*∑ j, (led j).peak.toNat≤P.hq*J+P.hp*β := by
  have hs := h.peak_sum
  have hb := Ledger.tailCharge_zero_le β J P.hp P.hq (P.harm β)
  have cast : ((∑ j, (led j).peak.toNat : Nat) : Int)=∑ j, (led j).peak := by
    push_cast
    exact sum_congr rfl (fun j _ => Int.toNat_of_nonneg (h.peak_nonneg j))
  have hle : ∑ j, (led j).peak.toNat≤Ledger.tailCharge β J 0 := by
    have : ((∑ j, (led j).peak.toNat : Nat) : Int)≤(Ledger.tailCharge β J 0 : Int) := by
      rw [cast]; exact hs
    exact_mod_cast this
  exact (Nat.mul_le_mul_left _ hle).trans hb

theorem ledCost_bound {led : Fin J → Ledger.Counter} {β : Nat} (h : Ledger.Good P.pop P.elen β led)
    (idle : ∀ j, (led j).idle=P.dlen j) :
    P.ledCost led≤∑ j, P.serviceCost j*(P.pop j+P.elen j+P.dlen j)+
      ((P.cb*J+P.lw1*∑ j, P.ρ1 j+P.lw2*∑ j, P.ρ2 j)+
      (Ledger.cdiv (P.cb*P.hp) P.hq+Ledger.cdiv (P.lw1*P.wp1) P.hq+Ledger.cdiv (P.lw2*P.wp2) P.hq)*β) := by
  have per : ∀ j, (led j).k≤P.pop j+P.elen j+P.dlen j+(led j).peak.toNat := by
    intro j
    have := h.services_le j
    rw [idle j] at this
    have e := Int.toNat_of_nonneg (h.peak_nonneg j)
    omega
  have step1 : P.ledCost led≤∑ j, (P.serviceCost j*(P.pop j+P.elen j+P.dlen j)+
      P.serviceCost j*(led j).peak.toNat) := by
    unfold ledCost
    apply sum_le_sum
    intro j _
    rw [←Nat.mul_add]
    exact Nat.mul_le_mul_left _ (per j)
  have step2 : ∑ j, P.serviceCost j*(led j).peak.toNat≤P.cb*∑ j, (led j).peak.toNat+
      (P.lw1*∑ j, P.ρ1 j*(led j).peak.toNat+P.lw2*∑ j, P.ρ2 j*(led j).peak.toNat) := by
    rw [mul_sum,mul_sum,mul_sum,←sum_add_distrib,←sum_add_distrib]
    apply sum_le_sum
    intro j _
    have := Nat.mul_le_mul_right (led j).peak.toNat (P.cost_le_cb j)
    have e : (P.cb+P.lw1*P.ρ1 j+P.lw2*P.ρ2 j)*(led j).peak.toNat=
        P.cb*(led j).peak.toNat+(P.lw1*(P.ρ1 j*(led j).peak.toNat)+P.lw2*(P.ρ2 j*(led j).peak.toNat)) := by ring
    omega
  rw [sum_add_distrib] at step1
  have c0 := Ledger.scale_frac P.hq_pos (P.peak_toNat_sum h) P.cb
  have w1 := h.weighted_peak P.ρ1
  have w2 := h.weighted_peak P.ρ2
  have l1 := Ledger.scale_frac (J:=0) P.hq_pos (by simpa using P.wharm1 β) P.lw1
  have l2 := Ledger.scale_frac (J:=0) P.hq_pos (by simpa using P.wharm2 β) P.lw2
  have m1 := Nat.mul_le_mul_left P.lw1 w1
  have m2 := Nat.mul_le_mul_left P.lw2 w2
  simp only [Nat.mul_zero,Nat.zero_add] at l1 l2
  have e1 : P.lw1*(∑ j, P.ρ1 j+Ledger.layered P.ρ1 β)=P.lw1*∑ j, P.ρ1 j+P.lw1*Ledger.layered P.ρ1 β := by ring
  have e2 : P.lw2*(∑ j, P.ρ2 j+Ledger.layered P.ρ2 β)=P.lw2*∑ j, P.ρ2 j+P.lw2*Ledger.layered P.ρ2 β := by ring
  have e3 : (Ledger.cdiv (P.cb*P.hp) P.hq+Ledger.cdiv (P.lw1*P.wp1) P.hq+Ledger.cdiv (P.lw2*P.wp2) P.hq)*β=
      Ledger.cdiv (P.cb*P.hp) P.hq*β+Ledger.cdiv (P.lw1*P.wp1) P.hq*β+Ledger.cdiv (P.lw2*P.wp2) P.hq*β := by ring
  omega

theorem childBudget_bound {led : Fin J → Ledger.Counter} {β : Nat} (h : Ledger.Good P.pop P.elen β led) :
    ∑ j, (P.Q j).toCore.budget (P.childBeta led j)≤
      ∑ j, (P.Q j).base+P.rmax*(J+∑ j, (P.elen j+P.dlen j+2))+Ledger.cdiv (P.rmax*P.hp) P.hq*β := by
  have per : ∀ j, (P.Q j).toCore.budget (P.childBeta led j)≤(P.Q j).base+P.rmax*P.childBeta led j := by
    intro j
    unfold Core.budget
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (le_sup (f:=fun j => (P.Q j).rate) (mem_univ j))) _
  have hsum := sum_le_sum (fun j (_ : j∈univ) => per j)
  rw [sum_add_distrib,←mul_sum] at hsum
  have hb : ∑ j, P.childBeta led j=∑ j, (led j).peak.toNat+∑ j, (P.elen j+P.dlen j+2) := by
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro j _
    simp only [childBeta,elen,dlen]
    ring
  have := Ledger.scale_frac P.hq_pos (P.peak_toNat_sum h) P.rmax
  rw [hb] at hsum
  nlinarith

/-- The finishing law of a star node. -/
theorem finish {β : Nat} {s : P.StarRec} {B : Board n} (hs : P.Holds β s B) (atZ : blank B=P.zP)
    (core : s.counts.ac=P.frame.M) (res : s.counts.ar=P.frame.r) (Prep : Board n → Prop) :
    Nonempty (Finish (P.core P.baseP P.rateP Prep) β s B) := by
  classical
  obtain ⟨hec,her⟩ := hs.sound.sources_done core res
  have hv := hs.sound.valid
  set r := s.roles
  -- facts at the start of draining
  have allS : ∀ i, (s.led i).S=P.pop i := by
    have hsum : ∑ i, (s.led i).S=∑ i, P.pop i := by rw [hs.inner.sumS,hec,P.M_eq]
    exact fun i => (sum_eq_sum_iff_of_le (fun i _ => hs.inner.ledger.S_le i)).mp hsum i (mem_univ i)
  have capOk : Ledger.totalCredit s.led≤β := P.cap_ok hs
  -- the operation at the hub
  let Φ : Board n → Nat → Prop := fun D len =>
    (∀ j : Fin J, ∀ x∈(P.Q j).coreCells∪(P.Q j).reserveCells, D x=P.goal x) ∧
    (∀ y, y∉P.frame.cells → y∉P.conn → D y=B y) ∧
    ∃ led1 : Fin J → Ledger.Counter, Ledger.Good P.pop P.elen β led1 ∧ (∀ j, (led1 j).idle=P.dlen j) ∧
      len+P.totalWork s.ch+P.ledCost s.led≤P.ledCost led1+
        ∑ j, (2*((P.L.accessTail j).length+(P.L.exportQ j).length)+(P.Q j).toCore.budget (P.childBeta led1 j))
  have inner : ∀ B2 : Board n, Path B B2 → blank B2=P.L.hub P.L.w → (∀ y, y∉P.conn → B2 y=B y) →
      ∃ D : Board n, ∃ q : Path B2 D, blank D=P.L.hub P.L.w ∧ (∀ y∈P.conn, D y=B2 y) ∧ Φ D q.length := by
    intro B2 pB2 blank2 off2
    have notConn {y : Cell n} (hy : P.foot y) : y∉P.conn := P.foot_not_conn hy
    have h2 : P.Inner B2 r s.led s.ch β s.counts.ec s.counts.ac false false := by
      apply hs.inner.congr (Equiv.refl _) (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl hs.inner.disjoint
      · intro j; simp only [ce,Equiv.coe_refl,List.map_id]
        exact List.map_congr_left (fun c hc => off2 c (notConn (Or.inl ⟨j,Or.inl hc⟩)))
      · intro j; simp only [cd,Equiv.coe_refl,List.map_id]
        exact List.map_congr_left (fun c hc => off2 c (notConn (Or.inl ⟨j,Or.inr (Or.inl hc)⟩)))
      · simpa using off2 _ (notConn (Or.inr rfl))
      · intro j
        exact (P.Q j).transport (hs.inner.child j) pB2
          (fun x hx => off2 x (notConn (Or.inl ⟨j,Or.inr (Or.inr hx)⟩)))
      · exact fun _ => rfl
      · exact fun _ => rfl
      · exact fun _ => rfl
    obtain ⟨C1,p1,led1,ch1,b1,h1,_,_,free,S1,idle1,_,fix1,cost1⟩ :=
      Inner.drainAll J le_rfl h2 blank2 allS capOk h2.carrier_token h2.carrier_token_fin
    rw [core] at h1
    have comp := fun j => Inner.child_complete h1 (fun j t ht => free j j.isLt t ht) j
    obtain ⟨E,p2,b2,placed2,_,fix2,cost2⟩ :=
      P.finishChildren (P.childBeta led1) ch1 J le_rfl b1 (fun j => h1.child j) comp
    have offAll {y : Cell n} (hy : y∉P.frame.cells) : ∀ j : Fin J, j.val<J → y∉(P.Q j).cells ∧ y∉(P.Q j).strip :=
      fun j _ => ⟨fun h => hy (P.child_sub_cells j h),fun h => hy (P.own_sub_cells (P.strip_own j h))⟩
    refine ⟨E,p1.append p2,b2,?_,⟨fun j x hx => placed2 j j.isLt x hx,?_,led1,h1.ledger,?_,?_⟩⟩
    · intro y hy
      rw [fix2 y (fun j _ => ⟨fun h => (P.conn_free y hy).1 j |>.2.2 h,P.conn_strip y hy j⟩),
        fix1 y (P.conn_not_foot hy)]
    · intro y hy hc
      rw [fix2 y (offAll hy),fix1 y (fun hf => hy (P.foot_cells hf)),off2 y hc]
    · intro j
      rw [idle1,hs.idle0 j]; simp [dlen]
    · have tw : P.totalWork ch1=∑ j, (P.Q j).work (ch1 j) := rfl
      simp only [Fin.is_lt,if_true] at cost2
      rw [Path.length_append]
      omega
  obtain ⟨C3,path3,D,len,_,⟨placedD,fixD,led1,good1,idleL,costD⟩,blank3,offC3,onC3,len3⟩ :=
    P.exists_hubbed atZ Φ inner
  -- `C3` agrees with `B` outside P
  have outC3 (y : Cell n) (hy : y∉P.frame.cells) : C3 y=B y := by
    by_cases hc : y∈P.conn
    · exact onC3 y hc
    · rw [offC3 y hc,fixD y hy hc]
  have homesC3 (j : Fin J) (x : Cell n) (hx : x∈(P.Q j).coreCells∪(P.Q j).reserveCells) : C3 x=P.goal x := by
    have hxc : x∉P.conn := fun hc => ((P.conn_free x hc).1 j).2.2 (P.home_sub j hx)
    rw [offC3 x hxc,placedD j x hx]
  -- reserve goals sit in P outside the children's homes
  have present : ∀ x∈P.frame.reserveCells, ∃ y∈P.frame.cells, y∉P.homeCells ∧ C3 y=P.goal x := by
    intro x hx
    have hres : P.goal x∈s.roles .reserveFinal := by
      rw [hs.sound.reserveFinal_complete res]; exact mem_image_of_mem _ hx
    have inB : P.goal x∈P.frame.cells.image B := role_present hs.sound.inventory _ hres
    have same : P.frame.cells.image C3=P.frame.cells.image B :=
      TileRoles.contents_eq_of_exterior_fixed _ _ _ outC3
    rw [←same] at inB
    obtain ⟨y,hy,eq⟩ := mem_image.mp inB
    refine ⟨y,hy,?_,eq⟩
    intro hyh
    simp only [homeCells,mem_biUnion,mem_univ,true_and] at hyh
    obtain ⟨j,hj⟩ := hyh
    rw [homesC3 j y hj] at eq
    have := P.goal.injective eq
    subst this
    exact disjoint_left.mp P.frame.core_reserve
      (by simp only [frame,homeCells,mem_biUnion,mem_univ,true_and]; exact ⟨j,hj⟩) hx
  obtain ⟨C,path4,blankC,resC,outC,homeC,len4⟩ := P.finalSort blank3 present
  refine ⟨⟨C,path3.append path4,blankC.trans atZ.symm,?_,?_,?_⟩⟩
  · intro x hx _
    rw [outC x hx,outC3 x hx]
  · intro x hx
    rcases mem_union.mp hx with hx | hx
    · have hx' := hx
      change x∈P.homeCells at hx'
      simp only [homeCells,mem_biUnion,mem_univ,true_and] at hx'
      obtain ⟨j,hj⟩ := hx'
      rw [homeC x hx,homesC3 j x hj]; rfl
    · exact resC x hx
  · -- the budget
    have hw := hs.work_le
    have hl := P.ledCost_bound good1 idleL
    have hcb := P.childBudget_bound good1
    have hexc := exception_bound hs.sound.valid hs.lateInv
    have hreq : s.nreq≤(P.frame.M+P.frame.r)+β := by
      have := hs.nreq_le; have := hs.sound.valid.1; omega
    -- direct exchanges: by position from fresh static cells, then at most `r - |stat| + β` more
    have hdx : P.dxCost*s.ndx+∑ x∈P.stat \ s.fresh, P.dw x≤
        P.dxCost*(P.frame.r-P.stat.card)+∑ x∈P.stat, P.dw x+P.dxCost*β := by
      obtain ⟨st1,st2,st3,st4⟩ := hs.statInv
      have hsub : ∑ x∈P.stat \ s.fresh, P.dw x≤∑ x∈P.stat, P.dw x :=
        sum_le_sum_of_subset (sdiff_subset)
      have hnd := hs.ndx_le
      by_cases hne : s.fresh.Nonempty
      · have nf0 := st4 hne
        obtain ⟨x,hx⟩ := hne
        have her : s.counts.er<P.frame.r :=
          hs.sound.toState.source_reserve.mp ⟨_,st2 x hx⟩
        have l0 : s.late=0 := hs.lateInv.2.1 (Or.inr her)
        have : s.ndx=0 := by omega
        rw [this,Nat.mul_zero,Nat.zero_add]
        omega
      · have hf : s.fresh=∅ := not_nonempty_iff_eq_empty.mp hne
        rw [hf,sdiff_empty]
        rw [hf,card_empty,Nat.sub_zero] at st3
        have hcs : s.ndx≤(P.frame.r-P.stat.card)+β := by
          have := hs.sound.valid.2.1; omega
        have := Nat.mul_le_mul_left P.dxCost hcs
        rw [Nat.mul_add] at this
        omega
    have split : ∑ j, (2*((P.L.accessTail j).length+(P.L.exportQ j).length)+
        (P.Q j).toCore.budget (P.childBeta led1 j))=
        ∑ j, 2*((P.L.accessTail j).length+(P.L.exportQ j).length)+
        ∑ j, (P.Q j).toCore.budget (P.childBeta led1 j) := sum_add_distrib
    have bsplit : ∑ j, ((P.Q j).base+2*((P.L.accessTail j).length+(P.L.exportQ j).length))=
        ∑ j, (P.Q j).base+∑ j, 2*((P.L.accessTail j).length+(P.L.exportQ j).length) := sum_add_distrib
    show s.work+(path3.append path4).length≤P.baseP+P.rateP*β
    rw [Path.length_append,len3]
    unfold baseP rateP
    rw [bsplit]
    have m1 := Nat.mul_le_mul_left P.wrapCost hreq
    rw [split] at costD
    nlinarith

end StarSpec
end SlidingPuzzle.NestedRouting.Interface
