import NestedRouting.Star.Rounds

/-! The inner invariant is stable under relabelling the lanes, carrier and
children by a tile permutation fixing P's core sources and core finals.
This covers paused transport, ancestor substitution and direct exchanges. -/
namespace SlidingPuzzle.NestedRouting.Interface
open Finset TileRoles
open SlidingPuzzle.NestedRouting.ReservePolicy

variable {n : Nat} [NeZero n] {J : Nat}

namespace StarSpec
namespace Inner
variable {P : StarSpec n J} {B : Board n} {r : Roles n} {led : Fin J → Ledger.Counter}
  {ch : (j : Fin J) → (P.Q j).Rec} {cap ecNow acNow : Nat} {cs cr : Bool}

omit [NeZero n] in
theorem perm_mem_iff (π : Equiv.Perm (Tile n)) {S : Finset (Tile n)} (fix : ∀ t∈S, π t=t)
    (t : Tile n) : π t∈S ↔ t∈S := by
  constructor
  · intro h
    have := fix _ h
    rw [π.injective this] at h
    exact h
  · intro h; rw [fix t h]; exact h

theorem congr (h : P.Inner B r led ch cap ecNow acNow cs cr) {B' : Board n} {r' : Roles n}
    {ch' : (j : Fin J) → (P.Q j).Rec} (π : Equiv.Perm (Tile n))
    (fixS : ∀ t∈r .coreSource, π t=t) (fixF : ∀ t∈r .coreFinal, π t=t)
    (hS : r' .coreSource=r .coreSource) (hF : r' .coreFinal=r .coreFinal)
    (disj : ∀ i i', i≠i' → Disjoint (r' i) (r' i'))
    (ce' : ∀ j, P.ce B' j=(P.ce B j).map π) (cd' : ∀ j, P.cd B' j=(P.cd B j).map π)
    (K' : B' (P.L.hub P.L.K)=π (B (P.L.hub P.L.K)))
    (child' : ∀ j, (P.Q j).Holds (P.childBeta led j) (ch' j) B')
    (cnt' : ∀ j, (P.Q j).counts (ch' j)=(P.Q j).counts (ch j))
    (src' : ∀ j, P.childSrc j (ch' j)=P.childSrc j (ch j))
    (fin' : ∀ j, P.childFin j (ch' j)=P.childFin j (ch j)) :
    P.Inner B' r' led ch' cap ecNow acNow cs cr := by
  classical
  have iS := perm_mem_iff π fixS
  have iF := perm_mem_iff π fixF
  have cntS (l : List (Tile n)) : (l.map π).countP (fun t => t∈r .coreSource)=l.countP (fun t => t∈r .coreSource) := by
    rw [List.countP_map]; exact List.countP_congr (fun t _ => by simp [iS t])
  have cntF (l : List (Tile n)) : (l.map π).countP (fun t => t∈r .coreFinal)=l.countP (fun t => t∈r .coreFinal) := by
    rw [List.countP_map]; exact List.countP_congr (fun t _ => by simp [iF t])
  refine ⟨disj,child',h.ledger,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,h.sumS,h.sumG⟩
  · intro j; rw [cnt',hS,ce',cntS]; exact h.bridgeS j
  · intro j; rw [cnt',hF,cd',cntF]; exact h.bridgeG j
  · intro j; rw [src',hS]; exact h.src_child j
  · intro j; rw [fin',hF]; exact h.fin_child j
  · intro t ht
    rw [hS] at ht
    rcases h.src_loc t ht with ⟨j,hj⟩ | ⟨j,hj⟩ | ⟨hc,hK⟩
    · exact Or.inl ⟨j,by rw [src']; exact hj⟩
    · exact Or.inr (Or.inl ⟨j,by rw [ce',←fixS t ht]; exact List.mem_map_of_mem hj⟩)
    · exact Or.inr (Or.inr ⟨hc,by rw [K',←hK,fixS t ht]⟩)
  · intro t ht
    rw [hF] at ht
    rcases h.fin_loc t ht with ⟨j,hj⟩ | ⟨j,hj⟩ | ⟨hc,hK⟩
    · exact Or.inl ⟨j,by rw [fin']; exact hj⟩
    · exact Or.inr (Or.inl ⟨j,by rw [cd',←fixF t ht]; exact List.mem_map_of_mem hj⟩)
    · exact Or.inr (Or.inr ⟨hc,by rw [K',←hK,fixF t ht]⟩)
  · intro j t ht htf
    rw [cd'] at ht; rw [hF] at htf
    obtain ⟨t0,h0,rfl⟩ := List.mem_map.mp ht
    have h0f := (iF t0).mp htf
    rw [fixF t0 h0f]
    exact h.del_home j t0 h0 h0f
  · intro j t ht
    rw [cd'] at ht; rw [hS]
    obtain ⟨t0,h0,rfl⟩ := List.mem_map.mp ht
    rw [iS]; exact h.del_src j t0 h0
  · intro j t ht
    rw [ce'] at ht; rw [hF]
    obtain ⟨t0,h0,rfl⟩ := List.mem_map.mp ht
    rw [iF]; exact h.exp_fin j t0 h0
  · intro j i hi hlen hns
    have e := ce' j
    have hiB : i<(P.ce B j).length := by rw [e] at hi; simpa using hi
    have key : ∀ k (hk : k<(P.ce B' j).length), (P.ce B' j)[k]=π ((P.ce B j)[k]'(by rw [e] at hk; simpa using hk)) := by
      intro k hk
      rw [List.getElem_of_eq e]
      simp
    rw [hS,key,iS] at hns
    have hlenB : (P.ce B j).length ≤ i+(led j).k := by rw [e] at hlen; simpa using hlen
    obtain ⟨sl,rest⟩ := h.entered j i hiB hlenB hns
    refine ⟨by unfold sourceless; rw [cnt']; exact sl,?_⟩
    intro i' hi' hlt
    rw [hS,key,iS]
    exact rest i' _ hlt

/-- Only the carrier changes, and the roles change only on the old and new
carrier tiles. -/
theorem recarrier (h : P.Inner B r led ch cap ecNow acNow cs cr) {B' : Board n} {r' : Roles n}
    {cs' cr' : Bool} (disj' : ∀ i i', i≠i' → Disjoint (r' i) (r' i'))
    (ce' : ∀ j, P.ce B' j=P.ce B j) (cd' : ∀ j, P.cd B' j=P.cd B j)
    (cells' : ∀ j, ∀ x∈(P.Q j).cells, B' x=B x)
    (child' : ∀ j, (P.Q j).Holds (P.childBeta led j) (ch j) B')
    (agreeS : ∀ t, t≠B (P.L.hub P.L.K) → t≠B' (P.L.hub P.L.K) → (t∈r' .coreSource ↔ t∈r .coreSource))
    (agreeF : ∀ t, t≠B (P.L.hub P.L.K) → t≠B' (P.L.hub P.L.K) → (t∈r' .coreFinal ↔ t∈r .coreFinal))
    (newS : B' (P.L.hub P.L.K)∈r' .coreSource → cs'=true)
    (newF : B' (P.L.hub P.L.K)∈r' .coreFinal → cr'=true)
    (oldS : B (P.L.hub P.L.K)∈r' .coreSource → B (P.L.hub P.L.K)=B' (P.L.hub P.L.K))
    (oldF : B (P.L.hub P.L.K)∈r' .coreFinal → B (P.L.hub P.L.K)=B' (P.L.hub P.L.K)) :
    P.Inner B' r' led ch cap ecNow acNow cs' cr' := by
  classical
  -- tiles of lanes and children are neither carrier tile
  have laneNe {j : Fin J} {t : Tile n} (ht : t∈P.ce B j ∨ t∈P.cd B j) :
      t≠B (P.L.hub P.L.K) ∧ t≠B' (P.L.hub P.L.K) := by
    rcases ht with ht | ht
    · obtain ⟨c,hc,rfl⟩ := cell_of_ce ht
      have hcK : c≠P.L.hub P.L.K := fun e => (P.L.hub_loop j).1 (e ▸ P.L.mem_loop_of_exportQ hc)
      refine ⟨fun e => hcK (B.injective e),fun e => hcK (B'.injective ?_)⟩
      have : B' c=B c :=
        List.map_eq_map_iff.mp (show (P.L.exportQ j).map B'=(P.L.exportQ j).map B from ce' j) c hc
      rw [this,e]
    · obtain ⟨c,hc,rfl⟩ := cell_of_cd ht
      have hcK : c≠P.L.hub P.L.K := fun e => (P.L.hub_loop j).1 (e ▸ P.L.mem_loop_of_deliveryQ hc)
      refine ⟨fun e => hcK (B.injective e),fun e => hcK (B'.injective ?_)⟩
      have : B' c=B c :=
        List.map_eq_map_iff.mp (show (P.L.deliveryQ j).map B'=(P.L.deliveryQ j).map B from cd' j) c hc
      rw [this,e]
  have childNe {j : Fin J} {x : Cell n} (hx : x∈(P.Q j).cells) :
      B x≠B (P.L.hub P.L.K) ∧ B x≠B' (P.L.hub P.L.K) := by
    have hxK : x≠P.L.hub P.L.K := fun e => (P.L.hub_child j).1 (e ▸ hx)
    refine ⟨fun e => hxK (B.injective e),fun e => hxK (B'.injective ?_)⟩
    rw [cells' j x hx,e]
  have childTile {j : Fin J} {t : Tile n} (ht : t∈P.childSrc j (ch j) ∨ t∈P.childFin j (ch j)) :
      t≠B (P.L.hub P.L.K) ∧ t≠B' (P.L.hub P.L.K) := by
    rcases ht with ht | ht
    · obtain ⟨x,hx,rfl⟩ := h.mem_childSrc_cell ht; exact childNe hx
    · obtain ⟨x,hx,rfl⟩ := h.mem_childFin_cell ht; exact childNe hx
  have cntS (j : Fin J) : (P.ce B j).countP (fun t => t∈r' .coreSource)=(P.ce B j).countP (fun t => t∈r .coreSource) :=
    List.countP_congr (fun t ht => by
      obtain ⟨n1,n2⟩ := laneNe (Or.inl ht); simp [agreeS t n1 n2])
  have cntF (j : Fin J) : (P.cd B j).countP (fun t => t∈r' .coreFinal)=(P.cd B j).countP (fun t => t∈r .coreFinal) :=
    List.countP_congr (fun t ht => by
      obtain ⟨n1,n2⟩ := laneNe (Or.inr ht); simp [agreeF t n1 n2])
  refine ⟨disj',child',h.ledger,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,h.sumS,h.sumG⟩
  · intro j; rw [ce',cntS]; exact h.bridgeS j
  · intro j; rw [cd',cntF]; exact h.bridgeG j
  · intro j t ht
    obtain ⟨n1,n2⟩ := childTile (Or.inl ht)
    exact (agreeS t n1 n2).mpr (h.src_child j ht)
  · intro j t ht
    obtain ⟨n1,n2⟩ := childTile (Or.inr ht)
    exact (agreeF t n1 n2).mpr (h.fin_child j ht)
  · intro t ht
    by_cases hn : t=B' (P.L.hub P.L.K)
    · exact Or.inr (Or.inr ⟨newS (hn ▸ ht),hn⟩)
    by_cases ho : t=B (P.L.hub P.L.K)
    · exact absurd ((oldS (ho ▸ ht)).symm.trans ho.symm).symm hn
    rcases h.src_loc t ((agreeS t ho hn).mp ht) with ⟨j,hj⟩ | ⟨j,hj⟩ | ⟨_,hK⟩
    · exact Or.inl ⟨j,hj⟩
    · exact Or.inr (Or.inl ⟨j,by rw [ce']; exact hj⟩)
    · exact absurd hK ho
  · intro t ht
    by_cases hn : t=B' (P.L.hub P.L.K)
    · exact Or.inr (Or.inr ⟨newF (hn ▸ ht),hn⟩)
    by_cases ho : t=B (P.L.hub P.L.K)
    · exact absurd ((oldF (ho ▸ ht)).symm.trans ho.symm).symm hn
    rcases h.fin_loc t ((agreeF t ho hn).mp ht) with ⟨j,hj⟩ | ⟨j,hj⟩ | ⟨_,hK⟩
    · exact Or.inl ⟨j,hj⟩
    · exact Or.inr (Or.inl ⟨j,by rw [cd']; exact hj⟩)
    · exact absurd hK ho
  · intro j t ht htf
    rw [cd'] at ht
    obtain ⟨n1,n2⟩ := laneNe (Or.inr ht)
    exact h.del_home j t ht ((agreeF t n1 n2).mp htf)
  · intro j t ht
    rw [cd'] at ht
    obtain ⟨n1,n2⟩ := laneNe (Or.inr ht)
    rw [agreeS t n1 n2]; exact h.del_src j t ht
  · intro j t ht
    rw [ce'] at ht
    obtain ⟨n1,n2⟩ := laneNe (Or.inl ht)
    rw [agreeF t n1 n2]; exact h.exp_fin j t ht
  · intro j i hi hlen hns
    have e := ce' j
    have hiB : i<(P.ce B j).length := by rw [e] at hi; exact hi
    have key : ∀ k (hk : k<(P.ce B' j).length), (P.ce B' j)[k]=(P.ce B j)[k]'(by rw [e] at hk; exact hk) :=
      fun k hk => List.getElem_of_eq e hk
    have tileNe (k : Nat) (hk : k<(P.ce B j).length) :=
      laneNe (Or.inl (List.getElem_mem hk))
    rw [key,agreeS _ (tileNe i hiB).1 (tileNe i hiB).2] at hns
    obtain ⟨sl,rest⟩ := h.entered j i hiB (by rw [e] at hlen; exact hlen) hns
    refine ⟨sl,fun i' hi' hlt => ?_⟩
    have hi'B : i'<(P.ce B j).length := by rw [e] at hi'; exact hi'
    rw [key,agreeS _ (tileNe i' hi'B).1 (tileNe i' hi'B).2]
    exact rest i' hi'B hlt

end Inner
end StarSpec
end SlidingPuzzle.NestedRouting.Interface
