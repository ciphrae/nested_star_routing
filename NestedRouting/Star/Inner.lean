import NestedRouting.Star.Spec

/-! The inner invariant of a star node: how P's core sources and core
finals sit in its children and lanes, coupled to the children's counters
and to the scheduling ledger. It holds between services, both at rest and
in the middle of a request, for a fixed role classifier `r` (P's roles,
with the current input already classified). The carrier cell `K` may hold
a counted source (`cs`) or a counted real goal (`cr`). -/
namespace SlidingPuzzle.NestedRouting.Interface
open Finset TileRoles
open SlidingPuzzle.NestedRouting.ReservePolicy

variable {n : Nat} [NeZero n] {J : Nat}

namespace StarSpec
variable (P : StarSpec n J)

/-- Export lane contents, head first. -/
def ce (B : Board n) (j : Fin J) : List (Tile n) := (P.L.exportQ j).map B
/-- Delivery lane contents, head first. -/
def cd (B : Board n) (j : Fin J) : List (Tile n) := (P.L.deliveryQ j).map B

def elen (j : Fin J) : Nat := (P.L.exportQ j).length

def childSrc (j : Fin J) (s : (P.Q j).Rec) : Finset (Tile n) :=
  (P.Q j).roles s .coreSource∪(P.Q j).roles s .reserveSource
def childFin (j : Fin J) (s : (P.Q j).Rec) : Finset (Tile n) :=
  (P.Q j).roles s .coreFinal∪(P.Q j).roles s .reserveFinal
def homeGoals (j : Fin J) : Finset (Tile n) := (P.Q j).coreGoals∪(P.Q j).reserveGoals

def sourceless (j : Fin J) (s : (P.Q j).Rec) : Prop :=
  ((P.Q j).counts s).ec=(P.Q j).M ∧ ((P.Q j).counts s).er=(P.Q j).r

/-- The lead allowance P grants child `j`. -/
def childBeta (led : Fin J → Ledger.Counter) (j : Fin J) : Nat :=
  (led j).peak.toNat+(P.L.exportQ j).length+(P.L.deliveryQ j).length+2

structure Inner (B : Board n) (r : Roles n) (led : Fin J → Ledger.Counter)
    (ch : (j : Fin J) → (P.Q j).Rec) (cap ecNow acNow : Nat) (cs cr : Bool) : Prop where
  disjoint : ∀ i i', i≠i' → Disjoint (r i) (r i')
  child : ∀ j, (P.Q j).Holds (P.childBeta led j) (ch j) B
  ledger : Ledger.Good P.pop P.elen cap led
  bridgeS : ∀ j, ((P.Q j).counts (ch j)).ec+((P.Q j).counts (ch j)).er=
    (led j).S+(P.ce B j).countP (fun t => t∈r .coreSource)
  bridgeG : ∀ j, ((P.Q j).counts (ch j)).ac+((P.Q j).counts (ch j)).ar+
    (P.cd B j).countP (fun t => t∈r .coreFinal)=(led j).G
  src_child : ∀ j, P.childSrc j (ch j)⊆r .coreSource
  fin_child : ∀ j, P.childFin j (ch j)⊆r .coreFinal
  src_loc : ∀ t∈r .coreSource, (∃ j, t∈P.childSrc j (ch j)) ∨ (∃ j, t∈P.ce B j) ∨
    (cs=true ∧ t=B (P.L.hub P.L.K))
  fin_loc : ∀ t∈r .coreFinal, (∃ j, t∈P.childFin j (ch j)) ∨ (∃ j, t∈P.cd B j) ∨
    (cr=true ∧ t=B (P.L.hub P.L.K))
  del_home : ∀ j, ∀ t∈P.cd B j, t∈r .coreFinal → t∈P.homeGoals j
  del_src : ∀ j, ∀ t∈P.cd B j, t∉r .coreSource
  exp_fin : ∀ j, ∀ t∈P.ce B j, t∉r .coreFinal
  entered : ∀ j, ∀ i, ∀ hi : i < (P.ce B j).length, (P.ce B j).length ≤ i + (led j).k →
    (P.ce B j)[i] ∉ r .coreSource →
      P.sourceless j (ch j) ∧ ∀ i', ∀ hi' : i' < (P.ce B j).length, i < i' →
        (P.ce B j)[i'] ∉ r .coreSource
  sumS : ∑ j, (led j).S=ecNow
  sumG : ∑ j, (led j).G=acNow

namespace Inner
variable {P} {B : Board n} {r : Roles n} {led : Fin J → Ledger.Counter}
  {ch : (j : Fin J) → (P.Q j).Rec} {cap ecNow acNow : Nat} {cs cr : Bool}

theorem mem_childSrc_cell (h : P.Inner B r led ch cap ecNow acNow cs cr) {j : Fin J} {t : Tile n}
    (ht : t∈P.childSrc j (ch j)) : ∃ x∈(P.Q j).cells, B x=t := by
  have hc : t∈contents ((P.Q j).roles (ch j)) := by
    rw [Sound.contents_eq]
    simp only [childSrc,mem_union] at ht ⊢
    tauto
  rw [←((P.Q j).sound (h.child j)).inventory.exact] at hc
  simpa using hc

theorem mem_childFin_cell (h : P.Inner B r led ch cap ecNow acNow cs cr) {j : Fin J} {t : Tile n}
    (ht : t∈P.childFin j (ch j)) : ∃ x∈(P.Q j).cells, B x=t := by
  have hc : t∈contents ((P.Q j).roles (ch j)) := by
    rw [Sound.contents_eq]
    simp only [childFin,mem_union] at ht ⊢
    tauto
  rw [←((P.Q j).sound (h.child j)).inventory.exact] at hc
  simpa using hc

theorem cell_of_ce {j : Fin J} {t : Tile n} (ht : t∈P.ce B j) : ∃ c∈P.L.exportQ j, B c=t := by
  simpa [ce] using ht

theorem cell_of_cd {j : Fin J} {t : Tile n} (ht : t∈P.cd B j) : ∃ c∈P.L.deliveryQ j, B c=t := by
  simpa [cd] using ht

theorem exportQ_not_child {j j' : Fin J} {c : Cell n} (hc : c∈P.L.exportQ j) : c∉(P.Q j').cells :=
  P.L.loop_child j j' c (P.L.mem_loop_of_exportQ hc)

theorem deliveryQ_not_child {j j' : Fin J} {c : Cell n} (hc : c∈P.L.deliveryQ j) : c∉(P.Q j').cells :=
  P.L.loop_child j j' c (P.L.mem_loop_of_deliveryQ hc)

/-- Inside child `j`, P's core sources are exactly the child's sources. -/
theorem src_iff_child (h : P.Inner B r led ch cap ecNow acNow cs cr) (j : Fin J) {x : Cell n}
    (hx : x∈(P.Q j).cells) : B x∈r .coreSource ↔ B x∈P.childSrc j (ch j) := by
  constructor
  · intro hs
    rcases h.src_loc _ hs with ⟨j',hj'⟩ | ⟨j',hj'⟩ | ⟨_,hK⟩
    · obtain ⟨x',hx',eq⟩ := h.mem_childSrc_cell hj'
      have hxx : x'=x := B.injective eq
      subst hxx
      by_cases hjj : j'=j
      · subst hjj; exact hj'
      · exact absurd hx (disjoint_left.mp (P.L.children_disjoint j' j hjj) hx')
    · obtain ⟨c,hc,eq⟩ := cell_of_ce hj'
      have : c=x := B.injective eq
      subst this
      exact absurd hx (exportQ_not_child hc)
    · have : P.L.hub P.L.K=x := B.injective hK.symm
      subst this
      exact absurd hx (P.L.hub_child j).1
  · exact fun hs => h.src_child j hs

/-- Inside child `j`, P's core finals are exactly the child's finals. -/
theorem fin_iff_child (h : P.Inner B r led ch cap ecNow acNow cs cr) (j : Fin J) {x : Cell n}
    (hx : x∈(P.Q j).cells) : B x∈r .coreFinal ↔ B x∈P.childFin j (ch j) := by
  constructor
  · intro hs
    rcases h.fin_loc _ hs with ⟨j',hj'⟩ | ⟨j',hj'⟩ | ⟨_,hK⟩
    · obtain ⟨x',hx',eq⟩ := h.mem_childFin_cell hj'
      have hxx : x'=x := B.injective eq
      subst hxx
      by_cases hjj : j'=j
      · subst hjj; exact hj'
      · exact absurd hx (disjoint_left.mp (P.L.children_disjoint j' j hjj) hx')
    · obtain ⟨c,hc,eq⟩ := cell_of_cd hj'
      have : c=x := B.injective eq
      subst this
      exact absurd hx (deliveryQ_not_child hc)
    · have : P.L.hub P.L.K=x := B.injective hK.symm
      subst this
      exact absurd hx (P.L.hub_child j).1
  · exact fun hs => h.fin_child j hs

end Inner

theorem deliveryQ_nodup (j : Fin J) : (P.L.deliveryQ j).Nodup := by
  have h := P.L.loop_nodup j
  have split : loopOf (P.L.x j) (P.L.exportLane j) (P.L.z j) (P.L.e j) (P.L.deliveryLane j) (P.L.hub (P.L.H j))=
      (P.L.x j :: P.L.exportQ j)++(P.L.deliveryQ j++[P.L.hub (P.L.H j)]) := by
    simp [loopOf,StarLayout.exportQ,StarLayout.deliveryQ]
  rw [split] at h
  exact (List.nodup_append.mp (List.nodup_append.mp h).2.1).1

theorem cd_nodup (B : Board n) (j : Fin J) : (P.cd B j).Nodup :=
  (P.deliveryQ_nodup j).map B.injective

omit [NeZero n] in
theorem countP_eq_card {l : List (Tile n)} (hl : l.Nodup) (p : Tile n → Prop) [DecidablePred p] :
    l.countP p=(l.filter p).toFinset.card := by
  rw [List.toFinset_card_of_nodup (hl.filter _),List.countP_eq_length_filter]

theorem homeGoals_card (j : Fin J) : (P.homeGoals j).card=P.pop j := by
  unfold homeGoals pop
  rw [card_union_of_disjoint,Frame.coreGoals_card,Frame.reserveGoals_card]
  unfold Frame.coreGoals Frame.reserveGoals
  rw [disjoint_image (P.Q j).goal.injective]
  exact (P.Q j).core_reserve

namespace Inner
variable {P} {B : Board n} {r : Roles n} {led : Fin J → Ledger.Counter}
  {ch : (j : Fin J) → (P.Q j).Rec} {cap ecNow acNow : Nat} {cs cr : Bool}

theorem childFin_card (h : P.Inner B r led ch cap ecNow acNow cs cr) (j : Fin J) :
    (P.childFin j (ch j)).card=((P.Q j).counts (ch j)).ac+((P.Q j).counts (ch j)).ar := by
  have hs := (P.Q j).sound (h.child j)
  unfold childFin
  rw [card_union_of_disjoint (hs.inventory.disjoint _ _ (by decide)),hs.coreFinals,hs.reserveFinals]

theorem childFin_home (h : P.Inner B r led ch cap ecNow acNow cs cr) (j : Fin J) :
    P.childFin j (ch j)⊆P.homeGoals j := by
  have hs := (P.Q j).sound (h.child j)
  unfold childFin homeGoals
  exact union_subset_union hs.coreFinal_goal hs.reserveFinal_goal

/-- A real goal for spoke `j` sitting in the carrier is one more than the
goals of `j` already received, so there is room for it. -/
theorem real_room (h : P.Inner B r led ch cap ecNow acNow cs cr) (j : Fin J)
    (_hK : B (P.L.hub P.L.K)∈r .coreFinal) (hhome : B (P.L.hub P.L.K)∈P.homeGoals j) :
    (led j).G<P.pop j := by
  classical
  set T := ((P.cd B j).filter (fun t => t∈r .coreFinal)).toFinset
  have hT : (P.cd B j).countP (fun t => t∈r .coreFinal)=T.card := countP_eq_card (P.cd_nodup B j) _
  have hTsub : T⊆P.homeGoals j := by
    intro t ht
    simp only [T,List.mem_toFinset,List.mem_filter,decide_eq_true_eq] at ht
    exact h.del_home j t ht.1 ht.2
  have hd1 : Disjoint (P.childFin j (ch j)) T := by
    apply disjoint_left.mpr
    intro t h1 h2
    obtain ⟨x,hx,rfl⟩ := h.mem_childFin_cell h1
    simp only [T,List.mem_toFinset,List.mem_filter] at h2
    obtain ⟨c,hc,eq⟩ := cell_of_cd h2.1
    have : c=x := B.injective eq
    subst this
    exact deliveryQ_not_child hc hx
  have hKc : B (P.L.hub P.L.K)∉P.childFin j (ch j)∪T := by
    intro hm
    rcases mem_union.mp hm with h1 | h2
    · obtain ⟨x,hx,eq⟩ := h.mem_childFin_cell h1
      have : x=P.L.hub P.L.K := B.injective eq
      subst this
      exact (P.L.hub_child j).1 hx
    · simp only [T,List.mem_toFinset,List.mem_filter] at h2
      obtain ⟨c,hc,eq⟩ := cell_of_cd h2.1
      have : c=P.L.hub P.L.K := B.injective eq
      subst this
      exact (P.L.hub_loop j).1 (P.L.mem_loop_of_deliveryQ hc)
  have sub : insert (B (P.L.hub P.L.K)) (P.childFin j (ch j)∪T)⊆P.homeGoals j :=
    insert_subset hhome (union_subset (h.childFin_home j) hTsub)
  have hc := card_le_card sub
  rw [card_insert_of_notMem hKc,card_union_of_disjoint hd1,h.childFin_card j,←hT,homeGoals_card] at hc
  have := h.bridgeG j
  omega

end Inner

end StarSpec
end SlidingPuzzle.NestedRouting.Interface
