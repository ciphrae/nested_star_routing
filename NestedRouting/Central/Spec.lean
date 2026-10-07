import NestedRouting.Central.Layout
import NestedRouting.Star.Spec

/-! The central root as a `StarSpec`. Everything that is not a spoke's
loop lives on the middle row: the hub cells, the entry pair `eP, zP`
(left of the centre), the connector `zP → w` and six markers (right of the
hub). The root's own cells are all board cells outside the children,
markers and entry pair. -/
namespace SlidingPuzzle.NestedRouting.Central
open Interface Placement Finset Corner

set_option linter.unusedSectionVars false

namespace CParams
variable {n : Nat} [NeZero n] (p : CParams n)

theorem c_lt10 : p.c+11<p.N := by have := p.T_big; unfold c N; omega

/-- A cell of the middle row. -/
def mid (c0 : Nat) : Cell n := p.q0.loc p.c c0

def eP : Cell n := p.mid (p.c-2)
def zP : Cell n := p.mid (p.c-1)
def markers : Finset (Cell n) := (range 6).image (fun i => p.mid (p.c+5+i))

theorem mid_inj {a b : Nat} (ha : a<p.N) (hb : b<p.N) (h : p.mid a=p.mid b) : a=b :=
  (p.q0.loc_inj (by have := p.c_lt; omega) ha (by have := p.c_lt; omega) hb h).2

theorem mem_markers {y : Cell n} : y∈p.markers ↔ ∃ i<6, p.mid (p.c+5+i)=y := by
  simp [markers]

theorem markers_card : p.markers.card=6 := by
  unfold markers
  rw [card_image_of_injOn]
  · simp
  · intro i hi k hk e
    simp only [coe_range,Set.mem_Iio] at hi hk
    have := p.mid_inj (by have := p.c_lt10; omega) (by have := p.c_lt10; omega) e
    omega

theorem hubK' : p.hub K=p.mid (p.c+1) := p.hubK
theorem hubU' : p.hub u=p.mid (p.c+2) := p.hubU
theorem hubV' : p.hub v=p.mid (p.c+3) := p.hubV
theorem hubU2' : p.hub u2=p.mid (p.c+4) := p.hubU2
theorem hubW' : p.hub w=p.mid p.c := by
  unfold w mid; rw [hub_loc]; have := p.two_le_c; congr 1 <;> omega

theorem hub_mid (c0 : Nat) (h1 : p.c-2≤c0) (h2 : c0<p.c+5) : p.mid c0∈Set.range p.hub := by
  have := p.two_le_c
  refine ⟨hcell 2 (c0-(p.c-2)) (by omega) (by omega),?_⟩
  rw [hub_loc]; unfold mid; congr 1 <;> omega

/-- Frame cells of spoke quarters are not on the middle row. -/
theorem frame_ne_mid (j : Fin 4) {r c' c0 : Nat} (hr : p.B≤r) (hr2 : r<p.N) (hc2 : c'<p.N) (h0 : c0<p.N) :
    (p.frame j).loc r c'≠p.mid c0 :=
  p.mid_ne j (by unfold B at hr; omega) hr2 hc2 h0

variable (Q : Fin 4 → Region n)
  (hcells : ∀ j y, y∈(Q j).cells → ∃ r c', p.A+p.W≤r ∧ r<p.N ∧ p.A≤c' ∧ c'<p.N ∧ (p.frame j).loc r c'=y)
  (hstrip : ∀ j y, y∈(Q j).strip → ∃ r c', p.A≤r ∧ r<p.A+p.W ∧ p.A≤c' ∧ c'<p.N ∧ (p.frame j).loc r c'=y)
  (hentry : ∀ j, (Q j).Entry (p.e j) (p.z j))
  (G : Board n) (hgoalQ : ∀ j, (Q j).goal=G) (hG : ∀ y, y≠p.zP → G y≠0)

def childCellsF : Finset (Cell n) := univ.biUnion (fun j => (Q j).cells)
def own : Finset (Cell n) := univ\(childCellsF Q∪p.markers∪{p.eP,p.zP})

theorem mem_own {y : Cell n} :
    y∈p.own Q ↔ (∀ j, y∉(Q j).cells) ∧ y∉p.markers ∧ y≠p.eP ∧ y≠p.zP := by
  simp only [own,childCellsF,mem_sdiff,mem_univ,true_and,mem_union,mem_biUnion,mem_insert,
    mem_singleton,not_or,not_exists]
  tauto

include hcells in
theorem mid_notChild {c0 : Nat} (h0 : c0<p.N) (j : Fin 4) : p.mid c0∉(Q j).cells := by
  intro hc
  obtain ⟨r,c',h1,h2,h3,h4,e⟩ := hcells j _ hc
  have := p.B_le_A
  exact p.frame_ne_mid j (by omega) h2 h4 h0 e

include hstrip in
theorem mid_notStrip {c0 : Nat} (h0 : c0<p.N) (j : Fin 4) : p.mid c0∉(Q j).strip := by
  intro hc
  obtain ⟨r,c',h1,h2,h3,h4,e⟩ := hstrip j _ hc
  have := p.B_le_A; have := p.T_big; have := p.A_lt
  exact p.frame_ne_mid j (by omega) (by unfold A N at *; omega) h4 h0 e

include hcells in
theorem mid_own {c0 : Nat} (h0 : c0<p.N) (h1 : c0≠p.c-2) (h2 : c0≠p.c-1) (h3 : c0<p.c+5) :
    p.mid c0∈p.own Q := by
  have := p.two_le_c; have := p.c_lt10
  refine (p.mem_own Q).mpr ⟨fun j => p.mid_notChild Q hcells h0 j,?_,?_,?_⟩
  · rw [mem_markers]; rintro ⟨i,hi,e⟩
    have := p.mid_inj (by omega) h0 e; omega
  · intro e; exact h1 (p.mid_inj h0 (by omega) e)
  · intro e; exact h2 (p.mid_inj h0 (by omega) e)

theorem frame_notMarker (j : Fin 4) {r c' : Nat} (hr : p.B≤r) (hr2 : r<p.N) (hc2 : c'<p.N) :
    (p.frame j).loc r c'∉p.markers ∧ (p.frame j).loc r c'≠p.eP ∧ (p.frame j).loc r c'≠p.zP := by
  have := p.c_lt10; have := p.two_le_c
  refine ⟨?_,p.frame_ne_mid j hr hr2 hc2 (by omega),p.frame_ne_mid j hr hr2 hc2 (by omega)⟩
  rw [mem_markers]; rintro ⟨i,hi,e⟩
  exact p.frame_ne_mid j hr hr2 hc2 (by omega) e.symm

include hcells in
theorem loop_own' (j : Fin 4) {y : Cell n}
    (hy : y∈loopOf (p.x j) (p.exportLane j) (p.z j) (p.e j) (p.deliveryLane j) (p.hub (H j))) :
    y∈p.own Q := by
  have hc : ∀ j', y∉(Q j').cells := fun j' hq => by
    obtain ⟨r,c',hp,rfl⟩ := (p.mem_loop j).mp hy
    obtain ⟨r',c'',h1,h2,h3,h4,e⟩ := hcells j' _ hq
    have l := p.loopP_range hp; have := p.A_lt; have := p.B_le_A; have := p.W_two
    by_cases hj : j=j'
    · subst hj
      have := (p.coords j (by omega) (by omega) h2 h4 e.symm).1; omega
    · exact p.sep hj (by unfold B at l; omega) (by omega) (by unfold B at l; omega) (by omega)
        (by unfold B at *; omega) h2 (by unfold B at *; omega) h4 e.symm
  obtain ⟨r,c',hp,rfl⟩ := (p.mem_loop j).mp hy
  have l := p.loopP_range hp; have := p.A_lt
  have hr2 : r<p.N := by omega
  have hc2 : c'<p.N := by omega
  obtain ⟨m1,m2,m3⟩ := p.frame_notMarker j l.1 hr2 hc2
  exact (p.mem_own Q).mpr ⟨hc,m1,m2,m3⟩

include hcells hstrip hentry hgoalQ hG in
def base : StarBase n 4 := by
  have := p.c_lt10; have := p.two_le_c; have := p.A_lt; have := p.B_le_A; have hB : p.B=p.c+1 := rfl
  exact {
  Q := Q
  L := p.layout Q hcells hentry
  goal := G
  goal_child := hgoalQ
  own := p.own Q
  markers := p.markers
  eP := p.eP
  zP := p.zP
  own_child := fun j => by
    rw [disjoint_left]; intro y hy; exact ((p.mem_own Q).mp hy).1 j
  markers_child := fun j => by
    rw [disjoint_left]; intro y hy
    obtain ⟨i,hi,rfl⟩ := p.mem_markers.mp hy
    exact p.mid_notChild Q hcells (by omega) j
  own_markers := by
    rw [disjoint_left]; intro y hy; exact ((p.mem_own Q).mp hy).2.1
  eP_zP := by intro h; have := p.mid_inj (by omega) (by omega) h; omega
  eP_own := fun h => ((p.mem_own Q).mp h).2.2.1 rfl
  eP_markers := by
    rw [mem_markers]; rintro ⟨i,hi,e⟩; have := p.mid_inj (by omega) (by omega) e; omega
  eP_child := fun j => p.mid_notChild Q hcells (by omega) j
  zP_own := fun h => ((p.mem_own Q).mp h).2.2.2 rfl
  zP_markers := by
    rw [mem_markers]; rintro ⟨i,hi,e⟩; have := p.mid_inj (by omega) (by omega) e; omega
  zP_child := fun j => p.mid_notChild Q hcells (by omega) j
  loop_own := fun j y hy => p.loop_own' Q hcells j hy
  K_own := by
    change p.hub K∈_; rw [p.hubK']; exact p.mid_own Q hcells (by omega) (by omega) (by omega) (by omega)
  strip_own := by
    intro j y hy
    obtain ⟨r,c',h1,h2,h3,h4,rfl⟩ := hstrip j y hy
    have hT := p.T_big
    have hr : r<p.N := by unfold A N at *; omega
    have hBr : p.B≤r := by omega
    obtain ⟨m1,m2,m3⟩ := p.frame_notMarker j hBr hr h4
    refine (p.mem_own Q).mpr ⟨fun j' hq => ?_,m1,m2,m3⟩
    by_cases hj : j=j'
    · subst hj
      exact disjoint_left.mp (Q j).strip_out hy hq
    · obtain ⟨r',c'',h1',h2',h3',h4',e⟩ := hcells j' _ hq
      exact p.sep hj (by omega) hr (by omega) h4 (by omega) h2' (by omega) h4' e.symm
  goal_own := fun y hy => hG y ((p.mem_own Q).mp hy).2.2.2
  goal_spare := by
    intro j y hy
    apply hG
    rintro rfl
    have h0 : p.c-1<p.N := by omega
    exact p.mid_notChild Q hcells h0 j (by simp only [Frame.cells,mem_union]; exact Or.inr hy)
  connTail := [p.hub w]
  conn_last := by simp; rfl
  conn_chain := by
    apply List.isChain_cons_cons.mpr
    refine ⟨?_,List.isChain_singleton _⟩
    rw [hubW']; unfold zP mid
    have := p.q0.loc_adj_h (r:=p.c) (c:=p.c-1) (by omega) (by omega)
    rwa [show p.c-1+1=p.c by omega] at this
  conn_nodup := by
    simp only [List.nodup_cons,List.mem_singleton,List.not_mem_nil,not_false_eq_true,List.nodup_nil,
      and_true]
    rw [hubW']; intro h; have := p.mid_inj (by omega) (by omega) h; omega
  conn_free := by
    intro y hy
    have hm : ∃ c0, c0<p.N ∧ c0≠p.c+1 ∧ y=p.mid c0 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl
      · exact ⟨p.c-1,by omega,by omega,rfl⟩
      · exact ⟨p.c,by omega,by omega,p.hubW'⟩
    obtain ⟨c0,h0,h1,rfl⟩ := hm
    refine ⟨fun j => ⟨?_,?_,p.mid_notChild Q hcells h0 j⟩,?_⟩
    · intro h
      obtain ⟨r,c',hp,e⟩ := (p.mem_exportQ j).mp h
      have l := p.loopP_range (Or.inr (Or.inl hp))
      exact p.frame_ne_mid j l.1 (by omega) (by omega) h0 e
    · intro h
      obtain ⟨r,c',hp,e⟩ := (p.mem_deliveryQ j).mp h
      have l := p.loopP_range (Or.inr (Or.inr hp))
      exact p.frame_ne_mid j l.1 (by omega) (by omega) h0 e
    · change p.mid c0≠p.hub K
      rw [p.hubK']; intro h; exact h1 (p.mid_inj h0 (by omega) h)
  conn_eP := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    rw [hubW']
    exact ⟨fun h => by have := p.mid_inj (by omega) (by omega) h; omega,
      fun h => by have := p.mid_inj (by omega) (by omega) h; omega⟩
  conn_u := by
    change p.hub u∉_
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    rw [hubW',hubU']
    exact ⟨fun h => by have := p.mid_inj (by omega) (by omega) h; omega,
      fun h => by have := p.mid_inj (by omega) (by omega) h; omega⟩
  conn_v := by
    change p.hub v∉_
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    rw [hubW',hubV']
    exact ⟨fun h => by have := p.mid_inj (by omega) (by omega) h; omega,
      fun h => by have := p.mid_inj (by omega) (by omega) h; omega⟩
  u_own := by
    change p.hub u∈_; rw [p.hubU']; exact p.mid_own Q hcells (by omega) (by omega) (by omega) (by omega)
  v_own := by
    change p.hub v∈_; rw [p.hubV']; exact p.mid_own Q hcells (by omega) (by omega) (by omega) (by omega)
  wm := 7
  wι := p.hub
  w_adj := by intro a b h; unfold hub; rw [Placement.distance]; exact h
  w_side := by omega
  w_eP := p.hub_mid _ (by omega) (by omega)
  w_zP := p.hub_mid _ (by omega) (by omega)
  w_K := ⟨K,rfl⟩
  w_u := ⟨u,rfl⟩
  w_v := ⟨v,rfl⟩
  u2 := u2
  u2_own := by
    change p.hub u2∈_; rw [p.hubU2']; exact p.mid_own Q hcells (by omega) (by omega) (by omega) (by omega)
  u2_u := by change u2≠u; simp [u2,u,hcell]
  u2_v := by change u2≠v; simp [u2,v,hcell]
  u2_K := by change u2≠K; simp [u2,K,hcell]
  u2_loop := by
    intro j h
    change p.hub u2∈_ at h; rw [p.hubU2'] at h
    obtain ⟨r,c',hp,e⟩ := (p.mem_loop j).mp h
    have l := p.loopP_range hp
    exact p.frame_ne_mid j l.1 (by omega) (by omega) (by omega) e
  u2_child := by
    intro j; change p.hub u2∉_; rw [p.hubU2']; exact p.mid_notChild Q hcells (by omega) j
  pm := n
  pι := (boardP (n:=n)).embed
  p_adj := by intro a b h; rw [Placement.distance]; exact h
  p_side := by have := p.N_le; have := p.T_big; omega
  p_eP := boardP_range _
  p_zP := boardP_range _
  p_own := fun y _ => boardP_range y
  p_markers := fun y _ => boardP_range y
  p_child := fun _ y _ => boardP_range y
  six := by rw [p.markers_card]
  strip_walk := by
    intro j y hw hs
    obtain ⟨r',c'',h1,h2,h3,h4,rfl⟩ := hstrip j _ hs
    have hT := p.T_big
    have hr' : r'<p.N := by unfold A N at *; omega
    change _∈p.hub w :: p.accessTail j ∨ _∈p.x j :: (p.exportLane j++[p.z j]) at hw
    rw [List.mem_cons,p.mem_access,hubW p j,List.mem_cons] at hw
    rcases hw with (e | e | e) | (e | e)
    · have := (p.coords j hr' h4 (by omega) (by omega) e).1; omega
    · have := (p.coords j hr' h4 (by omega) (by omega) e).1; omega
    · have := (p.coords j hr' h4 (by omega) (by omega) e).1; omega
    · have := (p.coords j hr' h4 (by omega) (by omega) e).1; omega
    · obtain ⟨r,c',hp,e'⟩ := (p.mem_exportQ j).mp e
      have l := p.loopP_range (Or.inr (Or.inl hp))
      obtain ⟨rfl,rfl⟩ := p.coords j (by omega) (by omega) hr' h4 e'
      unfold expP at hp
      have : c'=p.A := by omega
      have hr : r=p.A+1 := by omega
      subst this; subst hr; rfl
  conn_strip := by
    intro y hy j
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact p.mid_notStrip Q hstrip (by omega) j
    · rw [hubW']; exact p.mid_notStrip Q hstrip (by omega) j
  hp := 3
  hq := 1
  hq_pos := Nat.one_pos
  harm := Ledger.harm_dyadic (m:=2) (by norm_num)
  lw1 := 0
  lw2 := 0
  ρ1 := fun _ => 0
  ρ2 := fun _ => 0
  wp1 := 0
  wp2 := 0
  wharm1 := fun _ => by simp [Ledger.layered]
  wharm2 := fun _ => by simp [Ledger.layered] }


end CParams
end SlidingPuzzle.NestedRouting.Central
