import NestedRouting.Corner.Star
import NestedRouting.Corner.Entry
import NestedRouting.Star.Spec

/-! The corner node as a `StarSpec`: its frame, connector, squares and
markers. Children are given together with the facts that they sit in the
bodies of their slots, enter at their band corners, and keep their strips
in their bands. -/
namespace SlidingPuzzle.NestedRouting.Corner
open Interface Placement Finset

namespace Params
variable (p : Params) {n : Nat} [NeZero n] (q : Placement p.T n) [NeZero p.T]

def body : Finset (Cell n) := ((univ : Finset (Cell p.T)).filter (fun x => p.W≤x.1.val)).map q.embed
def markers : Finset (Cell n) := (range 6).image (fun i => q.loc (p.W+1) (p.M0+5+i))
def eP : Cell n := q.loc (2*p.cs) 0
def zP : Cell n := q.loc (2*p.cs+1) 0

omit [NeZero n] in
theorem mem_body {x : Cell n} : x∈p.body q ↔ ∃ r c, p.W≤r ∧ r<p.T ∧ c<p.T ∧ q.loc r c=x := by
  unfold body
  simp only [mem_map,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨y.1.val,y.2.val,hy,y.1.isLt,y.2.isLt,by rw [q.loc_eq y.1.isLt y.2.isLt]⟩
  · rintro ⟨r,c,h1,h2,h3,rfl⟩
    exact ⟨(⟨r,h2⟩,⟨c,h3⟩),h1,(q.loc_eq h2 h3).symm⟩

omit [NeZero n] in
theorem mem_markers {x : Cell n} : x∈p.markers q ↔ ∃ i<6, q.loc (p.W+1) (p.M0+5+i)=x := by
  simp [markers]

omit [NeZero n] in
theorem markers_card : (p.markers q).card=6 := by
  unfold markers
  rw [card_image_of_injOn]
  · simp
  · intro i hi j hj e
    have hb := p.hub_bound
    have := p.hub_fit
    simp only [coe_range,Set.mem_Iio] at hi hj
    have := p.coords q (by omega) (by unfold M0 J W at *; omega) (by omega) (by unfold M0 J W at *; omega) e
    omega

end Params
namespace Params
variable (p : Params) {n : Nat} [NeZero n] (q : Placement p.T n) [NeZero p.T]

def connTail : List (Cell n) :=
  Seg.mk (fun i => q.loc (2*p.cs+2+i) 0) (p.W-2*p.cs-1)++Seg.mk (fun i => q.loc p.W (1+i)) 2

def wm : Nat := p.W+p.M0+6

omit [NeZero p.T] in
theorem wm_fit : 0+p.wm≤p.T := by have := p.hub_fit; unfold wm W M0 J at *; omega

def wι : Cell p.wm ↪ Cell n := (q.sub 0 0 p.wm p.wm_fit p.wm_fit).embed

omit [NeZero n] in
theorem in_w {r c : Nat} (hr : r<p.wm) (hc : c<p.wm) : q.loc r c∈Set.range (p.wι q) := by
  have : NeZero p.wm := ⟨by unfold wm; omega⟩
  refine ⟨(⟨r,hr⟩,⟨c,hc⟩),?_⟩
  unfold wι
  rw [←(q.sub 0 0 p.wm p.wm_fit p.wm_fit).loc_eq hr hc,q.loc_sub p.wm_fit p.wm_fit hr hc]
  simp

omit [NeZero n] in
theorem in_range {r c : Nat} (hr : r<p.T) (hc : c<p.T) : q.loc r c∈Set.range q.embed :=
  ⟨(⟨r,hr⟩,⟨c,hc⟩),(q.loc_eq hr hc).symm⟩

variable (Q : Fin p.J → Region n)
  (hcells : ∀ j x, x∈(Q j).cells → ∃ r c, p.bodyP j r c ∧ q.loc r c=x)

include hcells in
/-- A cell above all child bodies lies in no child. -/
theorem notChild_low {r c : Nat} (hr : r<p.T) (hc : c<p.T) (hlow : r<p.W+4) (j : Fin p.J) :
    q.loc r c∉(Q j).cells := by
  intro h
  obtain ⟨r',c',hp,e⟩ := hcells j _ h
  have l := p.bodyP_lt j.isLt hp
  have := p.coords q l.1 l.2 hr hc e
  have hR : p.W+4≤p.R (p.rowOf j) := by unfold R; omega
  unfold bodyP at hp; omega

omit [NeZero n] in
theorem notMarker {r c : Nat} (hr : r<p.T) (hc : c<p.T) (h : r≠p.W+1 ∨ c<p.M0+5) :
    q.loc r c∉p.markers q := by
  rw [mem_markers]
  rintro ⟨i,hi,e⟩
  have hb := p.hub_bound
  have := p.hub_fit
  have := p.coords q (by omega) (by unfold M0 J W at *; omega) hr hc e
  omega

end Params
namespace Params
variable (p : Params) {n : Nat} [NeZero n] (q : Placement p.T n) [NeZero p.T]

def connP (r c : Nat) : Prop := (c=0 ∧ 2*p.cs+1≤r ∧ r≤p.W) ∨ (r=p.W ∧ 1≤c ∧ c≤2)

omit [NeZero n] in
theorem mem_conn {x : Cell n} : x∈p.zP q :: p.connTail q ↔ ∃ r c, p.connP r c ∧ q.loc r c=x := by
  have csW : 2*p.cs+1<p.W := p.strip_fit
  unfold zP connTail connP
  rw [List.mem_cons,List.mem_append,Seg.mem_down,Seg.mem_right]
  constructor
  · rintro (rfl | ⟨r,h1,h2,rfl⟩ | ⟨c,h1,h2,rfl⟩)
    · exact ⟨_,_,Or.inl ⟨rfl,le_rfl,by omega⟩,rfl⟩
    · exact ⟨r,0,Or.inl ⟨rfl,by omega,by omega⟩,rfl⟩
    · exact ⟨p.W,c,Or.inr ⟨rfl,by omega,by omega⟩,rfl⟩
  · rintro ⟨r,c,(⟨rfl,h1,h2⟩ | ⟨rfl,h1,h2⟩),rfl⟩
    · rcases Nat.lt_or_ge (2*p.cs+1) r with hr | hr
      · exact Or.inr (Or.inl ⟨r,by omega,by omega,rfl⟩)
      · have : r=2*p.cs+1 := by omega
        subst this; exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨c,h1,by omega,rfl⟩)

omit [NeZero p.T] in
theorem connP_lt {r c : Nat} (h : p.connP r c) : r<p.T ∧ c<p.T := by
  have := p.hub_fit
  unfold connP at h; unfold W at *; omega

omit [NeZero n] in
theorem conn_last' : (p.zP q :: p.connTail q).getLast (List.cons_ne_nil _ _)=q.loc p.W 2 := by
  have hM : 0<2 := by omega
  have h : (p.zP q :: p.connTail q).getLast?=some (q.loc p.W 2) := by
    change ([p.zP q]++p.connTail q).getLast?=_
    unfold connTail
    rw [List.getLast?_append,List.getLast?_append,Seg.getLast?_mk _ _ hM]
    simp only [Option.some_or]
  rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _)] at h
  exact Option.some.inj h

omit [NeZero n] in
theorem conn_chain' : Chained (p.zP q :: p.connTail q) := by
  have hb := p.hub_bound
  have csW : 2*p.cs+1<p.W := p.strip_fit
  have hM : 0<p.M0 := by unfold M0; omega
  unfold zP connTail
  change Chained ([q.loc (2*p.cs+1) 0]++(_++_))
  apply Seg.chained_append (chained_single _)
  · apply Seg.chained_append (Seg.chained_down q (by omega) (by omega)) (Seg.chained_right q (by omega) (by omega))
    intro a b ha hb'
    rw [Seg.getLast?_mk _ _ (by omega)] at ha
    rw [Seg.head?_mk _ _ (by omega)] at hb'
    cases ha; cases hb'
    have e1 : 2*p.cs+2+(p.W-2*p.cs-1-1)=p.W := by omega
    rw [e1,Nat.add_zero]
    exact p.adjH q (by omega) (by omega) (by omega) (Or.inl rfl)
  · intro a b ha hb'
    simp only [List.getLast?_singleton,Option.some.injEq] at ha
    rw [List.head?_append,Seg.head?_mk _ _ (by omega)] at hb'
    simp only [Option.some_or,Option.some.injEq] at hb'
    subst ha; subst hb'
    rw [Nat.add_zero]
    exact p.adjV q (by omega) (by omega) (by omega) (Or.inl rfl)

omit [NeZero n] in
theorem conn_nodup' : (p.zP q :: p.connTail q).Nodup := by
  have hb := p.hub_bound
  have csW : 2*p.cs+1<p.W := p.strip_fit
  unfold zP connTail
  rw [List.nodup_cons,List.nodup_append]
  refine ⟨?_,p.nodup_down q (by omega) (by omega),p.nodup_right q (by omega) (by omega),?_⟩
  · rw [List.mem_append,Seg.mem_down,Seg.mem_right]
    rintro (⟨r,h1,h2,e⟩ | ⟨c,h1,h2,e⟩)
    · have := (p.coords q (by omega) (by omega) (by omega) (by omega) e).1; omega
    · have := (p.coords q (by omega) (by omega) (by omega) (by omega) e).2; omega
  · intro a ha b hb' e
    rw [Seg.mem_down] at ha; rw [Seg.mem_right] at hb'
    obtain ⟨r,_,_,rfl⟩ := ha; obtain ⟨c,_,_,rfl⟩ := hb'
    have := (p.coords q (by omega) (by omega) (by omega) (by omega) e).2; omega

/-! ### The exchanges at the entry, by `t`-cycles

All frames run down from the entry row `2cs` and right from column 0, so
their block is `p = eP`, `q = (2cs,1)`, `s = zP`, `z = (2cs+1,1)`. -/

omit [NeZero p.T] in
theorem entry_fit : 2*p.cs+1<p.W ∧ p.W+p.M0+11≤p.T := by
  have := p.strip_fit; have := p.hub_fit; unfold W M0 J at *; constructor <;> omega

omit [NeZero p.T] in
theorem fit : Entry.Fit p.T p.W p.cs := by
  have := p.entry_fit; exact ⟨this.1,by omega,by omega⟩

/-- The wrapper frame reaches the carrier `K = (W+1,1)`. -/
def wFrame : Routes.Frame n :=
  Entry.frame q p.cs (p.W+2-2*p.cs) 6 (by have := p.entry_fit; omega) (by have := p.entry_fit; omega)
    (by have := p.entry_fit; omega)

/-- The third cell of the wrapper cycle, in the band next to the entry. -/
def wcell : Cell n := q.loc (2*p.cs) 1

open Classical in
/-- The weight of a cell in the final sort: the `t`-cycle bound at its
position in the direct frame. -/
noncomputable def sortW (x : Cell n) : Nat :=
  if h : ∃ y : Cell p.T, q.embed y=x then (3*(Cycle3.tw (h.choose.1.val-2*p.cs) h.choose.2.val+2)+3)/4 else 0

omit [NeZero n] in
theorem sortW_loc {r c : Nat} (hr : r<p.T) (hc : c<p.T) :
    p.sortW q (q.loc r c)=(3*(Cycle3.tw (r-2*p.cs) c+2)+3)/4 := by
  classical
  have h : ∃ y : Cell p.T, q.embed y=q.loc r c := ⟨(⟨r,hr⟩,⟨c,hc⟩),(q.loc_eq hr hc).symm⟩
  unfold sortW
  rw [dif_pos h]
  have := q.embed.injective (h.choose_spec.trans (q.loc_eq hr hc))
  rw [this]

/-- The wrapper cycle by one `t`-cycle: `t_K` in the wrapper frame. -/
theorem wrap_exchange (plus : Bool) (B : Board n) (hB : blank B=p.zP q) :
    ∃ C : Board n, ∃ path : Path B C, path.length≤Cycle3.tw (p.W+1-2*p.cs) 1+2 ∧ blank C=p.zP q ∧
      Cycle3.IsCycle B C (p.hub q p.K) (if plus then p.eP q else p.wcell q)
        (if plus then p.wcell q else p.eP q) := by
  have := p.entry_fit
  have e10 : (p.wFrame q).loc 1 0=p.zP q := by rw [wFrame,Entry.frame_loc]; rfl
  obtain ⟨C,path,len,bC,cyc⟩ := Cycle3.tcycle_s_at (p.wFrame q) (by change 3≤p.W+2-2*p.cs; omega)
    (by change 6≤6; omega) B (hB.trans e10.symm) (p.W+1-2*p.cs) 1
    (by change _<p.W+2-2*p.cs; omega) (by change _<6; omega) (Or.inl (by omega)) plus
  have eK : (p.wFrame q).loc (p.W+1-2*p.cs) 1=p.hub q p.K := by
    rw [wFrame,Entry.frame_loc,hubK]; congr 1; omega
  have e00 : (p.wFrame q).loc 0 0=p.eP q := by rw [wFrame,Entry.frame_loc]; rfl
  have e01 : (p.wFrame q).loc 0 1=p.wcell q := by rw [wFrame,Entry.frame_loc]; rfl
  rw [eK,e00,e01] at cyc
  exact ⟨C,path,len,bC.trans e10,cyc⟩

end Params

namespace Params
variable (p : Params) {n : Nat} [NeZero n] (q : Placement p.T n) [NeZero p.T]
  (Q : Fin p.J → Region n)
  (hcells : ∀ j x, x∈(Q j).cells → ∃ r c, p.bodyP j r c ∧ q.loc r c=x)
  (hstrip : ∀ j x, x∈(Q j).strip → ∃ r c, p.bandP j r c ∧ q.loc r c=x)
  (hentry : ∀ j, (Q j).Entry (p.e q j) (p.z q j))
  (G : Board n)
  (hgoalQ : ∀ j, (Q j).goal=G)
  (hgoal : ∀ x∈p.body q, G x≠0)
  (hp hq : Nat) (hq_pos : 0<hq) (harm : ∀ B : Nat, hq*∑ t ∈ Finset.Ioc 0 p.J, B/t≤hp*B)
  (wp1 wp2 : Nat) (wharm1 : ∀ B : Nat, hq*Ledger.layered (fun j : Fin p.J => p.rowOf j+p.colOf j) B≤wp1*B)
  (wharm2 : ∀ B : Nat, hq*Ledger.layered (fun j : Fin p.J => p.J-1-j.val) B≤wp2*B)

def childCellsF : Finset (Cell n) := univ.biUnion (fun j => (Q j).cells)

def own : Finset (Cell n) := p.body q \ (p.childCellsF Q∪p.markers q)

theorem mem_own {x : Cell n} :
    x∈p.own q Q ↔ x∈p.body q ∧ (∀ j, x∉(Q j).cells) ∧ x∉p.markers q := by
  simp [own,childCellsF,not_or]

theorem loc_own {r c : Nat} (hr : r<p.T) (hc : c<p.T) (hW : p.W≤r) (hch : ∀ j, q.loc r c∉(Q j).cells)
    (hm : r≠p.W+1 ∨ c<p.M0+5) : q.loc r c∈p.own q Q :=
  (p.mem_own q Q).mpr ⟨(p.mem_body q).mpr ⟨r,c,hW,hr,hc,rfl⟩,hch,p.notMarker q hr hc hm⟩

include hcells hstrip hentry hgoalQ hgoal hq_pos harm in
def base : StarBase n p.J := by
  have hb := p.hub_bound
  have hfit := p.hub_fit
  have csW : 2*p.cs+1<p.W := p.strip_fit
  have hWT : p.W<p.T := by unfold W M0 J at *; omega
  have hM0 : p.M0+11≤p.T := by unfold W M0 J at *; omega
  exact {
  Q := Q
  L := p.layout q Q hcells hentry
  goal := G
  goal_child := hgoalQ
  own := p.own q Q
  markers := p.markers q
  eP := p.eP q
  zP := p.zP q
  own_child := fun j => by
    rw [disjoint_left]; intro x hx hq; exact ((p.mem_own q Q).mp hx).2.1 j hq
  markers_child := fun j => by
    rw [disjoint_left]; intro x hx hq
    obtain ⟨i,hi,rfl⟩ := (p.mem_markers q).mp hx
    exact p.notChild_low q Q hcells (by omega) (by unfold M0 J W at *; omega) (by omega) j hq
  own_markers := by
    rw [disjoint_left]; intro x hx hm; exact ((p.mem_own q Q).mp hx).2.2 hm
  eP_zP := by
    intro e; have := p.coords q (by omega) (by omega) (by omega) (by omega) e; omega
  eP_own := by
    intro h; obtain ⟨r,c,h1,h2,h3,e⟩ := (p.mem_body q).mp ((p.mem_own q Q).mp h).1
    have := p.coords q h2 h3 (by omega) (by omega) e; omega
  eP_markers := p.notMarker q (by omega) (by omega) (Or.inl (by omega))
  eP_child := fun j => p.notChild_low q Q hcells (by omega) (by omega) (by omega) j
  zP_own := by
    intro h; obtain ⟨r,c,h1,h2,h3,e⟩ := (p.mem_body q).mp ((p.mem_own q Q).mp h).1
    have := p.coords q h2 h3 (by omega) (by omega) e; omega
  zP_markers := p.notMarker q (by omega) (by omega) (Or.inl (by omega))
  zP_child := fun j => p.notChild_low q Q hcells (by omega) (by omega) (by omega) j
  loop_own := by
    intro j c hc
    obtain ⟨r,c',hp,rfl⟩ := (p.mem_loop q j).mp hc
    have l := p.loopP_lt j.isLt hp
    have bj := p.bounds j.isLt
    have := bj.y_ge
    apply p.loc_own q Q l.1 l.2
    · unfold loopP expP delP at hp; omega
    · intro j'; exact (p.layout q Q hcells hentry).loop_child j j' _ hc
    · left; unfold loopP expP delP at hp; omega
  K_own := by
    change p.hub q p.K∈_
    rw [p.hubK q]
    exact p.loc_own q Q (by omega) (by omega) (by omega)
      (fun j => p.notChild_low q Q hcells (by omega) (by omega) (by omega) j) (Or.inr (by omega))
  strip_own := by
    intro j x hx
    obtain ⟨r,c,hp,rfl⟩ := hstrip j x hx
    have bj := p.bounds j.isLt
    have := bj.R_le; have := bj.f_le
    have hR : p.W+4≤p.R (p.rowOf j) := by unfold R; omega
    have hWT' : p.W<p.T' := by unfold W; have := p.band_fit; omega
    unfold bandP at hp
    have hf : p.f j=p.C (p.colOf j) := rfl
    apply p.loc_own q Q (by omega) (by omega) (by omega)
    · intro j' hq
      obtain ⟨r',c',hp',e⟩ := hcells j' _ hq
      have l' := p.bodyP_lt j'.isLt hp'
      obtain ⟨rfl,rfl⟩ := p.coords q l'.1 l'.2 (by omega) (by omega) e
      unfold bodyP at hp'
      by_cases hjj : (j : Nat)=j'
      · rw [hjj] at hp; omega
      · exact p.slot_disjoint j.isLt j'.isLt hjj ⟨hp.1,by omega,hp.2.2⟩ ⟨by omega,hp'.2.1,hp'.2.2⟩
    · left; omega
  goal_own := fun x hx => hgoal x ((p.mem_own q Q).mp hx).1
  goal_spare := by
    intro j x hx
    obtain ⟨r,c,hp,rfl⟩ := hcells j x (by simp only [Frame.cells,mem_union]; exact Or.inr hx)
    have l := p.bodyP_lt j.isLt hp
    have hR : p.W+4≤p.R (p.rowOf j) := by unfold R; omega
    unfold bodyP at hp
    exact hgoal _ ((p.mem_body q).mpr ⟨_,_,by omega,l.1,l.2,rfl⟩)
  connTail := p.connTail q
  conn_last := by
    rw [p.conn_last' q]; exact (p.hubW q).symm
  conn_chain := p.conn_chain' q
  conn_nodup := p.conn_nodup' q
  conn_free := by
    intro c hc
    obtain ⟨r,c',hp,rfl⟩ := (p.mem_conn q).mp hc
    have l := p.connP_lt hp
    have hrW : r≤p.W := by unfold connP at hp; omega
    refine ⟨fun j => ⟨?_,?_,p.notChild_low q Q hcells l.1 l.2 (by omega) j⟩,?_⟩
    · intro h
      obtain ⟨r',c'',hp',e⟩ := (p.mem_exportQ q j).mp h
      have l' := p.loopP_lt j.isLt (Or.inr (Or.inl hp'))
      have := p.coords q l'.1 l'.2 l.1 l.2 e
      unfold expP at hp'; have := (p.bounds j.isLt).y_ge; omega
    · intro h
      obtain ⟨r',c'',hp',e⟩ := (p.mem_deliveryQ q j).mp h
      have l' := p.loopP_lt j.isLt (Or.inr (Or.inr hp'))
      have := p.coords q l'.1 l'.2 l.1 l.2 e
      unfold delP at hp'; have := (p.bounds j.isLt).y_ge; omega
    · intro e
      change q.loc r c'=p.hub q p.K at e
      rw [p.hubK q] at e
      have := p.coords q l.1 l.2 (by omega) (by omega) e; omega
  conn_eP := by
    intro h
    obtain ⟨r,c,hp,e⟩ := (p.mem_conn q).mp h
    have l := p.connP_lt hp
    have := p.coords q l.1 l.2 (by omega) (by omega) e
    unfold connP at hp; omega
  conn_u := by
    intro h
    obtain ⟨r,c,hp,e⟩ := (p.mem_conn q).mp h
    have l := p.connP_lt hp
    change q.loc r c=p.hub q p.u at e; rw [p.hubU q] at e
    have := p.coords q l.1 l.2 (by omega) (by omega) e
    unfold connP at hp; omega
  conn_v := by
    intro h
    obtain ⟨r,c,hp,e⟩ := (p.mem_conn q).mp h
    have l := p.connP_lt hp
    change q.loc r c=p.hub q p.v at e; rw [p.hubV q] at e
    have := p.coords q l.1 l.2 (by omega) (by omega) e
    unfold connP at hp; omega
  u_own := by
    change p.hub q p.u∈_; rw [p.hubU q]
    exact p.loc_own q Q (by omega) (by omega) (by omega)
      (fun j => p.notChild_low q Q hcells (by omega) (by omega) (by omega) j) (Or.inr (by omega))
  v_own := by
    change p.hub q p.v∈_; rw [p.hubV q]
    exact p.loc_own q Q (by omega) (by omega) (by omega)
      (fun j => p.notChild_low q Q hcells (by omega) (by omega) (by omega) j) (Or.inr (by omega))
  wm := p.wm
  wι := p.wι q
  w_adj := by intro a b h; unfold wι; rw [Placement.distance]; exact h
  w_side := by unfold wm; omega
  w_eP := p.in_w q (r:=2*p.cs) (c:=0) (by unfold wm; omega) (by unfold wm; omega)
  w_zP := p.in_w q (r:=2*p.cs+1) (c:=0) (by unfold wm; omega) (by unfold wm; omega)
  w_K := by
    change p.hub q p.K∈_; rw [p.hubK q]
    exact p.in_w q (by unfold wm; omega) (by unfold wm; omega)
  w_u := by
    change p.hub q p.u∈_; rw [p.hubU q]
    exact p.in_w q (by unfold wm; omega) (by unfold wm; omega)
  w_v := by
    change p.hub q p.v∈_; rw [p.hubV q]
    exact p.in_w q (by unfold wm; omega) (by unfold wm; omega)
  u2 := p.u2
  u2_own := by
    change p.hub q p.u2∈_; rw [p.hubU2 q]
    exact p.loc_own q Q (by omega) (by omega) (by omega)
      (fun j => p.notChild_low q Q hcells (by omega) (by omega) (by omega) j) (Or.inr (by omega))
  u2_u := by change p.u2≠p.u; intro h; simp only [u2,u,hcell,Prod.mk.injEq,Fin.mk.injEq] at h; omega
  u2_v := by change p.u2≠p.v; intro h; simp only [u2,v,hcell,Prod.mk.injEq,Fin.mk.injEq] at h; omega
  u2_K := by change p.u2≠p.K; intro h; simp only [u2,K,hcell,Prod.mk.injEq,Fin.mk.injEq] at h; omega
  u2_loop := by
    intro j h
    change p.hub q p.u2∈_ at h; rw [p.hubU2 q] at h
    obtain ⟨r,c,hp,e⟩ := (p.mem_loop q j).mp h
    have l := p.loopP_lt j.isLt hp
    have := p.coords q l.1 l.2 (by omega) (by omega) e
    have bj := p.bounds j.isLt
    have := bj.y_ge
    unfold loopP expP delP at hp; omega
  u2_child := by
    intro j
    change p.hub q p.u2∉_; rw [p.hubU2 q]
    exact p.notChild_low q Q hcells (by omega) (by omega) (by omega) j
  pm := p.T
  pι := q.embed
  p_adj := by intro a b h; rw [Placement.distance]; exact h
  p_side := by omega
  p_eP := p.in_range q (by omega) (by omega)
  p_zP := p.in_range q (by omega) (by omega)
  p_own := by
    intro x hx
    obtain ⟨r,c,_,h2,h3,rfl⟩ := (p.mem_body q).mp ((p.mem_own q Q).mp hx).1
    exact p.in_range q h2 h3
  p_markers := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := (p.mem_markers q).mp hx
    exact p.in_range q (by omega) (by unfold M0 J W at *; omega)
  p_child := by
    intro j x hx
    obtain ⟨r,c,hp,rfl⟩ := hcells j x hx
    have l := p.bodyP_lt j.isLt hp
    exact p.in_range q l.1 l.2
  six := by rw [p.markers_card q]
  strip_walk := by
    intro j c hw hs
    obtain ⟨r,c',hp,rfl⟩ := hstrip j _ hs
    have bj := p.bounds j.isLt
    have := bj.R_le; have := bj.f_le; have := bj.a_eq; have := bj.y_band
    have hR : p.W+4≤p.R (p.rowOf j) := by unfold R; omega
    have hf : p.f j=p.C (p.colOf j) := rfl
    have hWT' : p.W<p.T' := by unfold W; have := p.band_fit; omega
    unfold bandP at hp
    have lr : r<p.T := by omega
    have lc : c'<p.T := by omega
    rcases hw with hw | hw
    · obtain ⟨r',c'',hp',e⟩ := (p.mem_access q j).mp hw
      have l' := p.accP_lt j.isLt hp'
      have := p.coords q l'.1 l'.2 lr lc e
      unfold accP at hp'; omega
    · rw [List.mem_cons] at hw
      rcases hw with hw | hw
      · change q.loc r c'=q.loc (p.W+2) (p.a j) at hw
        have := p.coords q lr lc (by omega) (by omega) hw; omega
      · obtain ⟨r',c'',hp',e⟩ := (p.mem_exportQ q j).mp hw
        have l' := p.loopP_lt j.isLt (Or.inr (Or.inl hp'))
        have := p.coords q l'.1 l'.2 lr lc e
        change q.loc r c'=q.loc (p.y j+1) (p.f j)
        have hC : p.M0≤p.C (p.colOf j) := by unfold C; omega
        unfold expP at hp'
        congr 1 <;> omega
  conn_strip := by
    intro c hc j hs
    obtain ⟨r,c',hp,e⟩ := (p.mem_conn q).mp hc
    obtain ⟨r',c'',hp',e'⟩ := hstrip j _ hs
    have l := p.connP_lt hp
    have bj := p.bounds j.isLt
    have := bj.R_le; have := bj.f_le
    have hR : p.W+4≤p.R (p.rowOf j) := by unfold R; omega
    have hWT' : p.W<p.T' := by unfold W; have := p.band_fit; omega
    have hf : p.f j=p.C (p.colOf j) := rfl
    unfold bandP at hp'
    have := p.coords q (by omega) (by omega) l.1 l.2 (e'.trans e.symm)
    unfold connP at hp; omega
  hp := hp
  hq := hq
  hq_pos := hq_pos
  harm := harm
  lw1 := 2*p.T'
  lw2 := 48
  ρ1 := fun j => p.rowOf j+p.colOf j
  ρ2 := fun j => p.J-1-j.val
  wp1 := wp1
  wp2 := wp2
  wharm1 := wharm1
  wharm2 := wharm2 }


include hcells in
/-- Cells of P (children, own cells, markers) lie in the body. -/
theorem body_coords {x : Cell n} (hx : (∃ j, x∈(Q j).cells) ∨ x∈p.own q Q ∨ x∈p.markers q) :
    ∃ r c, p.W≤r ∧ r<p.T ∧ c<p.T ∧ q.loc r c=x := by
  rcases hx with ⟨j,hj⟩ | hx | hx
  · obtain ⟨r,c,hp,e⟩ := hcells j x hj
    have l := p.bodyP_lt j.isLt hp
    have hR : p.W+4≤p.R (p.rowOf j) := by unfold R; omega
    unfold bodyP at hp
    exact ⟨r,c,by omega,l.1,l.2,e⟩
  · exact (p.mem_body q).mp ((p.mem_own q Q).mp hx).1
  · obtain ⟨i,hi,rfl⟩ := (p.mem_markers q).mp hx
    have := p.entry_fit
    exact ⟨_,_,by omega,by omega,by unfold M0 J W at *; omega,rfl⟩

include hcells in
theorem row_W_facts {c : Nat} (hc : c<2) :
    q.loc p.W c∈p.own q Q ∧
      (∀ j, q.loc p.W c∉loopOf (p.x q j) (p.exportLane q j) (p.z q j) (p.e q j) (p.deliveryLane q j)
        (p.hub q (p.H j))) ∧ (∀ j, q.loc p.W c∉(Q j).cells) ∧
      q.loc p.W c≠p.hub q p.K := by
  have := p.entry_fit; have := p.hub_bound
  refine ⟨p.loc_own q Q (by omega) (by omega) le_rfl
    (fun j => p.notChild_low q Q hcells (by omega) (by omega) (by omega) j) (Or.inl (by omega)),?_,
    fun j => p.notChild_low q Q hcells (by omega) (by omega) (by omega) j,?_⟩
  · intro j h
    obtain ⟨r,c',hp,e⟩ := (p.mem_loop q j).mp h
    have l := p.loopP_lt j.isLt hp
    have := p.coords q l.1 l.2 (by omega) (by omega) e
    have bj := p.bounds j.isLt
    have := bj.y_ge
    unfold loopP expP delP at hp; omega
  · rw [hubK]; intro e
    have := p.coords q (by omega) (by omega) (by omega) (by omega) e; omega

include hcells in
/-- Cells left of the child columns are in no child. -/
theorem notChild_left {r c : Nat} (hr : r<p.T) (hc : c<p.M0) (j : Fin p.J) : q.loc r c∉(Q j).cells := by
  intro h
  obtain ⟨r',c',hp,e⟩ := hcells j _ h
  have l := p.bodyP_lt j.isLt hp
  have := p.hub_bound
  have := p.coords q l.1 l.2 hr (by omega) e
  have hC : p.M0≤p.C (p.colOf j) := by unfold C; omega
  unfold bodyP at hp; omega

/-- Static margin cells: in the body rows of slot row `ρ`, the four left
columns and the margin columns of the spokes of slot rows `≤ ρ`. -/
def statP (r c : Nat) : Prop :=
  ∃ ρ<p.b, p.R ρ+p.W≤r ∧ r<p.R ρ+p.T' ∧ c<p.M0 ∧ (c<4 ∨ p.M0≤c+2*p.b*(ρ+1))

instance (r c : Nat) : Decidable (p.statP r c) := by unfold statP; infer_instance

def statF : Finset (Cell n) :=
  (((range p.T)×ˢ(range p.T)).filter (fun rc => p.statP rc.1 rc.2)).image (fun rc => q.loc rc.1 rc.2)

omit [NeZero n] in
theorem mem_statF {x : Cell n} : x∈p.statF q ↔ ∃ r c, r<p.T ∧ c<p.T ∧ p.statP r c ∧ q.loc r c=x := by
  unfold statF
  simp only [mem_image,mem_filter,mem_product,mem_range,Prod.exists]
  constructor
  · rintro ⟨r,c,⟨⟨hr,hc⟩,hp⟩,rfl⟩; exact ⟨r,c,hr,hc,hp,rfl⟩
  · rintro ⟨r,c,hr,hc,hp,rfl⟩; exact ⟨r,c,⟨⟨hr,hc⟩,hp⟩,rfl⟩

omit [NeZero n] [NeZero p.T] in
/-- Slot rows are ordered. -/
theorem R_mono {ρ ρ' : Nat} (h : ρ<ρ') : p.R ρ+p.T'≤p.R ρ' := by
  unfold R
  have : (ρ+1)*p.T'≤ρ'*p.T' := Nat.mul_le_mul_right _ h
  rw [Nat.add_mul,Nat.one_mul] at this; omega

omit [NeZero n] [NeZero p.T] in
/-- A static cell is on no loop. -/
theorem statP_not_loop {r c : Nat} (hs : p.statP r c) (j : Fin p.J) : ¬p.loopP j r c := by
  obtain ⟨ρ,hρ,h1,h2,h3,h4⟩ := hs
  have hb := p.bounds j.isLt
  have ha := hb.a_eq; have ha4 := hb.a_ge; have hy := hb.y_band; have hyW := hb.y_ge
  have hWT : p.W<p.T' := by unfold W; have := p.band_fit; omega
  have hR0 : p.W+4≤p.R ρ := by unfold R; omega
  -- band rows of `rowOf j` lie outside the body rows of slot row `ρ`
  have band (r' : Nat) (hr1 : p.R (p.rowOf j)≤r') (hr2 : r'<p.R (p.rowOf j)+p.W) : r'≠r := by
    intro e; subst e
    rcases Nat.lt_trichotomy (p.rowOf j) ρ with hl | he | hg
    · have := p.R_mono hl; omega
    · rw [he] at hr2; omega
    · have := p.R_mono hg; omega
  -- a margin column of spoke `j` is static only below its slot row
  have col (hc : c=p.a j ∨ c=p.a j+1) : p.rowOf j≤ρ := by
    have hc4 : 4≤c := by omega
    have h4' : p.M0≤c+2*p.b*(ρ+1) := by omega
    have hj : j.val<p.b*(ρ+1) := by
      have : 2*(j.val+1)≤2*p.b*(ρ+1)+1 := by omega
      have e : 2*p.b*(ρ+1)=2*(p.b*(ρ+1)) := by ring
      omega
    unfold rowOf; exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul p.b_pos).mpr (by rw [Nat.mul_comm] at hj; omega))
  unfold loopP expP delP
  rintro (⟨rfl,_⟩ | (⟨rfl,_,h5⟩ | ⟨rfl,_,_⟩) | (⟨rfl,_,_⟩ | ⟨rfl,_,h5⟩))
  · omega
  · have := col (Or.inl rfl)
    rcases Nat.lt_or_eq_of_le this with hl | he
    · have := p.R_mono hl; omega
    · rw [he] at hy; omega
  · exact band (p.y j+1) (by omega) (by omega) rfl
  · exact band (p.y j) (by omega) (by omega) rfl
  · have := col (Or.inr rfl)
    rcases Nat.lt_or_eq_of_le this with hl | he
    · have := p.R_mono hl; omega
    · rw [he] at hy; omega

include hcells in
/-- Static cells are own cells off the loops, the carrier and the parking cells. -/
theorem stat_facts {x : Cell n} (hx : x∈p.statF q) :
    x∈p.own q Q ∧ (∀ j, x∉loopOf (p.x q j) (p.exportLane q j) (p.z q j) (p.e q j) (p.deliveryLane q j)
      (p.hub q (p.H j))) ∧ x≠p.hub q p.K ∧ x≠q.loc p.W 0 ∧ x≠q.loc p.W 1 := by
  obtain ⟨r,c,hr,hc,hs,rfl⟩ := (p.mem_statF q).mp hx
  have hs' := hs
  obtain ⟨ρ,hρ,h1,h2,h3,_⟩ := hs'
  have := p.hub_bound
  have hR0 : p.W+4≤p.R ρ := by unfold R; omega
  refine ⟨p.loc_own q Q hr hc (by omega) (fun j => p.notChild_left q Q hcells hr h3 j) (Or.inl (by omega)),?_,?_,?_,?_⟩
  · intro j h
    obtain ⟨r',c',hp,e⟩ := (p.mem_loop q j).mp h
    have l := p.loopP_lt j.isLt hp
    obtain ⟨rfl,rfl⟩ := p.coords q l.1 l.2 hr hc e
    exact p.statP_not_loop hs j hp
  · rw [hubK]; intro e; have := p.coords q hr hc (by omega) (by omega) e; omega
  · intro e; have := p.coords q hr hc (by omega) (by omega) e; omega
  · intro e; have := p.coords q hr hc (by omega) (by omega) e; omega

/-- The cost of a direct exchange with a cell, by its position. -/
noncomputable def dwW (x : Cell n) : Nat :=
  if h : ∃ y : Cell p.T, q.embed y=x then Entry.dw q p.fit h.choose.1.val h.choose.2.val else 0

omit [NeZero n] in
theorem dwW_loc {r c : Nat} (hr : r<p.T) (hc : c<p.T) : p.dwW q (q.loc r c)=Entry.dw q p.fit r c := by
  classical
  have h : ∃ y : Cell p.T, q.embed y=q.loc r c := ⟨(⟨r,hr⟩,⟨c,hc⟩),(q.loc_eq hr hc).symm⟩
  unfold dwW
  rw [dif_pos h]
  have := q.embed.injective (h.choose_spec.trans (q.loc_eq hr hc))
  rw [this]

include hcells hstrip hentry hgoalQ hgoal hq_pos harm in
/-- The corner node: the wrapper cycle and the direct exchange are
`t`-cycles at the entry. -/
noncomputable def spec : StarSpec n p.J :=
  { p.base q Q hcells hstrip hentry G hgoalQ hgoal hp hq hq_pos harm wp1 wp2 wharm1 wharm2 with
    wc := p.wcell q
    wcost := Cycle3.tw (p.W+1-2*p.cs) 1+2
    wX := fun B hB => by
      have := p.wrap_exchange q true B hB
      simp only [if_true] at this
      exact this
    wX' := fun B hB => by
      obtain ⟨C,path,len,bC,cyc⟩ := p.wrap_exchange q false B hB
      simp only [Bool.false_eq_true,if_false] at cyc
      exact ⟨C,path,len,bC,cyc.rotate.rotate⟩
    wc_conn := by
      have := p.entry_fit
      intro h
      obtain ⟨r,c,hp,e⟩ := (p.mem_conn q).mp h
      have l := p.connP_lt hp
      have := p.coords q l.1 l.2 (by omega) (by omega) e
      unfold connP at hp; omega
    wc_loop := by
      have := p.entry_fit
      intro j h
      obtain ⟨r,c,hp,e⟩ := (p.mem_loop q j).mp h
      have l := p.loopP_lt j.isLt hp
      have := p.coords q l.1 l.2 (by omega) (by omega) e
      have bj := p.bounds j.isLt
      have := bj.y_ge
      unfold loopP expP delP at hp; omega
    wc_child := fun j => by
      have := p.entry_fit
      exact p.notChild_low q Q hcells (by omega) (by omega) (by omega) j
    wc_K := by
      have := p.entry_fit; have := p.hub_bound
      change p.wcell q≠p.hub q p.K
      rw [hubK]; intro e
      have := p.coords q (by omega) (by omega) (by omega) (by omega) e; omega
    park := fun c => c=q.loc p.W 0 ∨ c=q.loc p.W 1
    dcost := Entry.dcost q p.fit
    dX := fun B x hB hx => by
      obtain ⟨r,c,hr,hrT,hc,rfl⟩ := p.body_coords q Q hcells hx
      have := p.entry_fit
      have d01 : q.loc p.W 0≠q.loc p.W 1 := fun e => by
        have := p.coords q (by omega) (by omega) (by omega) (by omega) e; omega
      by_cases h0 : q.loc r c=q.loc p.W 0
      · obtain ⟨C,path,len,bC,cyc⟩ := Entry.direct_exchange q p.fit B hB hr hrT hc (c':=1) (by omega) (h0 ▸ d01)
        exact ⟨C,path,_,Or.inr rfl,(h0 ▸ d01).symm,bC,cyc.1,cyc.2.1,cyc.2.2.1,cyc.2.2.2,len⟩
      · obtain ⟨C,path,len,bC,cyc⟩ := Entry.direct_exchange q p.fit B hB hr hrT hc (c':=0) (by omega) h0
        exact ⟨C,path,_,Or.inl rfl,Ne.symm h0,bC,cyc.1,cyc.2.1,cyc.2.2.1,cyc.2.2.2,len⟩
    park_own := by
      rintro c (rfl | rfl)
      · exact (p.row_W_facts q Q hcells (c:=0) (by omega)).1
      · exact (p.row_W_facts q Q hcells (c:=1) (by omega)).1
    park_loop := by
      rintro c (rfl | rfl)
      · exact (p.row_W_facts q Q hcells (c:=0) (by omega)).2.1
      · exact (p.row_W_facts q Q hcells (c:=1) (by omega)).2.1
    park_child := by
      rintro c (rfl | rfl)
      · exact (p.row_W_facts q Q hcells (c:=0) (by omega)).2.2.1
      · exact (p.row_W_facts q Q hcells (c:=1) (by omega)).2.2.1
    park_K := by
      rintro c (rfl | rfl)
      · exact (p.row_W_facts q Q hcells (c:=0) (by omega)).2.2.2
      · exact (p.row_W_facts q Q hcells (c:=1) (by omega)).2.2.2
    stat := p.statF q
    stat_own := fun x hx => (p.stat_facts q Q hcells hx).1
    stat_loop := fun x hx => (p.stat_facts q Q hcells hx).2.1
    stat_K := fun x hx => (p.stat_facts q Q hcells hx).2.2.1
    stat_park := by
      rintro x hx (rfl | rfl)
      · exact (p.stat_facts q Q hcells hx).2.2.2.1 rfl
      · exact (p.stat_facts q Q hcells hx).2.2.2.2 rfl
    dw := p.dwW q
    dXw := fun B x hB hx => by
      obtain ⟨r,c,hr,hc,hs,rfl⟩ := (p.mem_statF q).mp hx
      obtain ⟨ρ,_,h1,_,_,_⟩ := hs
      have := p.entry_fit
      have hR0 : p.W+4≤p.R ρ := by unfold R; omega
      have n0 : q.loc r c≠q.loc p.W 0 := fun e => by
        have := p.coords q hr hc (by omega) (by omega) e; omega
      obtain ⟨C,path,len,bC,cyc⟩ := Entry.direct_exchange_at q p.fit B hB (by omega) hr hc (c':=0) (by omega) n0
      exact ⟨C,path,_,Or.inl rfl,Ne.symm n0,bC,cyc.1,cyc.2.1,cyc.2.2.1,cyc.2.2.2,by rw [p.dwW_loc q hr hc]; exact len⟩
    fw := p.sortW q
    fsort := fun B T R F hB hR _ inside hnonzero hpresent room =>
      Entry.finish q p.fit B T hB R F (fun x hx => p.body_coords q Q hcells (hR x hx)) (p.sortW q)
        (fun r c _ hr hc => by rw [p.sortW_loc q hr hc]; omega) inside hnonzero hpresent room }

end Params
end SlidingPuzzle.NestedRouting.Corner
