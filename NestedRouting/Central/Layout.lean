import NestedRouting.Central.Frames

/-! The central root layout: a pinwheel of four quadrant children around a
central hub, inside an odd square of side `N = 2T+2m+1` at the board
origin. Spoke `j` sees the square through the frame `frame j`, the square
reflected so that its quadrant is the lower-right one, entered at its
corner `(A,A)`, `A = T+2m+1`. In frame coordinates the spoke's loop lies in
the quarter of rows and columns `≥ c+1`, `c = T+m`; reflections of the
quarters are disjoint, and the middle row and column `c` belong to no
spoke. -/
namespace SlidingPuzzle.NestedRouting.Central
open Interface Placement Finset Corner

set_option linter.unusedSectionVars false

structure CParams (n : Nat) where
  T : Nat
  m : Nat
  W : Nat
  N_le : 2*T+2*m+1≤n
  m_two : 2≤m
  W_two : 2≤W
  T_big : W+12≤T

namespace CParams
variable {n : Nat} (p : CParams n)

def N : Nat := 2*p.T+2*p.m+1
/-- The centre row and column. -/
def c : Nat := p.T+p.m
def A : Nat := p.T+2*p.m+1

instance : NeZero p.N := ⟨by unfold N; omega⟩

theorem N_le' : 0+p.N≤n := by have := p.N_le; unfold N; omega

def fr (j : Fin 4) : Bool := decide (2≤j.val)
def fc (j : Fin 4) : Bool := decide (j.val%2=1)

/-- Reflection of one coordinate. -/
def ρ (f : Bool) (r : Nat) : Nat := if f then p.N-1-r else r

def frame (j : Fin 4) : Placement p.N n where
  row := 0
  col := 0
  flipRow := fr j
  flipCol := fc j
  row_fits := p.N_le'
  col_fits := p.N_le'

def q0 : Placement p.N n := ⟨0,0,false,false,p.N_le',p.N_le'⟩

theorem frame_row (j : Fin 4) {r c' : Nat} (hr : r<p.N) (hc : c'<p.N) :
    ((p.frame j).loc r c').1.val=p.ρ (fr j) r := by
  rw [(p.frame j).loc_eq hr hc]
  simp only [embed_row,axis,ρ,frame]
  split_ifs <;> omega

theorem frame_col (j : Fin 4) {r c' : Nat} (hr : r<p.N) (hc : c'<p.N) :
    ((p.frame j).loc r c').2.val=p.ρ (fc j) c' := by
  rw [(p.frame j).loc_eq hr hc]
  simp only [embed_col,axis,ρ,frame]
  split_ifs <;> omega

theorem q0_row {r c' : Nat} (hr : r<p.N) (hc : c'<p.N) : (p.q0.loc r c').1.val=r := by
  rw [p.q0.loc_eq hr hc]; simp [axis,q0]

theorem q0_col {r c' : Nat} (hr : r<p.N) (hc : c'<p.N) : (p.q0.loc r c').2.val=c' := by
  rw [p.q0.loc_eq hr hc]; simp [axis,q0]

omit p in
theorem fr_fc_inj {j j' : Fin 4} (h1 : fr j=fr j') (h2 : fc j=fc j') : j=j' := by
  unfold fr fc at *
  have := j.isLt; have := j'.isLt
  apply Fin.ext
  simp only [decide_eq_decide] at h1 h2
  omega

/-- On its own side of the centre. -/
theorem ρ_side (f : Bool) {r : Nat} (h1 : p.c+1≤r) (h2 : r<p.N) :
    (f=false → p.c+1≤p.ρ f r) ∧ (f=true → p.ρ f r+1≤p.c) := by
  unfold ρ N c at *
  cases f <;> simp <;> omega

/-- Frame cells in the quarters of different spokes are different, and
none lies on the middle row or column. -/
theorem sep {j j' : Fin 4} (h : j≠j') {r c' r' c'' : Nat} (hr : p.c+1≤r) (hr2 : r<p.N)
    (hc : p.c+1≤c') (hc2 : c'<p.N) (hr' : p.c+1≤r') (hr2' : r'<p.N) (hc' : p.c+1≤c'')
    (hc2' : c''<p.N) : (p.frame j).loc r c'≠(p.frame j').loc r' c'' := by
  intro e
  have e1 : ((p.frame j).loc r c').1.val=((p.frame j').loc r' c'').1.val := by rw [e]
  have e2 : ((p.frame j).loc r c').2.val=((p.frame j').loc r' c'').2.val := by rw [e]
  rw [p.frame_row j hr2 hc2,p.frame_row j' hr2' hc2'] at e1
  rw [p.frame_col j hr2 hc2,p.frame_col j' hr2' hc2'] at e2
  have s1 := p.ρ_side (fr j) hr hr2
  have s2 := p.ρ_side (fr j') hr' hr2'
  have s3 := p.ρ_side (fc j) hc hc2
  have s4 := p.ρ_side (fc j') hc' hc2'
  apply h
  apply fr_fc_inj
  · cases hx : fr j <;> cases hy : fr j' <;> simp_all <;> omega
  · cases hx : fc j <;> cases hy : fc j' <;> simp_all <;> omega

theorem mid_row (j : Fin 4) {r c' : Nat} (hr : p.c+1≤r) (hr2 : r<p.N) (hc2 : c'<p.N) :
    ((p.frame j).loc r c').1.val≠p.c := by
  rw [p.frame_row j hr2 hc2]
  have := p.ρ_side (fr j) hr hr2
  cases hx : fr j <;> simp_all <;> omega

/-- The centre is fixed by every frame. -/
theorem ρ_c (f : Bool) : p.ρ f p.c=p.c := by
  unfold ρ N c; cases f <;> simp; omega

/-! ### Spokes, in frame coordinates -/

/-- First row and column of the spoke quarters. -/
def B : Nat := p.c+1

theorem AB : p.A=p.B+p.m := by unfold A B c; omega
theorem A_lt : p.A+1<p.N := by have := p.T_big; unfold A N; omega
theorem c_lt : p.c+6<p.N := by have := p.T_big; unfold c N; omega

variable (j : Fin 4)

def x : Cell n := (p.frame j).loc p.B p.B
def z : Cell n := (p.frame j).loc (p.A+1) p.A
def e : Cell n := (p.frame j).loc p.A p.A

def exportLane : List (Cell n) :=
  Seg.mk (fun i => (p.frame j).loc (p.B+1+i) p.B) (p.A+1-p.B)++
  Seg.mk (fun i => (p.frame j).loc (p.A+1) (p.B+1+i)) (p.A-p.B-1)

def deliveryLane : List (Cell n) :=
  Seg.mk (fun i => (p.frame j).loc p.A (p.A-1-i)) (p.A-p.B-1)++
  Seg.mk (fun i => (p.frame j).loc (p.A-1-i) (p.B+1)) (p.A-p.B-1)

def accessTail : List (Cell n) := [(p.frame j).loc p.B p.c,p.x j]

/-- Export queue cells, `z` included. -/
def expP (r c' : Nat) : Prop :=
  (c'=p.B ∧ p.B+1≤r ∧ r≤p.A+1) ∨ (r=p.A+1 ∧ p.B+1≤c' ∧ c'≤p.A)
/-- Delivery queue cells, `e` included. -/
def delP (r c' : Nat) : Prop :=
  (r=p.A ∧ p.B+1≤c' ∧ c'≤p.A) ∨ (c'=p.B+1 ∧ p.B+1≤r ∧ r≤p.A-1)
def loopP (r c' : Nat) : Prop :=
  (r=p.B ∧ (c'=p.B ∨ c'=p.B+1)) ∨ p.expP r c' ∨ p.delP r c'

theorem loopP_range {r c' : Nat} (h : p.loopP r c') :
    p.B≤r ∧ r≤p.A+1 ∧ p.B≤c' ∧ c'≤p.A := by
  have := p.AB; have := p.m_two
  unfold loopP expP delP at h; omega

theorem mem_exportQ {y : Cell n} :
    y∈p.exportLane j++[p.z j] ↔ ∃ r c', p.expP r c' ∧ (p.frame j).loc r c'=y := by
  have := p.AB; have := p.m_two
  simp only [exportLane,z,List.mem_append,List.mem_singleton,Seg.mem_down,Seg.mem_right,expP]
  constructor
  · rintro ((⟨r,h1,h2,rfl⟩ | ⟨c',h1,h2,rfl⟩) | rfl)
    · exact ⟨r,p.B,Or.inl ⟨rfl,h1,by omega⟩,rfl⟩
    · exact ⟨p.A+1,c',Or.inr ⟨rfl,h1,by omega⟩,rfl⟩
    · exact ⟨p.A+1,p.A,Or.inr ⟨rfl,by omega,le_rfl⟩,rfl⟩
  · rintro ⟨r,c',(⟨rfl,h1,h2⟩ | ⟨rfl,h1,h2⟩),rfl⟩
    · exact Or.inl (Or.inl ⟨r,h1,by omega,rfl⟩)
    · rcases Nat.lt_or_ge c' p.A with hc | hc
      · exact Or.inl (Or.inr ⟨c',h1,by omega,rfl⟩)
      · have : c'=p.A := by omega
        subst this; exact Or.inr rfl

theorem mem_deliveryQ {y : Cell n} :
    y∈p.e j :: p.deliveryLane j ↔ ∃ r c', p.delP r c' ∧ (p.frame j).loc r c'=y := by
  have := p.AB; have := p.m_two
  simp only [deliveryLane,e,List.mem_cons,List.mem_append,delP]
  rw [Seg.mem_left (p.frame j) (by omega),Seg.mem_up (p.frame j) (by omega)]
  constructor
  · rintro (rfl | ⟨c',h1,h2,rfl⟩ | ⟨r,h1,h2,rfl⟩)
    · exact ⟨p.A,p.A,Or.inl ⟨rfl,by omega,le_rfl⟩,rfl⟩
    · exact ⟨p.A,c',Or.inl ⟨rfl,by omega,by omega⟩,rfl⟩
    · exact ⟨r,p.B+1,Or.inr ⟨rfl,by omega,by omega⟩,rfl⟩
  · rintro ⟨r,c',(⟨rfl,h1,h2⟩ | ⟨rfl,h1,h2⟩),rfl⟩
    · rcases Nat.lt_or_ge c' p.A with hc | hc
      · exact Or.inr (Or.inl ⟨c',by omega,by omega,rfl⟩)
      · have : c'=p.A := by omega
        subst this; exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨r,by omega,by omega,rfl⟩)

theorem mem_access {y : Cell n} :
    y∈p.accessTail j ↔ y=(p.frame j).loc p.B p.c ∨ y=p.x j := by
  simp [accessTail]

/-! ### The hub -/

theorem hub_fits : p.c-2+7≤p.N := by have := p.c_lt; have := p.T_big; unfold c at *; omega

def hub : Cell 7 ↪ Cell n := (p.q0.sub (p.c-2) (p.c-2) 7 p.hub_fits p.hub_fits).embed

def hcell (r c' : Nat) (hr : r<7) (hc : c'<7) : Cell 7 := (⟨r,hr⟩,⟨c',hc⟩)

def w : Cell 7 := hcell 2 2 (by omega) (by omega)
def K : Cell 7 := hcell 2 3 (by omega) (by omega)
def u : Cell 7 := hcell 2 4 (by omega) (by omega)
def v : Cell 7 := hcell 2 5 (by omega) (by omega)
def u2 : Cell 7 := hcell 2 6 (by omega) (by omega)
def H (j : Fin 4) : Cell 7 :=
  hcell (if fr j then 1 else 3) (if fc j then 0 else 4) (by split_ifs <;> omega) (by split_ifs <;> omega)

theorem hub_loc (r c' : Nat) (hr : r<7) (hc : c'<7) :
    p.hub (hcell r c' hr hc)=p.q0.loc (p.c-2+r) (p.c-2+c') := by
  unfold hub
  show (p.q0.sub (p.c-2) (p.c-2) 7 p.hub_fits p.hub_fits).embed (⟨r,hr⟩,⟨c',hc⟩)=_
  rw [←(p.q0.sub (p.c-2) (p.c-2) 7 p.hub_fits p.hub_fits).loc_eq hr hc,p.q0.loc_sub p.hub_fits p.hub_fits hr hc]

theorem cell_ext {a b : Cell n} (h1 : a.1.val=b.1.val) (h2 : a.2.val=b.2.val) : a=b :=
  Prod.ext (Fin.ext h1) (Fin.ext h2)

theorem two_le_c : 2≤p.c := by have := p.T_big; unfold c; omega

theorem hubW : p.hub w=(p.frame j).loc p.c p.c := by
  unfold w; rw [hub_loc]
  have := p.c_lt; have := p.two_le_c
  apply cell_ext
  · rw [p.q0_row (by omega) (by omega),p.frame_row j (by omega) (by omega),p.ρ_c]; omega
  · rw [p.q0_col (by omega) (by omega),p.frame_col j (by omega) (by omega),p.ρ_c]; omega

theorem hubK : p.hub K=p.q0.loc p.c (p.c+1) := by
  unfold K; rw [hub_loc]; have := p.two_le_c; congr 1 <;> omega
theorem hubU : p.hub u=p.q0.loc p.c (p.c+2) := by
  unfold u; rw [hub_loc]; have := p.two_le_c; congr 1 <;> omega
theorem hubV : p.hub v=p.q0.loc p.c (p.c+3) := by
  unfold v; rw [hub_loc]; have := p.two_le_c; congr 1 <;> omega
theorem hubU2 : p.hub u2=p.q0.loc p.c (p.c+4) := by
  unfold u2; rw [hub_loc]; have := p.two_le_c; congr 1 <;> omega

theorem hubH : p.hub (H j)=(p.frame j).loc p.B (p.B+1) := by
  unfold H; rw [hub_loc]
  have := p.c_lt; have := p.two_le_c
  apply cell_ext
  · rw [p.q0_row (by split_ifs <;> omega) (by split_ifs <;> omega),
      p.frame_row j (by unfold B; omega) (by unfold B; omega)]
    unfold ρ B N c at *; split_ifs <;> omega
  · rw [p.q0_col (by split_ifs <;> omega) (by split_ifs <;> omega),
      p.frame_col j (by unfold B; omega) (by unfold B; omega)]
    unfold ρ B N c at *; split_ifs <;> omega

/-- A middle-row cell is no frame cell of any spoke quarter. -/
theorem mid_ne {r c' c0 : Nat} (hr : p.c+1≤r) (hr2 : r<p.N) (hc2 : c'<p.N) (h0 : c0<p.N) :
    (p.frame j).loc r c'≠p.q0.loc p.c c0 := by
  intro h
  have h1 : ((p.frame j).loc r c').1.val=(p.q0.loc p.c c0).1.val := by rw [h]
  rw [p.q0_row (by have := p.c_lt; omega) h0] at h1
  exact p.mid_row j hr hr2 hc2 h1

theorem mem_loop {y : Cell n} :
    y∈loopOf (p.x j) (p.exportLane j) (p.z j) (p.e j) (p.deliveryLane j) (p.hub (H j)) ↔
      ∃ r c', p.loopP r c' ∧ (p.frame j).loc r c'=y := by
  have split : loopOf (p.x j) (p.exportLane j) (p.z j) (p.e j) (p.deliveryLane j)
      (p.hub (H j))=[p.x j]++(p.exportLane j++[p.z j])++(p.e j :: p.deliveryLane j)++
        [p.hub (H j)] := by
    simp [loopOf]
  rw [split,List.mem_append,List.mem_append,List.mem_append,p.mem_exportQ,p.mem_deliveryQ,
    List.mem_singleton,List.mem_singleton,hubH]
  unfold loopP
  constructor
  · rintro (((rfl | ⟨r,c',hp,rfl⟩) | ⟨r,c',hp,rfl⟩) | rfl)
    · exact ⟨_,_,Or.inl ⟨rfl,Or.inl rfl⟩,rfl⟩
    · exact ⟨r,c',Or.inr (Or.inl hp),rfl⟩
    · exact ⟨r,c',Or.inr (Or.inr hp),rfl⟩
    · exact ⟨_,_,Or.inl ⟨rfl,Or.inr rfl⟩,rfl⟩
  · rintro ⟨r,c',(⟨rfl,rfl | rfl⟩ | hp | hp),rfl⟩
    · exact Or.inl (Or.inl (Or.inl rfl))
    · exact Or.inr rfl
    · exact Or.inl (Or.inl (Or.inr ⟨r,c',hp,rfl⟩))
    · exact Or.inl (Or.inr ⟨r,c',hp,rfl⟩)

/-! ### Chains and distinctness -/

theorem coords {r c' r' c'' : Nat} (hr : r<p.N) (hc : c'<p.N) (hr' : r'<p.N) (hc' : c''<p.N)
    (h : (p.frame j).loc r c'=(p.frame j).loc r' c'') : r=r' ∧ c'=c'' :=
  (p.frame j).loc_inj hr hc hr' hc' h

theorem adjH {r c' c'' : Nat} (hr : r<p.N) (hc : c'<p.N) (hc' : c''<p.N) (h : c''=c'+1 ∨ c'=c''+1) :
    gridDistance ((p.frame j).loc r c') ((p.frame j).loc r c'')=1 := by
  rw [(p.frame j).loc_dist hr hc hr hc']; rcases h with rfl | rfl <;> simp [Nat.dist]

theorem adjV {r r' c' : Nat} (hr : r<p.N) (hr' : r'<p.N) (hc : c'<p.N) (h : r'=r+1 ∨ r=r'+1) :
    gridDistance ((p.frame j).loc r c') ((p.frame j).loc r' c')=1 := by
  rw [(p.frame j).loc_dist hr hc hr' hc]; rcases h with rfl | rfl <;> simp [Nat.dist]

omit p in
theorem chained_single (y : Cell n) : Chained [y] := List.isChain_singleton y

theorem access_chain : Chained (p.hub w :: p.accessTail j) := by
  have := p.A_lt; have := p.AB; have := p.c_lt
  rw [hubW]
  unfold accessTail x
  apply List.isChain_cons_cons.mpr
  refine ⟨p.adjV j (by omega) (by unfold B; omega) (by omega) (Or.inl (by unfold B; rfl)),?_⟩
  apply List.isChain_cons_cons.mpr
  exact ⟨p.adjH j (by unfold B; omega) (by omega) (by unfold B; omega) (Or.inl (by unfold B; rfl)),
    List.isChain_singleton _⟩

theorem out_chain : Chained (p.x j :: (p.exportLane j++[p.z j])) := by
  have := p.A_lt; have := p.AB; have := p.m_two
  unfold x exportLane z
  change Chained ([(p.frame j).loc p.B p.B]++((_++_)++[_]))
  apply Seg.chained_append (chained_single _)
  · apply Seg.chained_append
    · apply Seg.chained_append (Seg.chained_down (p.frame j) (by omega) (by omega))
        (Seg.chained_right (p.frame j) (by omega) (by omega))
      intro a b ha' hb'
      rw [Seg.getLast?_mk _ _ (by omega)] at ha'
      rw [Seg.head?_mk _ _ (by omega)] at hb'
      cases ha'; cases hb'
      have e1 : p.B+1+(p.A+1-p.B-1)=p.A+1 := by omega
      rw [e1,Nat.add_zero]
      exact p.adjH j (by omega) (by omega) (by omega) (Or.inl rfl)
    · exact chained_single _
    · intro a b ha' hb'
      rw [List.getLast?_append,Seg.getLast?_mk _ _ (by omega)] at ha'
      simp only [Option.some_or,Option.some.injEq,List.head?_cons] at ha' hb'
      cases ha'; cases hb'
      have e1 : p.B+1+(p.A-p.B-1-1)=p.A-1 := by omega
      rw [e1]
      exact p.adjH j (by omega) (by omega) (by omega) (Or.inl (by omega))
  · intro a b ha' hb'
    simp only [List.getLast?_singleton,Option.some.injEq] at ha'
    rw [List.head?_append,List.head?_append,Seg.head?_mk _ _ (by omega)] at hb'
    simp only [Option.some_or,Option.some.injEq] at hb'
    subst ha'; subst hb'
    rw [Nat.add_zero]
    exact p.adjV j (by omega) (by omega) (by omega) (Or.inl rfl)

theorem back_chain :
    Chained (p.z j :: (p.e j :: p.deliveryLane j++[p.hub (H j),p.x j])) := by
  have := p.A_lt; have := p.AB; have := p.m_two
  rw [hubH]
  unfold x deliveryLane z e
  change Chained ([(p.frame j).loc (p.A+1) p.A]++([(p.frame j).loc p.A p.A]++((_++_)++
    [(p.frame j).loc p.B (p.B+1),(p.frame j).loc p.B p.B])))
  have tailC : Chained [(p.frame j).loc p.B (p.B+1),(p.frame j).loc p.B p.B] := by
    apply List.isChain_cons_cons.mpr
    exact ⟨p.adjH j (by omega) (by omega) (by omega) (Or.inr rfl),List.isChain_singleton _⟩
  apply Seg.chained_append (chained_single _)
  · apply Seg.chained_append (chained_single _)
    · apply Seg.chained_append
      · apply Seg.chained_append (Seg.chained_left (p.frame j) (by omega) (by omega) (by omega))
          (Seg.chained_up (p.frame j) (by omega) (by omega) (by omega))
        intro a b ha' hb'
        rw [Seg.getLast?_mk _ _ (by omega)] at ha'
        rw [Seg.head?_mk _ _ (by omega)] at hb'
        cases ha'; cases hb'
        have e1 : p.A-1-(p.A-p.B-1-1)=p.B+1 := by omega
        rw [e1,Nat.sub_zero]
        exact p.adjV j (by omega) (by omega) (by omega) (Or.inr (by omega))
      · exact tailC
      · intro a b ha' hb'
        rw [List.getLast?_append,Seg.getLast?_mk _ _ (by omega)] at ha'
        simp only [Option.some_or,Option.some.injEq,List.head?_cons] at ha' hb'
        cases ha'; cases hb'
        have e1 : p.A-1-(p.A-p.B-1-1)=p.B+1 := by omega
        rw [e1]
        exact p.adjV j (by omega) (by omega) (by omega) (Or.inr rfl)
    · intro a b ha' hb'
      simp only [List.getLast?_singleton,Option.some.injEq] at ha'
      rw [List.head?_append,List.head?_append,Seg.head?_mk _ _ (by omega)] at hb'
      simp only [Option.some_or,Option.some.injEq] at hb'
      subst ha'; subst hb'
      rw [Nat.sub_zero]
      exact p.adjH j (by omega) (by omega) (by omega) (Or.inr (by omega))
  · intro a b ha' hb'
    simp only [List.getLast?_singleton,Option.some.injEq,List.head?_cons,List.head?_append,
      Option.some_or] at ha' hb'
    subst ha'; subst hb'
    exact p.adjV j (by omega) (by omega) (by omega) (Or.inr rfl)

theorem nodup_down {r0 c' len : Nat} (hr : r0+len≤p.N) (hc : c'<p.N) :
    (Seg.mk (fun i => (p.frame j).loc (r0+i) c') len).Nodup :=
  Seg.nodup_mk (fun i hi k hk e => by have := (p.coords j (by omega) hc (by omega) hc e).1; omega)

theorem nodup_right {r c0 len : Nat} (hr : r<p.N) (hc : c0+len≤p.N) :
    (Seg.mk (fun i => (p.frame j).loc r (c0+i)) len).Nodup :=
  Seg.nodup_mk (fun i hi k hk e => by have := (p.coords j hr (by omega) hr (by omega) e).2; omega)

theorem nodup_left {r c0 len : Nat} (hr : r<p.N) (hc : c0<p.N) (hl : len≤c0+1) :
    (Seg.mk (fun i => (p.frame j).loc r (c0-i)) len).Nodup :=
  Seg.nodup_mk (fun i hi k hk e => by have := (p.coords j hr (by omega) hr (by omega) e).2; omega)

theorem nodup_up {r0 c' len : Nat} (hr : r0<p.N) (hc : c'<p.N) (hl : len≤r0+1) :
    (Seg.mk (fun i => (p.frame j).loc (r0-i) c') len).Nodup :=
  Seg.nodup_mk (fun i hi k hk e => by have := (p.coords j (by omega) hc (by omega) hc e).1; omega)

theorem access_nodup : (p.hub w :: p.accessTail j).Nodup := by
  have := p.c_lt; have hB : p.B=p.c+1 := rfl
  rw [hubW]
  unfold accessTail x
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true,not_or]
  refine ⟨⟨fun e => ?_,fun e => ?_⟩,⟨fun e => ?_,fun e => ?_⟩⟩
  · have := (p.coords j (by omega) (by omega) (by omega) (by omega) e).1; omega
  · have := (p.coords j (by omega) (by omega) (by omega) (by omega) e).1; omega
  · have := (p.coords j (by omega) (by omega) (by omega) (by omega) e).2; omega
  · exact e

theorem exportQ_nodup : (p.exportLane j++[p.z j]).Nodup := by
  have := p.A_lt; have := p.AB; have := p.m_two
  unfold exportLane z
  rw [List.nodup_append,List.nodup_append]
  refine ⟨⟨p.nodup_down j (by omega) (by omega),p.nodup_right j (by omega) (by omega),?_⟩,
    List.nodup_singleton _,?_⟩
  · intro a ha' b hb' e
    rw [Seg.mem_down] at ha'; rw [Seg.mem_right] at hb'
    obtain ⟨r,_,_,rfl⟩ := ha'; obtain ⟨c',_,_,rfl⟩ := hb'
    have := (p.coords j (by omega) (by omega) (by omega) (by omega) e).2; omega
  · intro a ha' b hb' e
    rw [List.mem_singleton] at hb'; subst hb'
    rw [List.mem_append,Seg.mem_down,Seg.mem_right] at ha'
    rcases ha' with ⟨r,_,_,rfl⟩ | ⟨c',_,_,rfl⟩
    · have := (p.coords j (by omega) (by omega) (by omega) (by omega) e).2; omega
    · have := (p.coords j (by omega) (by omega) (by omega) (by omega) e).2; omega

theorem deliveryQ_nodup : (p.e j :: p.deliveryLane j).Nodup := by
  have := p.A_lt; have := p.AB; have := p.m_two
  unfold deliveryLane e
  rw [List.nodup_cons,List.nodup_append]
  refine ⟨?_,p.nodup_left j (by omega) (by omega) (by omega),p.nodup_up j (by omega) (by omega) (by omega),?_⟩
  · rw [List.mem_append,Seg.mem_left (p.frame j) (by omega),Seg.mem_up (p.frame j) (by omega)]
    rintro (⟨c',h1,h2,e⟩ | ⟨r,h1,h2,e⟩)
    · have := (p.coords j (by omega) (by omega) (by omega) (by omega) e).2; omega
    · have := (p.coords j (by omega) (by omega) (by omega) (by omega) e).1; omega
  · intro a ha' b hb' e
    rw [Seg.mem_left (p.frame j) (by omega)] at ha'; rw [Seg.mem_up (p.frame j) (by omega)] at hb'
    obtain ⟨c',_,_,rfl⟩ := ha'; obtain ⟨r,_,_,rfl⟩ := hb'
    have := (p.coords j (by omega) (by omega) (by omega) (by omega) e).1; omega

theorem loopP_lt {r c' : Nat} (h : p.loopP r c') : r<p.N ∧ c'<p.N := by
  have := p.loopP_range h; have := p.A_lt; omega

theorem loop_nodup :
    (loopOf (p.x j) (p.exportLane j) (p.z j) (p.e j) (p.deliveryLane j) (p.hub (H j))).Nodup := by
  have := p.A_lt; have := p.AB; have := p.m_two
  have split : loopOf (p.x j) (p.exportLane j) (p.z j) (p.e j) (p.deliveryLane j)
      (p.hub (H j))=[p.x j]++(p.exportLane j++[p.z j])++(p.e j :: p.deliveryLane j)++
        [p.hub (H j)] := by simp [loopOf]
  have expLt {r c' : Nat} (h : p.expP r c') : r<p.N ∧ c'<p.N := p.loopP_lt (Or.inr (Or.inl h))
  have delLt {r c' : Nat} (h : p.delP r c') : r<p.N ∧ c'<p.N := p.loopP_lt (Or.inr (Or.inr h))
  rw [split,hubH]
  unfold x
  rw [List.nodup_append,List.nodup_append,List.nodup_append]
  refine ⟨⟨⟨List.nodup_singleton _,p.exportQ_nodup j,?_⟩,p.deliveryQ_nodup j,?_⟩,List.nodup_singleton _,?_⟩
  · intro a ha' b hb' e
    rw [List.mem_singleton] at ha'; subst ha'
    obtain ⟨r,c',hp,rfl⟩ := (p.mem_exportQ j).mp hb'
    have := expLt hp
    have := p.coords j (by omega) (by omega) this.1 this.2 e
    unfold expP at hp; omega
  · intro a ha' b hb' e
    obtain ⟨r',c'',hp',rfl⟩ := (p.mem_deliveryQ j).mp hb'
    have l' := delLt hp'
    rw [List.mem_append,List.mem_singleton] at ha'
    rcases ha' with rfl | ha'
    · have := p.coords j (by omega) (by omega) l'.1 l'.2 e
      unfold delP at hp'; omega
    · obtain ⟨r,c',hp,rfl⟩ := (p.mem_exportQ j).mp ha'
      have l := expLt hp
      have := p.coords j l.1 l.2 l'.1 l'.2 e
      unfold expP at hp; unfold delP at hp'; omega
  · intro a ha' b hb' e
    rw [List.mem_singleton] at hb'; subst hb'
    rw [List.mem_append,List.mem_append,List.mem_singleton] at ha'
    rcases ha' with (rfl | ha') | ha'
    · have := p.coords j (by omega) (by omega) (by omega) (by omega) e; omega
    · obtain ⟨r,c',hp,rfl⟩ := (p.mem_exportQ j).mp ha'
      have l := expLt hp
      have := p.coords j l.1 l.2 (by omega) (by omega) e
      unfold expP at hp; omega
    · obtain ⟨r,c',hp,rfl⟩ := (p.mem_deliveryQ j).mp ha'
      have l := delLt hp
      have := p.coords j l.1 l.2 (by omega) (by omega) e
      unfold delP at hp; omega

/-! ### The layout -/

variable [NeZero n] (Q : Fin 4 → Region n)
  (hcells : ∀ j y, y∈(Q j).cells → ∃ r c', p.A+p.W≤r ∧ r<p.N ∧ p.A≤c' ∧ c'<p.N ∧ (p.frame j).loc r c'=y)
  (hentry : ∀ j, (Q j).Entry (p.e j) (p.z j))

theorem B_le_A : p.B+2≤p.A := by have := p.AB; have := p.m_two; omega

theorem mid_hub {y : Cell 7} (hy : y.1.val=2) {r c' : Nat} (hr : p.B≤r) (hr2 : r<p.N) (hc2 : c'<p.N) :
    p.hub y≠(p.frame j).loc r c' := by
  have h := p.hub_loc y.1.val y.2.val y.1.isLt y.2.isLt
  have : hcell y.1.val y.2.val y.1.isLt y.2.isLt=y := rfl
  rw [this,hy,show p.c-2+2=p.c by have := p.two_le_c; omega] at h
  rw [h]
  exact (p.mid_ne j (r:=r) (c':=c') (c0:=p.c-2+y.2.val) (by unfold B at hr; omega) hr2 hc2
    (by have := p.c_lt; have := y.2.isLt; omega)).symm

include hcells hentry in
def geom : StarGeom n 4 Q where
  h := 7
  hub := p.hub
  hub_adj := by intro a b h; unfold hub; rw [Placement.distance]; exact h
  hub_side := by omega
  K := K
  u := u
  v := v
  w := w
  K_u := by simp [K,u,hcell]
  K_v := by simp [K,v,hcell]
  u_v := by simp [u,v,hcell]
  w_K := by simp [w,K,hcell]
  w_u := by simp [w,u,hcell]
  w_v := by simp [w,v,hcell]
  H := H
  H_K := fun j h => by simp only [H,K,hcell,Prod.mk.injEq,Fin.mk.injEq] at h; split_ifs at h <;> omega
  H_u := fun j h => by simp only [H,u,hcell,Prod.mk.injEq,Fin.mk.injEq] at h; split_ifs at h <;> omega
  H_v := fun j h => by simp only [H,v,hcell,Prod.mk.injEq,Fin.mk.injEq] at h; split_ifs at h <;> omega
  H_w := fun j h => by simp only [H,w,hcell,Prod.mk.injEq,Fin.mk.injEq] at h; split_ifs at h <;> omega
  H_inj := by
    intro j j' h
    simp only [H,hcell,Prod.mk.injEq,Fin.mk.injEq] at h
    apply fr_fc_inj
    · cases hx : fr j <;> cases hy : fr j' <;> simp_all
    · cases hx : fc j <;> cases hy : fc j' <;> simp_all
  accessTail := p.accessTail
  x := p.x
  exportLane := p.exportLane
  z := p.z
  e := p.e
  deliveryLane := p.deliveryLane
  access_last := by intro j; simp [accessTail]
  access_chain := p.access_chain
  out_chain := p.out_chain
  back_chain := p.back_chain
  access_nodup := p.access_nodup
  loop_nodup := p.loop_nodup
  access_loop := by
    intro j y hy hl
    obtain ⟨r,c',hp,rfl⟩ := (p.mem_loop j).mp hl
    have l := p.loopP_range hp; have := p.A_lt; have := p.c_lt; have hB : p.B=p.c+1 := rfl
    rw [List.mem_cons,p.mem_access,hubW p j] at hy
    rcases hy with e | e | e
    · have := (p.coords j (by omega) (by omega) (by omega) (by omega) e).1; omega
    · have := (p.coords j (by omega) (by omega) (by omega) (by omega) e).2; omega
    · exact e
  hub_access := by
    intro j
    have := p.c_lt; have hB : p.B=p.c+1 := rfl
    have hk (y : Cell 7) (hy : y.1.val=2) (hw : y≠w) : p.hub y∉p.hub w :: p.accessTail j := by
      rw [List.mem_cons,p.mem_access]
      rintro (e | e | e)
      · exact hw (p.hub.injective e)
      · exact p.mid_hub j hy (le_refl _) (by omega) (by omega) e
      · exact p.mid_hub j hy (le_refl _) (by omega) (by omega) e
    exact ⟨hk K rfl (by simp [K,w,hcell]),hk u rfl (by simp [u,w,hcell]),hk v rfl (by simp [v,w,hcell])⟩
  hub_loop := by
    intro j
    have hk (y : Cell 7) (hy : y.1.val=2) :
        p.hub y∉loopOf (p.x j) (p.exportLane j) (p.z j) (p.e j) (p.deliveryLane j) (p.hub (H j)) := by
      rw [p.mem_loop]
      rintro ⟨r,c',hp,e⟩
      have l := p.loopP_range hp; have := p.A_lt
      exact p.mid_hub j hy l.1 (by omega) (by omega) e.symm
    exact ⟨hk K rfl,hk u rfl,hk v rfl⟩
  entry := hentry
  loop_child := by
    intro j j' y hl hy
    obtain ⟨r,c',hp,rfl⟩ := (p.mem_loop j).mp hl
    obtain ⟨r',c'',h1,h2,h3,h4,e⟩ := hcells j' _ hy
    have l := p.loopP_range hp; have := p.A_lt; have := p.B_le_A; have := p.W_two
    by_cases hj : j=j'
    · subst hj
      have := (p.coords j (by omega) (by omega) h2 h4 e.symm).1; omega
    · exact p.sep hj (by unfold B at l; omega) (by omega) (by unfold B at l; omega) (by omega)
        (by unfold B at *; omega) h2 (by unfold B at *; omega) h4 e.symm
  access_child := by
    intro j y hy hc
    obtain ⟨r',c'',h1,h2,h3,h4,e⟩ := hcells j _ hc
    have := p.A_lt; have := p.B_le_A; have := p.c_lt; have hB : p.B=p.c+1 := rfl; have := p.W_two
    rw [List.mem_cons,p.mem_access,hubW p j] at hy
    rcases hy with rfl | rfl | rfl
    · have := (p.coords j (by omega) (by omega) h2 h4 e.symm).1; omega
    · have := (p.coords j (by omega) (by omega) h2 h4 e.symm).1; omega
    · have := (p.coords j (by omega) (by omega) h2 h4 e.symm).1; omega
  hub_child := by
    intro j
    have hk (y : Cell 7) (hy : y.1.val=2) : p.hub y∉(Q j).cells := by
      intro hc
      obtain ⟨r',c'',h1,h2,h3,h4,e⟩ := hcells j _ hc
      have := p.B_le_A
      exact p.mid_hub j hy (by omega) h2 h4 e.symm
    exact ⟨hk K rfl,hk u rfl,hk v rfl⟩
  children_disjoint := by
    intro j j' hj
    rw [Finset.disjoint_left]
    intro y hy hy'
    obtain ⟨r,c',h1,h2,h3,h4,e⟩ := hcells j _ hy
    obtain ⟨r',c'',h1',h2',h3',h4',e'⟩ := hcells j' _ hy'
    have := p.B_le_A; have hB : p.B=p.c+1 := rfl
    exact p.sep hj (by omega) h2 (by omega) h4 (by omega) h2' (by omega) h4' (e.trans e'.symm)
  loops_disjoint := by
    intro j j' hj y hl hl'
    obtain ⟨r,c',hp,rfl⟩ := (p.mem_loop j).mp hl
    obtain ⟨r',c'',hp',e⟩ := (p.mem_loop j').mp hl'
    have l := p.loopP_range hp; have l' := p.loopP_range hp'; have := p.A_lt; have hB : p.B=p.c+1 := rfl
    exact p.sep hj (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) e.symm


/-! ### The hub exchange by `t`-cycles

The carrier `K = (c, c+1)` and the blank's cell `w = (c, c)` form a block.
For a spoke whose hub cell lies left (`fc`), a frame runs left from `K`, and
the third cell is `(c, c-3)`; otherwise the blank first steps onto `K`, a
frame runs right from `w`, and the third cell is `u = (c, c+2)`. -/

theorem q0_cc {r c' : Nat} (hr : r<p.N) (hc : c'<p.N) : p.q0.loc r c'=cc r c' := by
  have := p.N_le
  have b := cc_val (n:=n) (r:=r) (c:=c') (by unfold N at hr; omega) (by unfold N at hc; omega)
  exact cell_eq ((p.q0_row hr hc).trans b.1.symm) ((p.q0_col hr hc).trans b.2.symm)

theorem hub_cc (r c' : Nat) (hr : r<7) (hc : c'<7) : p.hub (hcell r c' hr hc)=cc (p.c-2+r) (p.c-2+c') := by
  rw [hub_loc]; have := p.c_lt; have := p.two_le_c; exact p.q0_cc (by omega) (by omega)

/-- The third cell of the hub exchange of spoke `j`. -/
def hcR : Cell n := if fc j then p.q0.loc p.c (p.c-3) else p.hub u

open Routes in
theorem root_hX (B : Board n) (hB : blank B=p.hub w) (plus : Bool) :
    ∃ C : Board n, ∃ path : Path B C, path.length≤190 ∧ blank C=p.hub w ∧
      (if plus then Cycle3.IsCycle B C (p.hub (H j)) (p.hub K) (p.hcR j)
        else Cycle3.IsCycle B C (p.hub K) (p.hub (H j)) (p.hcR j)) := by
  have hcl := p.c_lt; have h2 := p.two_le_c; have hN := p.N_le
  have hTb := p.T_big; have hm := p.m_two
  have h14 : 14≤p.c := by unfold c; omega
  have hNn : 2*p.c+1≤n := by unfold N c at *; omega
  have ew : p.hub w=cc p.c p.c := by rw [show w=hcell 2 2 (by omega) (by omega) from rfl,hub_cc]; congr 1 <;> omega
  have eK : p.hub K=cc p.c (p.c+1) := by
    rw [show K=hcell 2 3 (by omega) (by omega) from rfl,hub_cc]; congr 1 <;> omega
  have eu : p.hub u=cc p.c (p.c+2) := by
    rw [show u=hcell 2 4 (by omega) (by omega) from rfl,hub_cc]; congr 1 <;> omega
  have eH : p.hub (H j)=cc (if fr j then p.c-1 else p.c+1) (if fc j then p.c-2 else p.c+2) := by
    unfold H; rw [hub_cc]; congr 1 <;> split_ifs <;> omega
  have tw31 : Cycle3.tw 3 1=56 := rfl
  have tw40 : Cycle3.tw 4 0=64 := rfl
  have tw21 : Cycle3.tw 2 1=44 := rfl
  have tw20 : Cycle3.tw 2 0=40 := rfl
  cases hfc : fc j
  · -- the hub cell lies right: the blank steps onto `K` first
    have eh : p.hcR j=cc p.c (p.c+2) := by unfold hcR; rw [hfc]; exact eu
    rw [hfc] at eH; simp only [Bool.false_eq_true,if_false] at eH
    have adj : gridDistance (p.hub w) (p.hub K)=1 := by
      rw [ew,eK]; unfold cc
      rw [(CParams.boardP (n:=n)).loc_dist (by omega) (by omega) (by omega) (by omega)]
      simp [Nat.dist]
    obtain ⟨C1,P1,l1,b1,s1,f1⟩ := Cycle3.move B (p.hub w) (p.hub K) hB adj
    let F := hframe (n:=n) p.c p.c 3 6 (fr j) false (by omega) (by omega) (fun h => by cases h)
      (fun _ => by omega) (fun _ => by omega) (fun _ => by omega)
    have Floc (i j' : Nat) : F.loc i j'=cc (ax (fr j) p.c j') (p.c+i) := by
      show cc (ax (fr j) p.c j') (ax false p.c i)=_; simp [ax]
    have e00 : F.loc 0 0=p.hub w := by rw [Floc,ew]; simp [ax]
    have e10 : F.loc 1 0=p.hub K := by rw [Floc,eK]; simp [ax]
    have e20 : F.loc 2 0=p.hcR j := by rw [Floc,eh]; simp [ax]
    have e21 : F.loc 2 1=p.hub (H j) := by
      rw [Floc,eH]; cases fr j <;> simp [ax]
    have ne : F.loc 2 0≠F.loc 2 1 := ne_loc F (by change 2<3; omega) (by change 0<6; omega)
      (by change 2<3; omega) (by change 1<6; omega) (by omega)
    have hw0 (x : Cell n) (hx : x≠p.hub w) (hxK : x≠p.hub K) : B.symm (C1 x)=x := by rw [f1 x hx hxK]; simp
    have hrow : (if fr j=true then p.c-1 else p.c+1)<n ∧ (if fr j=true then p.c-1 else p.c+1)≠p.c := by
      split_ifs <;> omega
    have nwK (x : Cell n) (hx : x=p.hcR j ∨ x=p.hub (H j)) : x≠p.hub w ∧ x≠p.hub K := by
      rcases hx with rfl | rfl
      · rw [eh,ew,eK]; exact ⟨cc_ne (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega)),
          cc_ne (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega))⟩
      · rw [eH,ew,eK]; exact ⟨cc_ne hrow.1 (by omega) (by omega) (by omega) (Or.inl hrow.2),
          cc_ne hrow.1 (by omega) (by omega) (by omega) (Or.inl hrow.2)⟩
    have kw : B.symm (C1 (p.hub w))=p.hub K := by rw [s1]; simp
    cases plus
    · obtain ⟨E,Q,lQ,bE,cyc⟩ := Cycle3.tdirect_at2 F F (by change 3≤3; omega) (by change 6≤6; omega)
        (by change 3≤3; omega) (by change 6≤6; omega) (fun _ _ _ _ => rfl) C1 (by rw [e10]; exact b1)
        2 1 (by change 2<3; omega) (by change 1<6; omega) (Or.inl (by omega))
        2 0 (by change 2<3; omega) (by change 0<6; omega) (Or.inl (by omega)) (Ne.symm ne)
      rw [e00,e20,e21] at cyc
      obtain ⟨E',R',lR,bR,cR⟩ := Cycle3.conj P1 Q (by rw [bE,e10,b1]) cyc
      rw [kw,hw0 _ (nwK _ (Or.inr rfl)).1 (nwK _ (Or.inr rfl)).2,
        hw0 _ (nwK _ (Or.inl rfl)).1 (nwK _ (Or.inl rfl)).2] at cR
      exact ⟨E',R',by omega,bR.trans hB,cR⟩
    · obtain ⟨E,Q,lQ,bE,cyc⟩ := Cycle3.tdirect_at2 F F (by change 3≤3; omega) (by change 6≤6; omega)
        (by change 3≤3; omega) (by change 6≤6; omega) (fun _ _ _ _ => rfl) C1 (by rw [e10]; exact b1)
        2 0 (by change 2<3; omega) (by change 0<6; omega) (Or.inl (by omega))
        2 1 (by change 2<3; omega) (by change 1<6; omega) (Or.inl (by omega)) ne
      rw [e00,e20,e21] at cyc
      obtain ⟨E',R',lR,bR,cR⟩ := Cycle3.conj P1 Q (by rw [bE,e10,b1]) cyc
      rw [kw,hw0 _ (nwK _ (Or.inr rfl)).1 (nwK _ (Or.inr rfl)).2,
        hw0 _ (nwK _ (Or.inl rfl)).1 (nwK _ (Or.inl rfl)).2] at cR
      exact ⟨E',R',by omega,bR.trans hB,cR.rotate.rotate⟩
  · -- the hub cell lies left: a frame runs left from `K`
    have eh : p.hcR j=cc p.c (p.c-3) := by unfold hcR; rw [hfc]; exact p.q0_cc (by omega) (by omega)
    rw [hfc] at eH; simp only [if_true] at eH
    let F := hframe (n:=n) p.c (p.c+1) 5 6 (fr j) true (by omega) (by omega) (fun _ => by omega)
      (fun h => by cases h) (fun _ => by omega) (fun _ => by omega)
    have Floc (i j' : Nat) : F.loc i j'=cc (ax (fr j) p.c j') (p.c+1-i) := by
      show cc (ax (fr j) p.c j') (ax true (p.c+1) i)=_; simp [ax]
    have e00 : F.loc 0 0=p.hub K := by rw [Floc,eK]; simp [ax]
    have e10 : F.loc 1 0=p.hub w := by rw [Floc,ew]; simp [ax]
    have e40 : F.loc 4 0=p.hcR j := by
      rw [Floc,eh]; cases fr j <;> simp only [ax,if_true,if_false,Bool.false_eq_true] <;> congr 1
    have e31 : F.loc 3 1=p.hub (H j) := by
      rw [Floc,eH]; cases fr j <;> simp only [ax,if_true,if_false,Bool.false_eq_true] <;> congr 1
    have ne : F.loc 4 0≠F.loc 3 1 := ne_loc F (by change 4<5; omega) (by change 0<6; omega)
      (by change 3<5; omega) (by change 1<6; omega) (by omega)
    cases plus
    · obtain ⟨C,P,lP,bC,cyc⟩ := Cycle3.tdirect_at2 F F (by change 3≤5; omega) (by change 6≤6; omega)
        (by change 3≤5; omega) (by change 6≤6; omega) (fun _ _ _ _ => rfl) B (by rw [e10]; exact hB)
        3 1 (by change 3<5; omega) (by change 1<6; omega) (Or.inl (by omega))
        4 0 (by change 4<5; omega) (by change 0<6; omega) (Or.inl (by omega)) (Ne.symm ne)
      rw [e00,e31,e40] at cyc
      exact ⟨C,P,by omega,by rw [bC,e10],cyc⟩
    · obtain ⟨C,P,lP,bC,cyc⟩ := Cycle3.tdirect_at2 F F (by change 3≤5; omega) (by change 6≤6; omega)
        (by change 3≤5; omega) (by change 6≤6; omega) (fun _ _ _ _ => rfl) B (by rw [e10]; exact hB)
        4 0 (by change 4<5; omega) (by change 0<6; omega) (Or.inl (by omega))
        3 1 (by change 3<5; omega) (by change 1<6; omega) (Or.inl (by omega)) ne
      rw [e00,e31,e40] at cyc
      exact ⟨C,P,by omega,by rw [bC,e10],cyc.rotate.rotate⟩

include hcells hentry in
/-- The root layout: the default geometry with the hub exchange by `t`-cycles. -/
def layout : StarLayout n 4 Q :=
  { (p.geom Q hcells hentry).square with
    hc := p.hcR
    hcost := fun _ => 190
    hX := fun j B hB => p.root_hX j B hB true
    hX' := fun j B hB => p.root_hX j B hB false
    hc_access := by
      intro j
      by_cases hf : fc j
      · have : p.hcR j=p.q0.loc p.c (p.c-3) := by unfold hcR; rw [if_pos hf]
        rw [this]
        have := p.c_lt; have h2 := p.two_le_c; have hB : p.B=p.c+1 := rfl
        have h14 : 3≤p.c := by have := p.T_big; unfold c; omega
        change _∉p.hub w :: p.accessTail j
        rw [List.mem_cons,p.mem_access]
        rintro (e | e | e)
        · have ew : p.hub w=p.q0.loc p.c p.c := by
            rw [show w=hcell 2 2 (by omega) (by omega) from rfl,hub_loc]; congr 1 <;> omega
          rw [ew] at e
          have := (p.q0.loc_inj (by omega) (by omega) (by omega) (by omega) e).2; omega
        · exact p.mid_ne j (le_refl _) (by omega) (by omega) (c0:=p.c-3) (by omega) e.symm
        · exact p.mid_ne j (le_refl _) (by omega) (by omega) (c0:=p.c-3) (by omega) e.symm
      · have : p.hcR j=p.hub u := by unfold hcR; rw [if_neg hf]
        rw [this]; exact ((p.geom Q hcells hentry).hub_access j).2.1
    hc_loop := by
      intro j
      by_cases hf : fc j
      · have : p.hcR j=p.q0.loc p.c (p.c-3) := by unfold hcR; rw [if_pos hf]
        rw [this]
        have := p.c_lt; have := p.A_lt
        have h14 : 3≤p.c := by have := p.T_big; unfold c; omega
        intro hl
        obtain ⟨r,c',hp,e⟩ := (p.mem_loop j).mp hl
        have l := p.loopP_range hp
        exact p.mid_ne j l.1 (by omega) (by omega) (c0:=p.c-3) (by omega) e
      · have : p.hcR j=p.hub u := by unfold hcR; rw [if_neg hf]
        rw [this]; exact ((p.geom Q hcells hentry).hub_loop j).2.1
    hc_child := by
      intro j
      by_cases hf : fc j
      · have : p.hcR j=p.q0.loc p.c (p.c-3) := by unfold hcR; rw [if_pos hf]
        rw [this]
        have := p.c_lt; have := p.B_le_A; have hB : p.B=p.c+1 := rfl
        have h14 : 3≤p.c := by have := p.T_big; unfold c; omega
        intro hc
        obtain ⟨r',c'',h1,h2,h3,h4,e⟩ := hcells j _ hc
        exact p.mid_ne j (by omega) h2 h4 (c0:=p.c-3) (by omega) e
      · have : p.hcR j=p.hub u := by unfold hcR; rw [if_neg hf]
        rw [this]; exact ((p.geom Q hcells hentry).hub_child j).2.1
    hc_K := by
      intro j
      by_cases hf : fc j
      · have : p.hcR j=p.q0.loc p.c (p.c-3) := by unfold hcR; rw [if_pos hf]
        rw [this]
        have := p.c_lt
        have h14 : 3≤p.c := by have := p.T_big; unfold c; omega
        change _≠p.hub K
        rw [hubK]; intro e
        have := (p.q0.loc_inj (by omega) (by omega) (by omega) (by omega) e).2; omega
      · have : p.hcR j=p.hub u := by unfold hcR; rw [if_neg hf]
        rw [this]; intro e; exact (p.geom Q hcells hentry).K_u (p.hub.injective e).symm }

end CParams
end SlidingPuzzle.NestedRouting.Central
