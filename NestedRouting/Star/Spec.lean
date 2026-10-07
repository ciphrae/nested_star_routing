import NestedRouting.Star.Service
import NestedRouting.Star.Ledger
import NestedRouting.Moves.GoalCompletion

/-! The static data of a star node P over children `Q j`, and the frame it
presents to its own parent. P's homes for core goals are the children's
homes; its reserve homes are its own cells (lanes, hub, children's strips,
remainders) together with the children's spare cells; its spare cells are
its markers. P is entered through the single pair `(eP, zP)`. -/
namespace SlidingPuzzle.NestedRouting.Interface
open Finset TileRoles

variable {n : Nat} [NeZero n]

structure StarBase (n J : Nat) [NeZero n] where
  Q : Fin J → Region n
  L : StarLayout n J Q
  goal : Board n
  goal_child : ∀ j, (Q j).goal=goal
  own : Finset (Cell n)
  markers : Finset (Cell n)
  eP : Cell n
  zP : Cell n
  own_child : ∀ j, Disjoint own (Q j).cells
  markers_child : ∀ j, Disjoint markers (Q j).cells
  own_markers : Disjoint own markers
  eP_zP : eP≠zP
  eP_own : eP∉own
  eP_markers : eP∉markers
  eP_child : ∀ j, eP∉(Q j).cells
  zP_own : zP∉own
  zP_markers : zP∉markers
  zP_child : ∀ j, zP∉(Q j).cells
  loop_own : ∀ j c, c∈L.loop j → c∈own
  K_own : L.hub L.K∈own
  strip_own : ∀ j, (Q j).strip⊆own
  goal_own : ∀ x∈own, goal x≠0
  goal_spare : ∀ j, ∀ x∈(Q j).spareCells, goal x≠0
  /-- The connector walk from `zP` to the hub park cell. -/
  connTail : List (Cell n)
  conn_last : (zP :: connTail).getLast (List.cons_ne_nil _ _)=L.hub L.w
  conn_chain : Chained (zP :: connTail)
  conn_nodup : (zP :: connTail).Nodup
  /-- It avoids lanes, children and the carrier, which services change. -/
  conn_free : ∀ c∈zP :: connTail, (∀ j, c∉L.exportQ j ∧ c∉L.deliveryQ j ∧ c∉(Q j).cells) ∧
    c≠L.hub L.K
  conn_eP : eP∉zP :: connTail
  conn_u : L.hub L.u∉zP :: connTail
  conn_v : L.hub L.v∉zP :: connTail
  u_own : L.hub L.u∈own
  v_own : L.hub L.v∈own
  /-- The wrapper square: input, blank cell, carrier and parity cells. -/
  wm : Nat
  wι : Cell wm ↪ Cell n
  w_adj : ∀ a b, gridDistance a b=1 → gridDistance (wι a) (wι b)=1
  w_side : 6≤wm
  w_eP : eP∈Set.range wι
  w_zP : zP∈Set.range wι
  w_K : L.hub L.K∈Set.range wι
  w_u : L.hub L.u∈Set.range wι
  w_v : L.hub L.v∈Set.range wι
  /-- A third parity cell, for direct exchanges. -/
  u2 : Cell L.h
  u2_own : L.hub u2∈own
  u2_u : u2≠L.u
  u2_v : u2≠L.v
  u2_K : u2≠L.K
  u2_loop : ∀ j, L.hub u2∉L.loop j
  u2_child : ∀ j, L.hub u2∉(Q j).cells
  /-- The whole square, for direct exchanges anywhere in P. -/
  pm : Nat
  pι : Cell pm ↪ Cell n
  p_adj : ∀ a b, gridDistance a b=1 → gridDistance (pι a) (pι b)=1
  p_side : 6≤pm
  p_eP : eP∈Set.range pι
  p_zP : zP∈Set.range pι
  p_own : ∀ x∈own, x∈Set.range pι
  p_markers : ∀ x∈markers, x∈Set.range pι
  p_child : ∀ j, ∀ x∈(Q j).cells, x∈Set.range pι
  six : 6≤markers.card
  /-- The walk to a child's blank cell meets that child's strip only there. -/
  strip_walk : ∀ j c, (c∈L.hub L.w :: L.accessTail j ∨ c∈L.x j :: L.exportQ j) → c∈(Q j).strip → c=L.z j
  conn_strip : ∀ c∈zP :: connTail, ∀ j, c∉(Q j).strip
  /-- A bound `H_J ≤ hp/hq` on the harmonic number, in the floor form the ledger uses. -/
  hp : Nat
  hq : Nat
  hq_pos : 0<hq
  harm : ∀ B : Nat, hq*∑ t ∈ Finset.Ioc 0 J, B/t≤hp*B
  /-- Service costs split as `cb + lw1·ρ1 j + lw2·ρ2 j`; the layered harmonic
  bounds `layered ρ ≤ wp/hq` weigh each part by the spokes' own weights. -/
  lw1 : Nat
  lw2 : Nat
  ρ1 : Fin J → Nat
  ρ2 : Fin J → Nat
  wp1 : Nat
  wp2 : Nat
  wharm1 : ∀ B : Nat, hq*Ledger.layered ρ1 B≤wp1*B
  wharm2 : ∀ B : Nat, hq*Ledger.layered ρ2 B≤wp2*B

/-- A star node with its two exchanges at the entry, the blank on `zP`
before and after:
* the wrapper cycle of the carrier, `eP` and a third cell `wc`, both ways;
* the direct exchange of `eP` with any cell `q` of P, through a parking cell
  `p₁ ≠ q`. -/
structure StarSpec (n J : Nat) [NeZero n] extends StarBase n J where
  wc : Cell n
  wcost : Nat
  wX : ∀ B : Board n, blank B=zP → ∃ C : Board n, ∃ p : Path B C,
    p.length≤wcost ∧ blank C=zP ∧ Cycle3.IsCycle B C (L.hub L.K) eP wc
  wX' : ∀ B : Board n, blank B=zP → ∃ C : Board n, ∃ p : Path B C,
    p.length≤wcost ∧ blank C=zP ∧ Cycle3.IsCycle B C eP (L.hub L.K) wc
  wc_conn : wc∉zP :: connTail
  wc_loop : ∀ j, wc∉L.loop j
  wc_child : ∀ j, wc∉(Q j).cells
  wc_K : wc≠L.hub L.K
  park : Cell n → Prop
  dcost : Nat
  dX : ∀ (B : Board n) (q : Cell n), blank B=zP → ((∃ j, q∈(Q j).cells) ∨ q∈own ∨ q∈markers) →
    ∃ C : Board n, ∃ path : Path B C, ∃ p1 : Cell n, park p1 ∧ p1≠q ∧ blank C=zP ∧
      C eP=B q ∧ C q=B p1 ∧ C p1=B eP ∧
      (∀ y, y≠eP → y≠q → y≠p1 → C y=B y) ∧ path.length≤dcost
  park_own : ∀ c, park c → c∈own
  park_loop : ∀ c, park c → ∀ j, c∉L.loop j
  park_child : ∀ c, park c → ∀ j, c∉(Q j).cells
  park_K : ∀ c, park c → c≠L.hub L.K
  /-- The final sort: place goal tiles `T` on `F ⊆ R` for a set `R` of cells
  of P, keeping everything off `R`, at twice the weights `fw` of `R`. -/
  fw : Cell n → Nat
  fsort : ∀ (B T : Board n) (R F : Finset (Cell n)), blank B=zP →
    (∀ x∈R, (∃ j, x∈(Q j).cells) ∨ x∈own ∨ x∈markers) →
    (∀ x∈R, ∀ j, x∉(Q j).coreCells ∧ x∉(Q j).reserveCells) → F⊆R → (∀ x∈F, T x≠0) →
    (∀ x∈F, ∃ y∈R, B y=T x) → F.card+3≤R.card →
    ∃ C : Board n, ∃ path : Path B C, path.length≤2*∑ x∈R, fw x ∧ blank C=blank B ∧
      (∀ x, x∉R → C x=B x) ∧ ∀ x∈F, C x=T x
  /-- Static cells: own cells no service, wrapper or parking touches. A reserve
  source still on one is exported by a direct exchange charged by position. -/
  stat : Finset (Cell n)
  stat_own : ∀ x∈stat, x∈own
  stat_loop : ∀ x∈stat, ∀ j, x∉L.loop j
  stat_K : ∀ x∈stat, x≠L.hub L.K
  stat_park : ∀ x∈stat, ¬park x
  dw : Cell n → Nat
  dXw : ∀ (B : Board n) (q : Cell n), blank B=zP → q∈stat →
    ∃ C : Board n, ∃ path : Path B C, ∃ p1 : Cell n, park p1 ∧ p1≠q ∧ blank C=zP ∧
      C eP=B q ∧ C q=B p1 ∧ C p1=B eP ∧
      (∀ y, y≠eP → y≠q → y≠p1 → C y=B y) ∧ path.length≤dw q

namespace StarBase
variable {J : Nat} (S : StarBase n J)

theorem own_ne {x y : Cell n} (hx : x∈S.own) (hy : y∉S.own) : x≠y := fun e => hy (e ▸ hx)

/-- The default wrapper cycle, in the wrapper square with `u` as third cell. -/
theorem square_wX (B : Board n) (hB : blank B=S.zP) : ∃ C : Board n, ∃ p : Path B C,
    p.length≤54*S.wm ∧ blank C=S.zP ∧ Cycle3.IsCycle B C (S.L.hub S.L.K) S.eP (S.L.hub S.L.u) :=
  range_cycle S.wι S.w_adj S.w_side S.w_K S.w_eP S.w_u S.w_zP (S.own_ne S.K_own S.eP_own)
    (fun e => S.L.K_u (S.L.hub.injective e)) (S.own_ne S.u_own S.eP_own).symm
    (S.own_ne S.K_own S.zP_own).symm S.eP_zP.symm (S.own_ne S.u_own S.zP_own).symm B hB

theorem square_wX' (B : Board n) (hB : blank B=S.zP) : ∃ C : Board n, ∃ p : Path B C,
    p.length≤54*S.wm ∧ blank C=S.zP ∧ Cycle3.IsCycle B C S.eP (S.L.hub S.L.K) (S.L.hub S.L.u) :=
  range_cycle S.wι S.w_adj S.w_side S.w_eP S.w_K S.w_u S.w_zP (S.own_ne S.K_own S.eP_own).symm
    (S.own_ne S.u_own S.eP_own).symm (fun e => S.L.K_u (S.L.hub.injective e))
    S.eP_zP.symm (S.own_ne S.K_own S.zP_own).symm (S.own_ne S.u_own S.zP_own).symm B hB

/-- The default parking cells: the hub cells `u`, `v`, `u2`. -/
def parity (c : Cell n) : Prop :=
  c=S.L.hub S.L.u ∨ c=S.L.hub S.L.v ∨ c=S.L.hub S.u2

theorem parity_own {c : Cell n} (hc : S.parity c) : c∈S.own := by
  rcases hc with rfl | rfl | rfl
  · exact S.u_own
  · exact S.v_own
  · exact S.u2_own

/-- The default direct exchange: one three-cycle `(eP q p₁)` in the whole
square, parking on `u`, or on `v` when `q = u`. -/
theorem square_dX (B : Board n) (q : Cell n) (atZ : blank B=S.zP)
    (hq : (∃ j, q∈(S.Q j).cells) ∨ q∈S.own ∨ q∈S.markers) :
    ∃ C : Board n, ∃ path : Path B C, ∃ p1 : Cell n, S.parity p1 ∧ p1≠q ∧ blank C=S.zP ∧
      C S.eP=B q ∧ C q=B p1 ∧ C p1=B S.eP ∧
      (∀ y, y≠S.eP → y≠q → y≠p1 → C y=B y) ∧ path.length≤54*S.pm := by
  have hu : S.L.hub S.L.u≠S.L.hub S.L.v := fun e => S.L.u_v (S.L.hub.injective e)
  obtain ⟨p1,h1,n1⟩ : ∃ p1 : Cell n, S.parity p1 ∧ p1≠q := by
    by_cases hqu : q=S.L.hub S.L.u
    · exact ⟨_,Or.inr (Or.inl rfl),fun e => hu (hqu ▸ e).symm⟩
    · exact ⟨_,Or.inl rfl,fun e => hqu e.symm⟩
  have qr : q∈Set.range S.pι := by
    rcases hq with ⟨j,hj⟩ | hq | hq
    · exact S.p_child j q hj
    · exact S.p_own q hq
    · exact S.p_markers q hq
  have eq : S.eP≠q := by
    rintro rfl
    rcases hq with ⟨j,hj⟩ | hq | hq
    · exact S.eP_child j hj
    · exact S.eP_own hq
    · exact S.eP_markers hq
  have zq : S.zP≠q := by
    rintro rfl
    rcases hq with ⟨j,hj⟩ | hq | hq
    · exact S.zP_child j hj
    · exact S.zP_own hq
    · exact S.zP_markers hq
  have po := S.parity_own h1
  obtain ⟨C,path,len,blankC,se,sq,s1,fix⟩ :=
    range_cycle S.pι S.p_adj S.p_side S.p_eP qr (S.p_own p1 po) S.p_zP eq
      (S.own_ne po S.eP_own).symm n1.symm S.eP_zP.symm zq (S.own_ne po S.zP_own).symm B atZ
  exact ⟨C,path,p1,h1,n1,blankC,se,sq,s1,fix,len⟩

/-- The default final sort, by three-cycles in the whole square. -/
theorem square_fsort (B T : Board n) (R F : Finset (Cell n)) (atZ : blank B=S.zP)
    (hR : ∀ x∈R, (∃ j, x∈(S.Q j).cells) ∨ x∈S.own ∨ x∈S.markers) (inside : F⊆R)
    (hnonzero : ∀ x∈F, T x≠0) (hpresent : ∀ x∈F, ∃ y∈R, B y=T x) (room : F.card+3≤R.card) :
    ∃ C : Board n, ∃ path : Path B C, path.length≤2*∑ _x∈R, 27*S.pm ∧ blank C=blank B ∧
      (∀ x, x∉R → C x=B x) ∧ ∀ x∈F, C x=T x := by
  classical
  rw [sum_const,smul_eq_mul]
  have : NeZero S.pm := ⟨by have := S.p_side; omega⟩
  have inRange {x : Cell n} (hx : x∈R) : x∈Set.range S.pι := by
    rcases hR x hx with ⟨j,hj⟩ | h | h
    · exact S.p_child j x hj
    · exact S.p_own x h
    · exact S.p_markers x h
  set R' : Finset (Cell S.pm) := univ.filter (fun a => S.pι a∈R)
  set F' : Finset (Cell S.pm) := univ.filter (fun a => S.pι a∈F)
  have mapR : R'.map S.pι=R := by
    ext x; constructor
    · intro hx; obtain ⟨a,ha,rfl⟩ := mem_map.mp hx; simpa [R'] using ha
    · intro hx; obtain ⟨a,rfl⟩ := inRange hx; exact mem_map_of_mem _ (by simpa [R'] using hx)
  have mapF : F'.map S.pι=F := by
    ext x; constructor
    · intro hx; obtain ⟨a,ha,rfl⟩ := mem_map.mp hx; simpa [F'] using ha
    · intro hx; obtain ⟨a,rfl⟩ := inRange (inside hx); exact mem_map_of_mem _ (by simpa [F'] using hx)
  have cR : R'.card=R.card := by rw [←mapR,card_map]
  have cF : F'.card=F.card := by rw [←mapF,card_map]
  have zR : S.zP∉R := by
    intro h
    rcases hR _ h with ⟨j,hj⟩ | h | h
    · exact S.zP_child j hj
    · exact S.zP_own h
    · exact S.zP_markers h
  obtain ⟨C,path,len,blankC,outside,placed⟩ :=
    LocalBlockFinish.exists_finish_supported_real_goals S.pι S.p_adj B T S.p_side (atZ ▸ S.p_zP) R' F'
      (fun a ha => by simp only [R',F',mem_filter,mem_univ,true_and] at ha ⊢; exact inside ha)
      (fun a ha e => by simp only [F',mem_filter,mem_univ,true_and] at ha; exact zR (atZ ▸ e ▸ inside ha))
      (fun a ha => by simp only [F',mem_filter,mem_univ,true_and] at ha; exact hnonzero _ ha)
      (fun a ha => by
        simp only [F',mem_filter,mem_univ,true_and] at ha
        obtain ⟨y,hy,e⟩ := hpresent _ ha
        obtain ⟨b,rfl⟩ := inRange hy
        exact ⟨b,by simpa [R'] using hy,e⟩)
      (by rw [cR,cF]; exact room)
  refine ⟨C,path,by rw [←cR]; nlinarith,blankC,fun x hx => outside x (by rw [mapR]; exact hx),?_⟩
  intro x hx
  obtain ⟨a,rfl⟩ := inRange (inside hx)
  exact placed a (by simpa [F'] using hx)

/-- The default exchanges: three-cycles in the wrapper square and in the
whole square. -/
def square : StarSpec n J :=
  { S with
    wc := S.L.hub S.L.u
    wcost := 54*S.wm
    wX := S.square_wX
    wX' := S.square_wX'
    wc_conn := S.conn_u
    wc_loop := fun j => (S.L.hub_loop j).2.1
    wc_child := fun j => (S.L.hub_child j).2.1
    wc_K := fun h => S.L.K_u (S.L.hub.injective h).symm
    park := S.parity
    dcost := 54*S.pm
    dX := S.square_dX
    park_own := fun _ => S.parity_own
    park_loop := by
      rintro c (rfl | rfl | rfl) j
      · exact (S.L.hub_loop j).2.1
      · exact (S.L.hub_loop j).2.2
      · exact S.u2_loop j
    park_child := by
      rintro c (rfl | rfl | rfl) j
      · exact (S.L.hub_child j).2.1
      · exact (S.L.hub_child j).2.2
      · exact S.u2_child j
    park_K := by
      rintro c (rfl | rfl | rfl) h
      · exact S.L.K_u (S.L.hub.injective h).symm
      · exact S.L.K_v (S.L.hub.injective h).symm
      · exact S.u2_K (S.L.hub.injective h)
    fw := fun _ => 27*S.pm
    fsort := fun B T R F hB hR _ => S.square_fsort B T R F hB hR
    stat := ∅
    stat_own := by simp
    stat_loop := by simp
    stat_K := by simp
    stat_park := by simp
    dw := fun _ => 0
    dXw := by intro B q _ hq; simp at hq }

end StarBase

namespace StarSpec
variable {J : Nat} (P : StarSpec n J)

def childCells : Finset (Cell n) := univ.biUnion (fun j => (P.Q j).cells)
def homeCells : Finset (Cell n) := univ.biUnion (fun j => (P.Q j).coreCells∪(P.Q j).reserveCells)
def childSpare : Finset (Cell n) := univ.biUnion (fun j => (P.Q j).spareCells)

/-- The number of homes, hence of sources and of goals, of child `j`. -/
def pop (j : Fin J) : Nat := (P.Q j).M+(P.Q j).r

theorem home_sub (j : Fin J) : (P.Q j).coreCells∪(P.Q j).reserveCells⊆(P.Q j).cells := by
  intro x hx; simp only [Frame.cells,mem_union] at hx ⊢; tauto

theorem spare_sub (j : Fin J) : (P.Q j).spareCells⊆(P.Q j).cells := by
  intro x hx; simp only [Frame.cells,mem_union]; tauto

theorem homeCells_sub : P.homeCells⊆P.childCells := by
  intro x hx
  simp only [homeCells,childCells,mem_biUnion,mem_univ,true_and] at hx ⊢
  obtain ⟨j,hj⟩ := hx
  exact ⟨j,P.home_sub j hj⟩

theorem childSpare_sub : P.childSpare⊆P.childCells := by
  intro x hx
  simp only [childSpare,childCells,mem_biUnion,mem_univ,true_and] at hx ⊢
  obtain ⟨j,hj⟩ := hx
  exact ⟨j,P.spare_sub j hj⟩

theorem disjoint_own_childCells : Disjoint P.own P.childCells := by
  rw [childCells,disjoint_biUnion_right]
  exact fun j _ => P.own_child j

theorem disjoint_markers_childCells : Disjoint P.markers P.childCells := by
  rw [childCells,disjoint_biUnion_right]
  exact fun j _ => P.markers_child j

theorem home_spare_disjoint : Disjoint P.homeCells P.childSpare := by
  rw [homeCells,disjoint_biUnion_left]
  intro j _
  rw [childSpare,disjoint_biUnion_right]
  intro j' _
  by_cases hjj : j=j'
  · subst hjj
    exact disjoint_union_left.mpr ⟨(P.Q j).core_spare,(P.Q j).reserve_spare⟩
  · exact (P.L.children_disjoint j j' hjj).mono (P.home_sub j) (P.spare_sub j')

def frame : Frame n where
  goal := P.goal
  coreCells := P.homeCells
  reserveCells := P.own∪P.childSpare
  spareCells := P.markers
  strip := {P.eP,P.zP}
  Entry e z := e=P.eP ∧ z=P.zP
  core_reserve := disjoint_union_right.mpr
    ⟨(P.disjoint_own_childCells.mono_right P.homeCells_sub).symm,P.home_spare_disjoint⟩
  core_spare := (P.disjoint_markers_childCells.mono_right P.homeCells_sub).symm
  reserve_spare := disjoint_union_left.mpr
    ⟨P.own_markers,(P.disjoint_markers_childCells.mono_right P.childSpare_sub).symm⟩
  strip_out := by
    rw [disjoint_insert_left,disjoint_singleton_left]
    have hc (x : Cell n) (hx : ∀ j, x∉(P.Q j).cells) : x∉P.childCells := by
      simp only [childCells,mem_biUnion,mem_univ,true_and,not_exists]; exact hx
    simp only [mem_union,not_or]
    exact ⟨⟨⟨fun h => hc _ P.eP_child (P.homeCells_sub h),P.eP_own,
        fun h => hc _ P.eP_child (P.childSpare_sub h)⟩,P.eP_markers⟩,
      ⟨⟨fun h => hc _ P.zP_child (P.homeCells_sub h),P.zP_own,
        fun h => hc _ P.zP_child (P.childSpare_sub h)⟩,P.zP_markers⟩⟩
  entry_strip := by
    rintro e z ⟨rfl,rfl⟩
    exact ⟨by simp,by simp,P.eP_zP⟩
  goal_nonzero := by
    intro x hx
    rcases mem_union.mp hx with h | h
    · simp only [homeCells,mem_biUnion,mem_univ,true_and] at h
      obtain ⟨j,hj⟩ := h
      rw [←P.goal_child j]
      exact (P.Q j).goal_nonzero x hj
    · rcases mem_union.mp h with h | h
      · exact P.goal_own x h
      · simp only [childSpare,mem_biUnion,mem_univ,true_and] at h
        obtain ⟨j,hj⟩ := h
        exact P.goal_spare j x hj

theorem frame_cells : P.frame.cells=P.childCells∪P.own∪P.markers := by
  ext x
  simp only [Frame.cells,frame,mem_union]
  constructor
  · rintro ((h | h | h) | h)
    · exact Or.inl (Or.inl (P.homeCells_sub h))
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl (P.childSpare_sub h))
    · exact Or.inr h
  · rintro ((h | h) | h)
    · simp only [childCells,mem_biUnion,mem_univ,true_and] at h
      obtain ⟨j,hj⟩ := h
      simp only [Frame.cells,mem_union] at hj
      rcases hj with (h | h) | h
      · exact Or.inl (Or.inl (by simp only [homeCells,mem_biUnion,mem_univ,true_and,mem_union]; exact ⟨j,Or.inl h⟩))
      · exact Or.inl (Or.inl (by simp only [homeCells,mem_biUnion,mem_univ,true_and,mem_union]; exact ⟨j,Or.inr h⟩))
      · exact Or.inl (Or.inr (Or.inr (by simp only [childSpare,mem_biUnion,mem_univ,true_and]; exact ⟨j,h⟩)))
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inr h

theorem child_sub_cells (j : Fin J) : (P.Q j).cells⊆P.frame.cells := by
  intro x hx
  rw [frame_cells]
  simp only [childCells,mem_union,mem_biUnion,mem_univ,true_and]
  exact Or.inl (Or.inl ⟨j,hx⟩)

theorem own_sub_cells : P.own⊆P.frame.cells := by
  intro x hx; rw [frame_cells]; simp [hx]

theorem M_eq : P.frame.M=∑ j, P.pop j := by
  unfold Frame.M frame homeCells pop
  rw [card_biUnion]
  · apply sum_congr rfl
    intro j _
    exact card_union_of_disjoint (P.Q j).core_reserve
  · intro j _ j' _ hjj
    exact (P.L.children_disjoint j j' hjj).mono (P.home_sub j) (P.home_sub j')

end StarSpec
end SlidingPuzzle.NestedRouting.Interface
