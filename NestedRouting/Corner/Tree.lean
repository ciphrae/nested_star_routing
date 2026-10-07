import NestedRouting.Corner.Spec
import NestedRouting.Star.Region
import NestedRouting.Leaf

/-! The recursive tree of regions. A node of side `T` is a brute leaf when
`T < Tbig`, otherwise a corner star whose children have side
`T' = (T - M0)/b`. -/
namespace SlidingPuzzle.NestedRouting.Corner
open Interface Placement Finset

set_option linter.unusedSectionVars false

structure Consts where
  b : Nat
  /-- A bound `H_{b²} ≤ hp/hq` on the harmonic number. -/
  hp : Nat
  hq : Nat
  Tmin : Nat
  b_two : 2≤b
  hq_pos : 0<hq
  harm : ∀ B : Nat, hq*∑ t ∈ Finset.Ioc 0 (b*b), B/t≤hp*B
  /-- Layered harmonic bounds for the two service-cost weights: the slot's
  row plus column, and the margin column's distance from the slot side. -/
  wp1 : Nat
  wp2 : Nat
  wharm1 : ∀ B : Nat, hq*Ledger.layered (fun j : Fin (b*b) => j.val/b+j.val%b) B≤wp1*B
  wharm2 : ∀ B : Nat, hq*Ledger.layered (fun j : Fin (b*b) => b*b-1-j.val) B≤wp2*B
  Tmin_band : 2*b+3≤Tmin
  Tmin_six : 6≤Tmin
  /-- For the rate recursion: `H_{b²}/b < 1`. -/
  hJ_lt : hp<hq*b
  /-- `H_{b²} ≥ b/3`, which keeps the rate constant at least `24`. -/
  hb3 : hq*b≤3*hp
  /-- The harmonic bound is at least `2`, which pays for rounding. -/
  hq2 : 2*hq≤hp
  Tmin_lane : 2*(b*b)+4+b≤Tmin
  /-- A leaf request, `16T + 24W + 170`, is at most `24T`. -/
  Tmin_leaf : 24*(2*b)+170≤8*Tmin

namespace Consts
variable (k : Consts)

theorem b_pos : 1≤k.b := by have := k.b_two; omega
theorem bb : 2*k.b≤k.b*k.b := Nat.mul_le_mul_right _ k.b_two

def W : Nat := 2*k.b
def M0 : Nat := 2*(k.b*k.b)+4
def Tbig : Nat := k.M0+(k.W+12)+k.b*k.Tmin
def child (T : Nat) : Nat := (T-k.M0)/k.b

theorem child_ge {T : Nat} (hT : k.Tbig≤T) : k.Tmin≤k.child T := by
  unfold child Tbig at *
  apply (Nat.le_div_iff_mul_le (by have := k.b_pos; omega)).mpr
  rw [Nat.mul_comm]; omega

theorem child_lt {T : Nat} (hT : k.Tbig≤T) : k.child T<T := by
  have := k.b_pos
  unfold child Tbig M0 at *
  calc (T-(2*(k.b*k.b)+4))/k.b ≤ T-(2*(k.b*k.b)+4) := Nat.div_le_self _ _
    _ < T := by omega

theorem M0_le {T : Nat} (hT : k.Tbig≤T) : k.M0≤T := le_trans (by unfold Tbig; omega) hT

theorem child_mul (T : Nat) : k.b*k.child T≤T-k.M0 := by
  unfold child; rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _

theorem W_M0 : k.W+4≤k.M0 := by unfold W M0; have := k.bb; have := k.b_two; omega

/-- The corner parameters of a node of side `T ≥ Tbig`. -/
def params (T cs : Nat) (hT : k.Tbig≤T) (hcs : 2*cs+1<k.W) : Params where
  b := k.b
  T := T
  T' := k.child T
  cs := cs
  b_pos := k.b_pos
  rows_fit := by
    have hM := k.M0_le hT
    have h := k.child_mul T
    have hW := k.W_M0
    show k.W+4+k.b*k.child T≤T
    omega
  cols_fit := by
    have hM := k.M0_le hT
    have h := k.child_mul T
    show k.M0+k.b*k.child T≤T
    omega
  hub_fit := by
    have h : k.W+k.M0+11≤k.Tbig := by unfold Tbig; omega
    show k.W+k.M0+11≤T
    omega
  band_fit := (k.Tmin_band).trans (k.child_ge hT)
  strip_fit := hcs

theorem W_lt_Tmin : k.W<k.Tmin := by have := k.Tmin_band; unfold W; omega

variable {n : Nat} [NeZero n] {G : Board n}

/-- The goal has no blank in the body (rows `≥ W`) of the square. -/
def GoalOK (G : Board n) {T : Nat} [NeZero T] (q : Placement T n) : Prop :=
  ∀ r c, k.W≤r → r<T → c<T → G (q.loc r c)≠0

def leafBody {T : Nat} : Finset (Cell T) := univ.filter (fun x => k.W≤x.1.val)

/-- The body of a placed square: its rows `≥ W`. -/
def bodyCells {T : Nat} (q : Placement T n) : Finset (Cell n) := k.leafBody.map q.embed

theorem mem_bodyCells {T : Nat} [NeZero T] (q : Placement T n) {x : Cell n} :
    x∈k.bodyCells q ↔ ∃ r c, k.W≤r ∧ r<T ∧ c<T ∧ q.loc r c=x := by
  unfold bodyCells leafBody
  simp only [mem_map,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨y.1.val,y.2.val,hy,y.1.isLt,y.2.isLt,q.loc_eq y.1.isLt y.2.isLt⟩
  · rintro ⟨r,c,h1,h2,h3,rfl⟩
    exact ⟨(⟨r,h2⟩,⟨c,h3⟩),h1,(q.loc_eq h2 h3).symm⟩

/-- A node of side `T` placed by `q`, entered at `(2cs,0),(2cs+1,0)`: its
cells lie in the body of the square and its strip in the band above it. -/
structure Built (G : Board n) (T cs : Nat) [NeZero T] (q : Placement T n) where
  R : Region n
  cells_eq : R.cells=k.bodyCells q
  spare6 : R.g=6
  /-- The spare cells lie just below the band. -/
  spare_near : ∀ x∈R.spareCells, ∃ r c, r≤k.W+1 ∧ c<T ∧ q.loc r c=x
  strip : ∀ x∈R.strip, ∃ r c, r<k.W ∧ c<T ∧ q.loc r c=x
  entry : R.Entry (q.loc (2*cs) 0) (q.loc (2*cs+1) 0)
  goal : R.goal=G
  /-- No blank in the node's cells is all its records need to start. -/
  prep : ∀ B : Board n, (∀ x∈R.cells, B x≠0) → R.Prepared B

theorem Built.cells {T cs : Nat} [NeZero T] {q : Placement T n} (B : k.Built G T cs q) :
    ∀ x∈B.R.cells, ∃ r c, k.W≤r ∧ r<T ∧ c<T ∧ q.loc r c=x := by
  intro x hx; rw [B.cells_eq] at hx; exact (k.mem_bodyCells q).mp hx

/-! ### Leaves -/

section Leaf
variable {T : Nat} [NeZero T] (hW : k.W<T) (h6 : 6≤T)

include hW h6 in
def leafSpare : Finset (Cell T) :=
  (univ : Finset (Fin 6)).map ⟨fun i => (⟨k.W,hW⟩,⟨i.val,by omega⟩),by
    intro a b h; simp only [Prod.mk.injEq,Fin.mk.injEq,true_and] at h; exact Fin.ext h⟩

omit [NeZero T] in
theorem mem_leafSpare {x : Cell T} : x∈k.leafSpare hW h6 ↔ x.1.val=k.W ∧ x.2.val<6 := by
  unfold leafSpare
  simp only [mem_map,mem_univ,true_and]
  constructor
  · rintro ⟨i,rfl⟩; exact ⟨rfl,i.isLt⟩
  · rintro ⟨h1,h2⟩; exact ⟨⟨x.2.val,h2⟩,Prod.ext (Fin.ext h1.symm) rfl⟩

omit [NeZero T] in
theorem leafSpare_body : k.leafSpare hW h6⊆k.leafBody := by
  intro x hx; simp [leafBody,((k.mem_leafSpare hW h6).mp hx).1]

/-- The leaf's entry cell `(2cs,0)` and blank cell `(2cs+1,0)`, locally. -/
def leafE (cs : Nat) (hcs : 2*cs+1<k.W) : Cell T := (⟨2*cs,by omega⟩,⟨0,by omega⟩)
def leafZ (cs : Nat) (hcs : 2*cs+1<k.W) : Cell T := (⟨2*cs+1,by omega⟩,⟨0,by omega⟩)

include hW h6 in
theorem leaf_fit (cs : Nat) (hcs : 2*cs+1<k.W) : Entry.Fit T k.W cs := ⟨hcs,hW,h6⟩

include hW h6 in
/-- The leaf request: the direct exchange at the entry, parking on row `W`. -/
theorem leaf_rX (cs : Nat) (hcs : 2*cs+1<k.W) (q : Placement T n) (B : Board n)
    (hB : blank B=q.embed (k.leafZ hW h6 cs hcs)) (x : Cell T) (hx : k.W≤x.1.val) :
    ∃ C : Board n, ∃ path : Path B C, ∃ u∈k.leafSpare hW h6, u≠x ∧ blank C=q.embed (k.leafZ hW h6 cs hcs) ∧
      Cycle3.IsCycle B C (q.embed (k.leafE hW h6 cs hcs)) (q.embed x) (q.embed u) ∧
      path.length≤Entry.dw q (k.leaf_fit hW h6 cs hcs) x.1.val x.2.val := by
  have h1 : 2*cs<T := by omega
  have h2 : 2*cs+1<T := by omega
  have h0 : 0<T := by omega
  have eZ : q.embed (k.leafZ hW h6 cs hcs)=q.loc (2*cs+1) 0 := (q.loc_eq h2 h0).symm
  have eE : q.embed (k.leafE hW h6 cs hcs)=q.loc (2*cs) 0 := (q.loc_eq h1 h0).symm
  have eX : q.embed x=q.loc x.1.val x.2.val := (q.loc_eq x.1.isLt x.2.isLt).symm
  let u (c' : Nat) (hc : c'<2) : Cell T := (⟨k.W,hW⟩,⟨c',by omega⟩)
  have eU (c' : Nat) (hc : c'<2) : q.embed (u c' hc)=q.loc k.W c' := (q.loc_eq hW (by omega)).symm
  have uS (c' : Nat) (hc : c'<2) : u c' hc∈k.leafSpare hW h6 := (k.mem_leafSpare hW h6).mpr ⟨rfl,by simp [u]; omega⟩
  have go (c' : Nat) (hc : c'<2) (ne : u c' hc≠x) : ∃ C : Board n, ∃ path : Path B C,
      ∃ u∈k.leafSpare hW h6, u≠x ∧ blank C=q.embed (k.leafZ hW h6 cs hcs) ∧
      Cycle3.IsCycle B C (q.embed (k.leafE hW h6 cs hcs)) (q.embed x) (q.embed u) ∧
      path.length≤Entry.dw q (k.leaf_fit hW h6 cs hcs) x.1.val x.2.val := by
    have xy : q.loc x.1.val x.2.val≠q.loc k.W c' := by rw [←eX,←eU c' hc]; exact fun e => ne (q.embed.injective e).symm
    obtain ⟨C,path,len,bC,cyc⟩ := Entry.direct_exchange_at q (k.leaf_fit hW h6 cs hcs) B (hB.trans eZ) hx x.1.isLt
      x.2.isLt hc xy
    rw [←eE,←eX,←eU c' hc] at cyc
    exact ⟨C,path,u c' hc,uS c' hc,ne,bC.trans eZ.symm,cyc,len⟩
  by_cases h : u 0 (by omega)=x
  · refine go 1 (by omega) ?_
    rw [←h]; intro e; simp [u] at e
  · exact go 0 (by omega) h

/-- The leaf's final-sort bound: three halves of the `t`-cycle weights of the square. -/
def leafF : Nat := 2*∑ y : Cell T, (3*(Cycle3.tw y.1.val y.2.val+2)+3)/4

open Classical in
/-- The weight of a cell of the square: the `t`-cycle bound at its local position. -/
noncomputable def leafW (q : Placement T n) (x : Cell n) : Nat :=
  if h : ∃ y : Cell T, q.embed y=x then (3*(Cycle3.tw h.choose.1.val h.choose.2.val+2)+3)/4 else 0

omit [NeZero n] in
theorem leafW_embed (q : Placement T n) (y : Cell T) :
    leafW q (q.embed y)=(3*(Cycle3.tw y.1.val y.2.val+2)+3)/4 := by
  classical
  have h : ∃ y' : Cell T, q.embed y'=q.embed y := ⟨y,rfl⟩
  unfold leafW
  rw [dif_pos h,q.embed.injective h.choose_spec]

include hW h6 in
/-- The leaf's final sort: the `t`-cycle sort of its body, each cell charged
by its position. -/
theorem leaf_fX (cs : Nat) (hcs : 2*cs+1<k.W) (q : Placement T n) (hg : k.GoalOK G q) (B : Board n)
    (hB : blank B=q.embed (k.leafZ hW h6 cs hcs))
    (present : ∀ x∈k.leafBody\k.leafSpare hW h6, ∃ y∈k.leafBody, B (q.embed y)=G (q.embed x)) :
    ∃ C : Board n, ∃ path : Path B C, path.length≤leafF (T:=T) ∧ blank C=blank B ∧
      (∀ x, x∉(k.leafBody (T:=T)).map q.embed → C x=B x) ∧
      ∀ x∈k.leafBody\k.leafSpare hW h6, C (q.embed x)=G (q.embed x) := by
  classical
  have h2 : 2*cs+1<T := by omega
  have h0 : 0<T := by omega
  have eZ : q.embed (k.leafZ hW h6 cs hcs)=q.loc (2*cs+1) 0 := (q.loc_eq h2 h0).symm
  set R := (k.leafBody (T:=T)).map q.embed
  set F := (k.leafBody\k.leafSpare hW h6).map q.embed
  have room : F.card+3≤R.card := by
    have sub := k.leafSpare_body hW h6
    have e := card_sdiff_of_subset sub
    have h6' : (k.leafSpare hW h6).card=6 := by unfold leafSpare; simp
    simp only [F,R,card_map]
    have := card_le_card sub
    omega
  obtain ⟨C,path,len,bC,off,placed⟩ := Entry.finish q (k.leaf_fit hW h6 cs hcs) B G (hB.trans eZ) R F
    (by
      intro x hx
      obtain ⟨y,hy,rfl⟩ := mem_map.mp hx
      simp only [leafBody,mem_filter,mem_univ,true_and] at hy
      exact ⟨y.1.val,y.2.val,hy,y.1.isLt,y.2.isLt,q.loc_eq y.1.isLt y.2.isLt⟩)
    (leafW q)
    (by
      intro r c _ hr hc
      rw [q.loc_eq hr hc,leafW_embed]
      unfold Cycle3.tw; simp only; omega)
    (map_subset_map.mpr sdiff_subset)
    (by
      intro x hx
      obtain ⟨y,hy,rfl⟩ := mem_map.mp hx
      simp only [mem_sdiff,leafBody,mem_filter,mem_univ,true_and] at hy
      have := hg y.1.val y.2.val hy.1 y.1.isLt y.2.isLt
      rwa [q.loc_eq y.1.isLt y.2.isLt] at this)
    (by
      intro x hx
      obtain ⟨y,hy,rfl⟩ := mem_map.mp hx
      obtain ⟨z,hz,e⟩ := present y hy
      exact ⟨q.embed z,mem_map_of_mem _ hz,e⟩)
    room
  refine ⟨C,path,?_,bC,off,fun x hx => placed _ (mem_map_of_mem _ hx)⟩
  have hs : ∑ x∈R, leafW q x≤∑ y : Cell T, (3*(Cycle3.tw y.1.val y.2.val+2)+3)/4 := by
    simp only [R,sum_map,leafW_embed]
    exact sum_le_sum_of_subset (subset_univ _)
  unfold leafF
  omega

def leafSpec (cs : Nat) (hcs : 2*cs+1<k.W) (q : Placement T n) (hg : k.GoalOK G q) : LeafSpec n where
  m := T
  place := q
  goal := G
  core := k.leafBody\k.leafSpare hW h6
  reserve := ∅
  spare := k.leafSpare hW h6
  core_reserve := disjoint_empty_right _
  core_spare := sdiff_disjoint
  reserve_spare := disjoint_empty_left _
  side := h6
  six := by unfold leafSpare; simp
  goal_nonzero := by
    intro x hx
    simp only [union_empty,mem_sdiff,leafBody,mem_filter,mem_univ,true_and] at hx
    have := hg x.1.val x.2.val hx.1 x.1.isLt x.2.isLt
    rwa [q.loc_eq x.1.isLt x.2.isLt] at this
  entry e z := e=k.leafE hW h6 cs hcs ∧ z=k.leafZ hW h6 cs hcs
  entry_strip := by
    rintro e z ⟨rfl,rfl⟩
    simp only [union_empty,mem_union,mem_sdiff,leafBody,mem_filter,mem_univ,true_and,k.mem_leafSpare,leafE,leafZ]
    refine ⟨by omega,by omega,?_⟩
    intro e; simp at e
  rcost := Entry.dcost q (k.leaf_fit hW h6 cs hcs)
  rw x := Entry.dw q (k.leaf_fit hW h6 cs hcs) x.1.val x.2.val
  rw_le x := Entry.dw_le q (k.leaf_fit hW h6 cs hcs) x.1.isLt x.2.isLt
  rX := by
    rintro e z ⟨rfl,rfl⟩ B hB x hx
    have hxW : k.W≤x.1.val := by
      simp only [union_empty,mem_union,mem_sdiff,leafBody,mem_filter,mem_univ,true_and,k.mem_leafSpare] at hx
      omega
    exact k.leaf_rX hW h6 cs hcs q B hB x hxW
  fcost := leafF (T:=T)
  fX := by
    rintro e z ⟨rfl,rfl⟩ B hB present
    have body : k.leafBody\k.leafSpare hW h6∪∅∪k.leafSpare hW h6=k.leafBody :=
      by rw [union_empty,sdiff_union_of_subset (k.leafSpare_body hW h6)]
    obtain ⟨C,path,len,bC,off,placed⟩ := k.leaf_fX hW h6 cs hcs q hg B hB (by
      intro x hx
      obtain ⟨y,hy,e⟩ := present x (by simpa using hx)
      exact ⟨y,by rw [←body]; exact hy,e⟩)
    refine ⟨C,path,len,bC,fun x hx => off x (by rw [←body]; exact hx),fun x hx => placed x (by simpa using hx)⟩

theorem leaf_cells (cs : Nat) (hcs : 2*cs+1<k.W) (q : Placement T n) (hg : k.GoalOK G q) :
    (k.leafSpec hW h6 cs hcs q hg).frame.cells=(k.leafBody).map q.embed := by
  rw [LeafSpec.cells_eq]
  congr 1
  show k.leafBody\k.leafSpare hW h6∪∅∪k.leafSpare hW h6=_
  rw [union_empty,sdiff_union_of_subset (k.leafSpare_body hW h6)]

theorem leaf_strip (cs : Nat) (hcs : 2*cs+1<k.W) (q : Placement T n) (hg : k.GoalOK G q) {x : Cell n} :
    x∈(k.leafSpec hW h6 cs hcs q hg).frame.strip ↔ ∃ y : Cell T, y.1.val<k.W ∧ q.embed y=x := by
  show x∈(univ\(k.leafBody\k.leafSpare hW h6∪∅∪k.leafSpare hW h6)).map q.embed ↔ _
  rw [union_empty,sdiff_union_of_subset (k.leafSpare_body hW h6)]
  simp only [leafBody,mem_map,mem_sdiff,mem_filter,mem_univ,true_and,not_le]
  exact ⟨fun ⟨y,h,e⟩ => ⟨y,h.2,e⟩,fun ⟨y,h,e⟩ => ⟨y,⟨mem_univ _,h⟩,e⟩⟩

def leaf (cs : Nat) (hcs : 2*cs+1<k.W) (q : Placement T n) (hg : k.GoalOK G q) : k.Built G T cs q where
  R := (k.leafSpec hW h6 cs hcs q hg).region
  cells_eq := k.leaf_cells hW h6 cs hcs q hg
  spare6 := by
    change (k.leafSpec hW h6 cs hcs q hg).frame.g=6
    rw [LeafSpec.g_eq]
    show (k.leafSpare hW h6).card=6
    unfold leafSpare; simp
  spare_near := by
    intro x hx
    change x∈(k.leafSpare hW h6).map q.embed at hx
    obtain ⟨y,hy,rfl⟩ := mem_map.mp hx
    have := (k.mem_leafSpare hW h6).mp hy
    exact ⟨y.1.val,y.2.val,by omega,y.2.isLt,q.loc_eq y.1.isLt y.2.isLt⟩
  strip := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := (k.leaf_strip hW h6 cs hcs q hg).mp hx
    exact ⟨y.1.val,y.2.val,hy,y.2.isLt,q.loc_eq y.1.isLt y.2.isLt⟩
  entry := by
    have h1 : 2*cs<T := by omega
    have h2 : 2*cs+1<T := by omega
    have h0 : 0<T := by omega
    exact ⟨k.leafE hW h6 cs hcs,k.leafZ hW h6 cs hcs,⟨rfl,rfl⟩,(q.loc_eq h1 h0).symm,(q.loc_eq h2 h0).symm⟩
  goal := rfl
  prep := fun _ h => h

end Leaf

/-- Builders for every child placement of side `child T`. -/
abbrev Sub (G : Board n) (T : Nat) [NeZero (k.child T)] : Type 1 :=
  ∀ cs', 2*cs'+1<k.W → ∀ q' : Placement (k.child T) n, k.GoalOK G q' → k.Built G (k.child T) cs' q'

/-! ### Corner stars -/

section Star
variable {T : Nat} [NeZero T] (hT : k.Tbig≤T) (cs : Nat) (hcs : 2*cs+1<k.W) (q : Placement T n)

instance paramsNeZero : NeZero (k.params T cs hT hcs).T := inferInstanceAs (NeZero T)

omit [NeZero T] in
include hT in
theorem child_ne : NeZero (k.child T) := ⟨by have := k.child_ge hT; have := k.Tmin_six; omega⟩

local notation "P" => k.params T cs hT hcs

theorem P_T' : (P).T'=k.child T := rfl
theorem P_W : (P).W=k.W := rfl

/-- The placement of child slot `j`. -/
def slot (j : Fin (P).J) : Placement (k.child T) n :=
  q.sub ((P).R ((P).rowOf j)) ((P).C ((P).colOf j)) (k.child T)
    ((P).R_le ((P).rowOf_lt j.isLt)) ((P).C_le ((P).colOf_lt j))

theorem slot_loc (j : Fin (P).J) {r c : Nat} (hr : r<k.child T) (hc : c<k.child T) :
    haveI := k.child_ne hT
    (k.slot hT cs hcs q j).loc r c=q.loc ((P).R ((P).rowOf j)+r) ((P).C ((P).colOf j)+c) := by
  have := k.child_ne hT
  exact q.loc_sub (t:=k.child T) ((P).R_le ((P).rowOf_lt j.isLt)) ((P).C_le ((P).colOf_lt j)) hr hc

theorem slot_ok (hg : k.GoalOK G q) (j : Fin (k.params T cs hT hcs).J) :
    haveI := k.child_ne hT
    k.GoalOK G (k.slot hT cs hcs q j) := by
  have := k.child_ne hT
  intro r c hW hr hc
  rw [k.slot_loc hT cs hcs q j hr hc]
  have hb := (k.params T cs hT hcs).bounds j.isLt
  have := hb.R_le; have := hb.f_le; have := hb.y_ge; have := hb.y_band
  have hf : (P).f j=(P).C ((P).colOf j) := rfl
  have e1 : (P).T=T := rfl
  have e2 : (P).T'=k.child T := rfl
  have e3 : (P).W=k.W := rfl
  apply hg <;> omega

theorem slot_col (j : Fin (k.params T cs hT hcs).J) : 2*(k.params T cs hT hcs).colOf j+1<k.W := by
  have := (k.params T cs hT hcs).colOf_lt j
  show _<2*k.b
  change _<k.b at this
  omega

variable [NeZero (k.child T)] (sub : k.Sub G T) (hg : k.GoalOK G q)

/-- The children of the star. -/
def kids (j : Fin (P).J) : k.Built G (k.child T) ((P).colOf j) (k.slot hT cs hcs q j) :=
  sub _ (k.slot_col hT cs hcs j) _ (k.slot_ok hT cs hcs q hg j)

theorem kids_cells (j : Fin (P).J) (x : Cell n) (hx : x∈(k.kids hT cs hcs q sub hg j).R.cells) :
    ∃ r c, (P).bodyP j r c ∧ q.loc r c=x := by
  obtain ⟨r,c,h1,h2,h3,rfl⟩ := Built.cells k (k.kids hT cs hcs q sub hg j) x hx
  refine ⟨_,_,?_,(k.slot_loc hT cs hcs q j h2 h3).symm⟩
  unfold Params.bodyP
  rw [P_T',P_W]
  omega

theorem kids_strip (j : Fin (P).J) (x : Cell n) (hx : x∈(k.kids hT cs hcs q sub hg j).R.strip) :
    ∃ r c, (P).bandP j r c ∧ q.loc r c=x := by
  obtain ⟨r,c,h1,h3,rfl⟩ := (k.kids hT cs hcs q sub hg j).strip x hx
  have hW := k.W_lt_Tmin
  have hc := k.child_ge hT
  refine ⟨_,_,?_,(k.slot_loc hT cs hcs q j (by omega) h3).symm⟩
  unfold Params.bandP
  rw [P_T',P_W]
  omega

theorem kids_entry (j : Fin (P).J) :
    (k.kids hT cs hcs q sub hg j).R.Entry ((P).e q j) ((P).z q j) := by
  have h := (k.kids hT cs hcs q sub hg j).entry
  have hb := (P).band_fit
  have hc := (P).colOf_lt j
  rw [P_T'] at hb
  change _<k.b at hc
  change 2*k.b+3≤_ at hb
  rw [k.slot_loc hT cs hcs q j (by omega) (by omega),k.slot_loc hT cs hcs q j (by omega) (by omega)] at h
  unfold Params.e Params.z Params.y Params.f
  rw [Nat.add_zero,←Nat.add_assoc] at h
  exact h

include hg in
theorem body_ok : ∀ x∈(P).body q, G x≠0 := by
  intro x hx
  obtain ⟨r,c,h1,h2,h3,rfl⟩ := ((P).mem_body q).mp hx
  exact hg r c h1 h2 h3

/-- The corner star over the built children. -/
noncomputable def starSpec : StarSpec n (P).J :=
  (P).spec q (fun j => (k.kids hT cs hcs q sub hg j).R) (k.kids_cells hT cs hcs q sub hg)
    (k.kids_strip hT cs hcs q sub hg) (k.kids_entry hT cs hcs q sub hg)
    G (fun j => (k.kids hT cs hcs q sub hg j).goal) (k.body_ok hT cs hcs q hg) k.hp k.hq k.hq_pos k.harm
    k.wp1 k.wp2 k.wharm1 k.wharm2

/-- The corner star as a built node. -/
noncomputable def star : k.Built G T cs q where
  R := (k.starSpec hT cs hcs q sub hg).region
  cells_eq := by
    change (k.starSpec hT cs hcs q sub hg).frame.cells=_
    rw [StarSpec.frame_cells]
    ext x
    simp only [mem_union]
    constructor
    · rintro ((h | h) | h)
      · simp only [StarSpec.childCells,mem_biUnion,mem_univ,true_and] at h
        obtain ⟨j,h⟩ := h
        obtain ⟨r,c,hp,rfl⟩ := k.kids_cells hT cs hcs q sub hg j x h
        have l := (P).bodyP_lt j.isLt hp
        have hb := (P).bounds j.isLt
        have := hb.y_ge; have := hb.y_band
        unfold Params.bodyP at hp
        rw [P_W] at *
        exact (k.mem_bodyCells q).mpr ⟨r,c,by omega,l.1,l.2,rfl⟩
      · exact (((P).mem_own q _).mp h).1
      · have hfit : k.W+k.M0+11≤T := (P).hub_fit
        have hM : (P).M0=k.M0 := rfl
        obtain ⟨i,hi,rfl⟩ := ((P).mem_markers q).mp h
        rw [P_W,hM]
        exact (k.mem_bodyCells q).mpr ⟨_,_,by omega,by omega,by unfold W at *; omega,rfl⟩
    · intro h
      by_cases h1 : x∈(k.starSpec hT cs hcs q sub hg).childCells
      · exact Or.inl (Or.inl h1)
      by_cases h2 : x∈(P).markers q
      · exact Or.inr h2
      refine Or.inl (Or.inr ((P).mem_own q _ |>.mpr ⟨h,?_,h2⟩))
      intro j hj
      apply h1
      simp only [StarSpec.childCells,mem_biUnion,mem_univ,true_and]
      exact ⟨j,hj⟩
  spare6 := (P).markers_card q
  spare_near := by
    intro x hx
    change x∈(P).markers q at hx
    have hfit : k.W+k.M0+11≤T := (P).hub_fit
    have hM : (P).M0=k.M0 := rfl
    obtain ⟨i,hi,rfl⟩ := ((P).mem_markers q).mp hx
    rw [P_W,hM]
    exact ⟨_,_,le_rfl,by omega,rfl⟩
  strip := by
    intro x hx
    have hWT := k.W_lt_Tmin
    have := k.Tmin_six
    have := Nat.le_mul_of_pos_left k.Tmin k.b_pos
    have : k.Tmin≤T := le_trans (by unfold Tbig; omega) hT
    change x∈({(P).eP q,(P).zP q} : Finset (Cell n)) at hx
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ⟨2*cs,0,by omega,by omega,rfl⟩
    · exact ⟨2*cs+1,0,by omega,by omega,rfl⟩
  entry := ⟨rfl,rfl⟩
  goal := rfl
  prep := by
    intro B h
    refine ⟨h,fun j => (k.kids hT cs hcs q sub hg j).prep B (fun x hx => h x ?_)⟩
    change x∈(k.starSpec hT cs hcs q sub hg).frame.cells
    rw [StarSpec.frame_cells]
    simp only [mem_union,StarSpec.childCells,mem_biUnion,mem_univ,true_and]
    exact Or.inl (Or.inl ⟨j,hx⟩)

end Star

/-! ### The tree -/

/-- The node of side `T`: a corner star over nodes of side `child T` when
`T ≥ Tbig`, otherwise a brute leaf. -/
noncomputable def build (T : Nat) [NeZero T] (hT : k.Tmin≤T) (cs : Nat) (hcs : 2*cs+1<k.W) (q : Placement T n)
    (hg : k.GoalOK G q) : k.Built G T cs q :=
  if h : k.Tbig≤T then
    haveI := k.child_ne h
    k.star h cs hcs q (fun cs' hcs' q' hg' => build (k.child T) (k.child_ge h) cs' hcs' q' hg') hg
  else k.leaf (by have := k.W_lt_Tmin; omega) (by have := k.Tmin_six; omega) cs hcs q hg
termination_by T
decreasing_by exact k.child_lt h

theorem build_star (T : Nat) [NeZero T] (hT : k.Tmin≤T) (cs : Nat) (hcs : 2*cs+1<k.W) (q : Placement T n)
    (hg : k.GoalOK G q) (h : k.Tbig≤T) :
    haveI := k.child_ne h
    k.build T hT cs hcs q hg=
      k.star h cs hcs q (fun cs' hcs' q' hg' => k.build (k.child T) (k.child_ge h) cs' hcs' q' hg') hg := by
  rw [build]; simp [h]

theorem build_leaf (T : Nat) [NeZero T] (hT : k.Tmin≤T) (cs : Nat) (hcs : 2*cs+1<k.W) (q : Placement T n)
    (hg : k.GoalOK G q) (h : ¬k.Tbig≤T) :
    k.build T hT cs hcs q hg=
      k.leaf (by have := k.W_lt_Tmin; omega) (by have := k.Tmin_six; omega) cs hcs q hg := by
  rw [build]; simp [h]

end Consts
end SlidingPuzzle.NestedRouting.Corner
