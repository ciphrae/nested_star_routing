import NestedRouting.Central.Exchange
import NestedRouting.Corner.Budget

/-! The root region: the central pinwheel over four corner-star trees, one
per quadrant, each placed by its frame so that its corner faces the centre. -/
namespace SlidingPuzzle.NestedRouting.Central
open Interface Placement Finset Corner

set_option linter.unusedSectionVars false

namespace CParams
variable {n : Nat} [NeZero n] (p : CParams n)

instance T_ne : NeZero p.T := ⟨by have := p.T_big; omega⟩

variable (k : Consts) (hW : p.W=k.W) (hT : k.Tmin≤p.T) (G : Board n) (hG : ∀ y, y≠p.zP → G y≠0)

theorem AT : p.A+p.T≤p.N := by unfold A N; omega

/-- The placement of quadrant `j`, oriented by its frame. -/
def quad (j : Fin 4) : Placement p.T n := (p.frame j).sub p.A p.A p.T p.AT p.AT

theorem quad_loc (j : Fin 4) {r c' : Nat} (hr : r<p.T) (hc : c'<p.T) :
    (p.quad j).loc r c'=(p.frame j).loc (p.A+r) (p.A+c') :=
  (p.frame j).loc_sub p.AT p.AT hr hc

include hW hG in
theorem quad_ok (j : Fin 4) : k.GoalOK G (p.quad j) := by
  intro r c' h1 h2 h3
  rw [p.quad_loc j h2 h3]
  apply hG
  have := p.AT; have := p.B_le_A; have := p.two_le_c
  exact p.frame_ne_mid j (by omega) (by omega) (by omega) (by have := p.c_lt; omega)

/-- Quadrant trees. -/
noncomputable def kid (j : Fin 4) : k.Built G p.T 0 (p.quad j) :=
  k.build p.T hT 0 (by unfold Consts.W; have := k.b_two; omega) (p.quad j) (p.quad_ok k hW G hG j)

noncomputable def kidQ (j : Fin 4) : Region n := (p.kid k hW hT G hG j).R

theorem kid_cells : ∀ j y, y∈(p.kidQ k hW hT G hG j).cells →
    ∃ r c', p.A+p.W≤r ∧ r<p.N ∧ p.A≤c' ∧ c'<p.N ∧ (p.frame j).loc r c'=y := by
  intro j y hy
  obtain ⟨r,c',h1,h2,h3,rfl⟩ := Consts.Built.cells k (p.kid k hW hT G hG j) y hy
  have := p.AT
  exact ⟨p.A+r,p.A+c',by omega,by omega,by omega,by omega,(p.quad_loc j h2 h3).symm⟩

theorem kid_strip : ∀ j y, y∈(p.kidQ k hW hT G hG j).strip →
    ∃ r c', p.A≤r ∧ r<p.A+p.W ∧ p.A≤c' ∧ c'<p.N ∧ (p.frame j).loc r c'=y := by
  intro j y hy
  obtain ⟨r,c',h1,h3,rfl⟩ := (p.kid k hW hT G hG j).strip y hy
  have := p.AT; have := p.T_big
  exact ⟨p.A+r,p.A+c',by omega,by omega,by omega,by omega,(p.quad_loc j (by omega) h3).symm⟩

theorem kid_entry : ∀ j, (p.kidQ k hW hT G hG j).Entry (p.e j) (p.z j) := by
  intro j
  have h := (p.kid k hW hT G hG j).entry
  have := p.T_big
  rw [p.quad_loc j (by omega) (by omega),p.quad_loc j (by omega) (by omega)] at h
  have e1 : p.A+2*0=p.A := by omega
  have e2 : p.A+(2*0+1)=p.A+1 := by omega
  rw [e1,e2,Nat.add_zero] at h
  exact h

/-- Quadrant `3` is reflected both ways: its far corner is the board's `(0,0)`. -/
theorem quad3_loc {r c' : Nat} (hr : r<p.T) (hc : c'<p.T) :
    (p.quad 3).loc r c'=cc (p.T-1-r) (p.T-1-c') := by
  have := p.AT; have := p.N_n
  have hNA : p.N=p.A+p.T := by unfold N A; omega
  rw [p.quad_loc 3 hr hc]
  have h1 := p.frame_row 3 (r:=p.A+r) (c':=p.A+c') (by omega) (by omega)
  have h2 := p.frame_col 3 (r:=p.A+r) (c':=p.A+c') (by omega) (by omega)
  have f3 : fr (3 : Fin 4)=true := rfl
  have c3 : fc (3 : Fin 4)=true := rfl
  rw [f3] at h1; rw [c3] at h2
  unfold ρ at h1 h2; simp only [if_true] at h1 h2
  have b := cc_val (n:=n) (r:=p.T-1-r) (c:=p.T-1-c') (by omega) (by omega)
  exact cell_eq (by rw [h1,b.1]; omega) (by rw [h2,b.2]; omega)

/-- The board's corner block, but for its `(0,1)`, holds homes of quadrant `3`. -/
theorem kid_corner : ∀ y, (y=cc 0 0 ∨ y=cc 1 0 ∨ y=cc 1 1) →
    ∃ j, y∈(p.kidQ k hW hT G hG j).coreCells∪(p.kidQ k hW hT G hG j).reserveCells := by
  intro y hy
  have hTb := p.T_big
  have hWk : k.W=p.W := hW.symm
  have home (r c' : Nat) (hr1 : k.W+2≤r) (hr : r<p.T) (hc : c'<p.T) :
      (p.quad 3).loc r c'∈(p.kidQ k hW hT G hG 3).coreCells∪(p.kidQ k hW hT G hG 3).reserveCells := by
    have hcell : (p.quad 3).loc r c'∈(p.kidQ k hW hT G hG 3).cells := by
      change _∈(p.kid k hW hT G hG 3).R.cells
      rw [(p.kid k hW hT G hG 3).cells_eq]
      exact (k.mem_bodyCells (p.quad 3)).mpr ⟨r,c',by omega,hr,hc,rfl⟩
    have nsp : (p.quad 3).loc r c'∉(p.kidQ k hW hT G hG 3).spareCells := by
      intro hs
      obtain ⟨r',c'',h1,h2,e⟩ := (p.kid k hW hT G hG 3).spare_near _ hs
      have := (p.quad 3).loc_inj (by omega) h2 hr hc e
      omega
    simp only [Frame.cells,mem_union] at hcell
    rcases hcell with h | h
    · exact mem_union.mpr h
    · exact absurd h nsp
  refine ⟨3,?_⟩
  rcases hy with rfl | rfl | rfl
  · have := home (p.T-1) (p.T-1) (by omega) (by omega) (by omega)
    rwa [p.quad3_loc (by omega) (by omega),show p.T-1-(p.T-1)=0 by omega] at this
  · have := home (p.T-2) (p.T-1) (by omega) (by omega) (by omega)
    rwa [p.quad3_loc (by omega) (by omega),show p.T-1-(p.T-2)=1 by omega,show p.T-1-(p.T-1)=0 by omega] at this
  · have := home (p.T-2) (p.T-2) (by omega) (by omega) (by omega)
    rwa [p.quad3_loc (by omega) (by omega),show p.T-1-(p.T-2)=1 by omega] at this

/-- The root star. -/
noncomputable def rootSpec : StarSpec n 4 :=
  p.spec (p.kidQ k hW hT G hG) (p.kid_cells k hW hT G hG) (p.kid_strip k hW hT G hG)
    (p.kid_entry k hW hT G hG) G (fun j => (p.kid k hW hT G hG j).goal) hG (p.kid_corner k hW hT G hG)

noncomputable def root : Region n := (p.rootSpec k hW hT G hG).region

theorem root_entry : (p.root k hW hT G hG).Entry p.eP p.zP := ⟨rfl,rfl⟩

theorem root_cells {y : Cell n} : y∈(p.root k hW hT G hG).cells ↔ y≠p.eP ∧ y≠p.zP := by
  change y∈(p.rootSpec k hW hT G hG).frame.cells ↔ _
  rw [StarSpec.frame_cells]
  simp only [mem_union]
  constructor
  · rintro ((h | h) | h)
    · simp only [StarSpec.childCells,mem_biUnion,mem_univ,true_and] at h
      obtain ⟨j,hj⟩ := h
      have := p.c_lt10; have := p.two_le_c
      have h0 : p.c-2<p.N := by omega
      have h1 : p.c-1<p.N := by omega
      exact ⟨fun e => p.mid_notChild _ (p.kid_cells k hW hT G hG) h0 j (by have : p.eP=p.mid (p.c-2) := rfl; rw [←this,←e]; exact hj),
        fun e => p.mid_notChild _ (p.kid_cells k hW hT G hG) h1 j (by have : p.zP=p.mid (p.c-1) := rfl; rw [←this,←e]; exact hj)⟩
    · have := (p.mem_own _).mp h; exact ⟨this.2.2.1,this.2.2.2⟩
    · have := p.c_lt10; have := p.two_le_c
      obtain ⟨i,hi,rfl⟩ := p.mem_markers.mp h
      exact ⟨fun e => by have := p.mid_inj (by omega) (by omega) e; omega,
        fun e => by have := p.mid_inj (by omega) (by omega) e; omega⟩
  · rintro ⟨h1,h2⟩
    by_cases hc : y∈(p.rootSpec k hW hT G hG).childCells
    · exact Or.inl (Or.inl hc)
    by_cases hm : y∈p.markers
    · exact Or.inr hm
    refine Or.inl (Or.inr ((p.mem_own _).mpr ⟨fun j hj => hc ?_,hm,h1,h2⟩))
    simp only [StarSpec.childCells,mem_biUnion,mem_univ,true_and]; exact ⟨j,hj⟩

theorem root_spare : (p.root k hW hT G hG).spareCells=p.markers := rfl

theorem root_homes {y : Cell n} :
    y∈(p.root k hW hT G hG).coreCells∪(p.root k hW hT G hG).reserveCells ↔
      y≠p.eP ∧ y≠p.zP ∧ y∉p.markers := by
  have hc := p.root_cells k hW hT G hG (y:=y)
  have d1 := (p.root k hW hT G hG).core_spare
  have d2 := (p.root k hW hT G hG).reserve_spare
  rw [root_spare] at d1 d2
  simp only [Frame.cells,mem_union] at hc ⊢
  constructor
  · intro h
    have hm : y∉p.markers := by
      rcases h with h | h
      · exact disjoint_left.mp d1 h
      · exact disjoint_left.mp d2 h
    have := hc.mp (Or.inl h)
    exact ⟨this.1,this.2,hm⟩
  · rintro ⟨h1,h2,h3⟩
    rcases hc.mpr ⟨h1,h2⟩ with h | h
    · exact h
    · exact absurd (by rwa [root_spare] at h) h3

theorem root_prepared (B : Board n) (h : ∀ y, y≠p.eP → y≠p.zP → B y≠0) :
    (p.root k hW hT G hG).Prepared B := by
  have hc : ∀ y∈(p.root k hW hT G hG).cells, B y≠0 := fun y hy =>
    h y ((p.root_cells k hW hT G hG).mp hy).1 ((p.root_cells k hW hT G hG).mp hy).2
  refine ⟨hc,fun j => (p.kid k hW hT G hG j).prep B (fun y hy => hc y ?_)⟩
  change y∈(p.rootSpec k hW hT G hG).frame.cells
  rw [StarSpec.frame_cells]
  simp only [mem_union,StarSpec.childCells,mem_biUnion,mem_univ,true_and]
  exact Or.inl (Or.inl ⟨j,hy⟩)

end CParams
end SlidingPuzzle.NestedRouting.Central
