import NestedRouting.Central.Budget
import NestedRouting.Interface.Driver
import NestedRouting.Moves.MarkedCleanup
import NestedRouting.Moves.CanonicalReduction
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The end-to-end canonical bound. From any reachable board:
1. walk the blank to the root's `zP` (at most `2n`);
2. gather the seven non-goal tiles of the relabelled goal `G′` and the
   blank onto the markers and the entry pair (at most `54n·8`);
3. run the root's feedback driver (at most its budget at lead one);
4. walk the blank to the target corner (at most `2n`);
5. clean the residual support, at most `2n+9` cells (at most `54n` each).
`G′` is the target with `zP` and the corner exchanged, so its blank is
at `zP`, outside every body. -/
namespace SlidingPuzzle.NestedRouting.Central
open Interface Placement Finset Corner

set_option linter.unusedSectionVars false

variable {n : Nat} [NeZero n]

/-- Large enough for the root parameters below. -/
def N0 (k : Consts) : Nat := 2*(k.Tmin+k.W+12)+6

/-- The root parameters for side `n`: `m = 2`, quadrants of side `(n-5)/2`. -/
def autoP (k : Consts) (n : Nat) (hn : N0 k≤n) : CParams n where
  T := (n-5)/2
  m := 2
  W := k.W
  N_le := by unfold N0 at hn; omega
  m_two := le_refl _
  W_two := by unfold Consts.W; have := k.b_two; omega
  T_big := by unfold N0 at hn; omega

namespace CParams
variable (p : CParams n)

/-- The target's blank cell. -/
def κ (hn : 2≤n) : Cell n := (⟨n-1,by omega⟩,⟨n-1,by omega⟩)

theorem target_κ (hn : 2≤n) : target n (κ hn)=0 := by
  have h1 : 1<n*n := by nlinarith
  have hprod : finProdFinEquiv (κ hn)=(⟨n*n-1,by omega⟩ : Fin (n*n)) := by
    apply Fin.ext
    simp only [finProdFinEquiv_apply_val,κ]
    have : n*(n-1)=n*n-n := Nat.mul_sub_one n n
    have : n≤n*n := Nat.le_mul_self n
    omega
  have hrot : finRotate (n*n) (⟨n*n-1,by omega⟩ : Fin (n*n))=0 := by
    rw [finRotate_apply]
    apply Fin.ext
    simp only [Fin.val_add,Fin.val_zero]
    rw [Fin.val_one',Nat.mod_eq_of_lt h1,show n*n-1+1=n*n from by omega,Nat.mod_self]
  simp only [target,Equiv.trans_apply,hprod,hrot]

theorem blank_target (hn : 2≤n) : blank (target n)=κ hn :=
  (target n).injective ((target n).apply_symm_apply 0 |>.trans (target_κ hn).symm)

theorem target_eq_zero {y : Cell n} (hn : 2≤n) (h : target n y=0) : y=κ hn :=
  (target n).injective (h.trans (target_κ hn).symm)

theorem mid_val {c0 : Nat} (h : c0<p.N) : (p.mid c0).1.val=p.c ∧ (p.mid c0).2.val=c0 :=
  ⟨p.q0_row (by have := p.c_lt; omega) h,p.q0_col (by have := p.c_lt; omega) h⟩

theorem zP_ne_κ (hn : 2≤n) : p.zP≠κ hn := by
  intro h
  have := (p.mid_val (c0:=p.c-1) (by have := p.c_lt; omega)).1
  have h1 : (p.zP).1.val=n-1 := by rw [h]; rfl
  have := p.N_le; have := p.T_big
  change (p.mid (p.c-1)).1.val=_ at h1
  unfold c at *; omega

/-- The relabelled goal. -/
def G' (hn : 2≤n) : Board n := (Equiv.swap p.zP (κ hn)).trans (target n)

theorem G'_ne (hn : 2≤n) : ∀ y, y≠p.zP → p.G' hn y≠0 := by
  intro y hy h0
  have := target_eq_zero hn h0
  simp only [Equiv.swap_apply_def] at this
  split_ifs at this with h1 h2
  · exact hy h1
  · exact p.zP_ne_κ hn this
  · exact h2 this

theorem G'_zP (hn : 2≤n) : p.G' hn p.zP=0 := by
  simp [G',Equiv.swap_apply_left,target_κ]

theorem G'_eq (hn : 2≤n) {y : Cell n} (h1 : y≠p.zP) (h2 : y≠κ hn) : p.G' hn y=target n y := by
  simp [G',Equiv.swap_apply_of_ne_of_ne h1 h2]

theorem blank_eq {C : Board n} {y : Cell n} (h : C y=0) : blank C=y := by
  unfold blank position; rw [←h]; simp

variable (k : Consts) (hW : p.W=k.W) (hT : k.Tmin≤p.T) (hn : 2≤n)

/-- A residual set: the gathered cells, the corner, the blank's column and the last row. -/
def resid : Finset (Cell n) :=
  insert p.eP (insert p.zP p.markers)∪insert (κ hn) (univ.filter (fun x : Cell n => x.2=p.zP.2 ∨ x.1=(κ hn).1))

theorem resid_card : (p.resid hn).card≤8+1+(n+n) := by
  unfold resid
  have h1 : (insert p.eP (insert p.zP p.markers)).card≤8 := by
    have := card_insert_le p.eP (insert p.zP p.markers)
    have := card_insert_le p.zP p.markers
    rw [p.markers_card] at *; omega
  have h2 : (univ.filter (fun x : Cell n => x.2=p.zP.2 ∨ x.1=(κ hn).1)).card≤n+n := by
    rw [filter_or]
    refine (card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
    · have : univ.filter (fun x : Cell n => x.2=p.zP.2)=(univ : Finset (Fin n))×ˢ{p.zP.2} := by
        ext ⟨a,b⟩; simp [eq_comm]
      rw [this,card_product]; simp
    · have : univ.filter (fun x : Cell n => x.1=(κ hn).1)={(κ hn).1}×ˢ(univ : Finset (Fin n)) := by
        ext ⟨a,b⟩; simp [eq_comm]
      rw [this,card_product]; simp
  have := card_union_le (insert p.eP (insert p.zP p.markers))
    (insert (κ hn) (univ.filter (fun x : Cell n => x.2=p.zP.2 ∨ x.1=(κ hn).1)))
  have := card_insert_le (κ hn) (univ.filter (fun x : Cell n => x.2=p.zP.2 ∨ x.1=(κ hn).1))
  omega

local notation "R0" => p.root k hW hT (p.G' hn) (p.G'_ne hn)

theorem solve (B : Board n) (hB : Reachable B) :
    ∃ path : Path B (target n), path.length≤2*n+54*n*8+(R0).budget 1+2*n+54*n*(8+1+(n+n)) := by
  have hn6 : 6≤n := by have := p.N_le; have := p.T_big; omega
  have S := p.rootSpec k hW hT (p.G' hn) (p.G'_ne hn)
  have heZ : p.eP≠p.zP := (p.rootSpec k hW hT (p.G' hn) (p.G'_ne hn)).eP_zP
  have heM : p.eP∉p.markers := (p.rootSpec k hW hT (p.G' hn) (p.G'_ne hn)).eP_markers
  have hzM : p.zP∉p.markers := (p.rootSpec k hW hT (p.G' hn) (p.G'_ne hn)).zP_markers
  -- 1. blank to zP
  obtain ⟨C1,p1,hb1,hl1,-⟩ := exists_blank_access_path_elbow B p.zP
  -- 2. gather
  let R : Finset (Cell n) := insert p.eP (insert p.zP p.markers)
  let Mk : Finset (Tile n) := insert 0 ((insert p.eP p.markers).image (p.G' hn))
  have hR : R.card=8 := by
    rw [card_insert_of_notMem (by simp [heZ,heM]),card_insert_of_notMem hzM,p.markers_card]
  have hMk : Mk.card=8 := by
    rw [card_insert_of_notMem,card_image_of_injective _ (p.G' hn).injective,
      card_insert_of_notMem heM,p.markers_card]
    rw [mem_image]; rintro ⟨y,hy,h0⟩
    apply p.G'_ne hn y _ h0
    rintro rfl
    rcases mem_insert.mp hy with h | h
    · exact heZ h.symm
    · exact hzM h
  have hsmall : 2*R.card<n*n := by rw [hR]; nlinarith
  obtain ⟨C2,p2,hl2,hb2,hM⟩ := MarkedCleanup.exists_gather_marked_card C1 hn6 Mk R (by rw [hR,hMk])
    (mem_insert_self _ _) (by rw [hb1]; simp [R]) hsmall
  rw [hR] at hl2
  have hb2' : blank C2=p.zP := hb2.trans hb1
  -- 3. drive the root
  have prep : (R0).Prepared C2 := by
    apply p.root_prepared
    intro y h1 h2 h0
    exact h2 ((blank_eq h0).symm.trans hb2')
  have hgoals : ∀ x∈(R0).coreCells∪(R0).reserveCells, C2 x∈(R0).Goals := by
    intro x hx
    obtain ⟨x1,x2,x3⟩ := (p.root_homes k hW hT (p.G' hn) (p.G'_ne hn)).mp hx
    have hxR : x∉R := by simp [R,x1,x2,x3]
    have hnot : C2 x∉Mk := fun h => hxR ((hM x).mp h)
    set y := (p.G' hn).symm (C2 x) with hy
    have hGy : p.G' hn y=C2 x := by rw [hy]; simp
    have hyh : y∈(R0).coreCells∪(R0).reserveCells := by
      apply (p.root_homes k hW hT (p.G' hn) (p.G'_ne hn)).mpr
      refine ⟨?_,?_,?_⟩
      · intro h; rw [h] at hGy
        exact hnot (mem_insert_of_mem (mem_image.mpr ⟨_,mem_insert_self _ _,hGy⟩))
      · intro h; rw [h,p.G'_zP] at hGy; exact hnot (by rw [←hGy]; exact mem_insert_self _ _)
      · intro hm; exact hnot (mem_insert_of_mem (mem_image.mpr ⟨_,mem_insert_of_mem hm,hGy⟩))
    rw [←hGy]
    unfold Region.Goals Frame.coreGoals Frame.reserveGoals
    rw [←image_union]
    exact mem_image.mpr ⟨y,hyh,rfl⟩
  have hpos : 0<(R0).M+(R0).r := by
    have hc : p.mid p.c∈(R0).coreCells∪(R0).reserveCells := by
      have := p.c_lt10; have := p.two_le_c
      apply (p.root_homes k hW hT (p.G' hn) (p.G'_ne hn)).mpr
      refine ⟨fun h => ?_,fun h => ?_,fun h => ?_⟩
      · have := p.mid_inj (by omega) (by omega) h; omega
      · have := p.mid_inj (by omega) (by omega) h; omega
      · obtain ⟨i,hi,e⟩ := p.mem_markers.mp h
        have := p.mid_inj (by omega) (by omega) e; omega
    have := card_pos.mpr ⟨_,hc⟩
    rw [card_union_of_disjoint (R0).core_reserve] at this
    exact this
  obtain ⟨C3,p3,hl3,hb3,-,hpl⟩ := (R0).drive (p.root_entry k hW hT (p.G' hn) (p.G'_ne hn)) hb2' prep
    hgoals hpos
  -- 4. blank to the corner
  obtain ⟨C4,p4,hb4,hl4,hfix4⟩ := exists_blank_access_path_elbow C3 (κ hn)
  -- 5. cleanup
  have hfix : ∀ x, x∉p.resid hn → C4 x=target n x := by
    intro x hx
    simp only [resid,mem_union,mem_insert,mem_filter,mem_univ,true_and,not_or] at hx
    obtain ⟨⟨x1,x2,x3⟩,x4,x5,x6⟩ := hx
    rw [hfix4 x (by rw [hb3]; exact x5) x6]
    have hh : x∈(R0).coreCells∪(R0).reserveCells :=
      (p.root_homes k hW hT (p.G' hn) (p.G'_ne hn)).mpr ⟨x1,x2,x3⟩
    rw [hpl x hh]
    exact p.G'_eq hn x2 x4
  have reach := MarkedCleanup.reachable_after_path hB (p1.append (p2.append (p3.append p4)))
  have hblank : blank C4=blank (target n) := hb4.trans (blank_target hn).symm
  obtain ⟨p5,hl5⟩ := MarkedCleanup.exists_reserve_cleanup C4 hn6 reach hblank (p.resid hn) hfix
  refine ⟨p1.append (p2.append (p3.append (p4.append p5))),?_⟩
  simp only [Path.length_append]
  have := Nat.mul_le_mul_left (54*n) (p.resid_card hn)
  omega

end CParams

/-- The root's cost per board cell, for `m = 2`, `W = k.W`. -/
def CrootK (k : Consts) : Nat := 394+374+8*(4*2+2*k.W+5)+25*(4*2+2*k.W+5)

/-- The root's cost per unit of side, for `m = 2`. -/
def ClinK (k : Consts) : Nat := 16*2*394+4*394+8*(2*2+3)+2+k.Kr*(16*2+12)+150+276*(4*2+2*k.W+5)+
  3*394+3*k.Kr+658

/-- Coefficient of `n²·log_b n`: the per-level overhead of a corner star. -/
def C1 (k : Consts) : Nat := k.K0

/-- Coefficient of `n²`: leaves, the root (its linear part absorbed using
`n ≥ N0`), and the end-to-end preparation. -/
def C2 (k : Consts) : Nat := k.Kl+CrootK k+Ledger.cdiv (ClinK k+922) (N0 k)+108

theorem autoP_Croot (k : Consts) (n : Nat) [NeZero n] (hn : N0 k≤n) : (autoP k n hn).Croot=CrootK k := by
  simp only [CParams.Croot,CParams.X,CParams.cR,autoP,CrootK]

theorem autoP_Clin (k : Consts) (n : Nat) [NeZero n] (hn : N0 k≤n) : (autoP k n hn).Clin k=ClinK k := by
  simp only [CParams.Clin,CParams.X,CParams.cR,autoP,ClinK]

/-- **Canonical bound.** For `n ≥ N0 k`, every reachable board reaches the
target in at most `n³ + C1·n²·d + C2·n²` slides, where `d ≤ log_b n` is the
depth of the quadrant trees. -/
theorem canonical (k : Consts) (n : Nat) [NeZero n] (hn : N0 k≤n) (B : Board n) (hB : Reachable B) :
    ∃ path : Path B (target n), path.length≤n^3+C1 k*n^2*k.dep ((n-5)/2)+C2 k*n^2 := by
  set p := autoP k n hn with hp
  have hW : p.W=k.W := rfl
  have hT : k.Tmin≤p.T := by show k.Tmin≤(n-5)/2; unfold N0 at hn; omega
  have hn2 : 2≤n := by unfold N0 at hn; omega
  have hN : n≤p.N+1 := by show n≤2*((n-5)/2)+2*2+1+1; omega
  obtain ⟨path,hl⟩ := p.solve k hW hT hn2 B hB
  have hb := p.root_budget k hW hT (p.G' hn2) (p.G'_ne hn2) hN
  rw [autoP_Croot k n hn,autoP_Clin k n hn] at hb
  refine ⟨path,hl.trans ?_⟩
  have hTn : 2*p.T≤n := by show 2*((n-5)/2)≤n; omega
  have hT3 : 8*(p.T*(p.T*(p.T-1)))≤n^3 := by
    have : p.T*(p.T*(p.T-1))≤p.T*(p.T*p.T) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    have : (2*p.T)*((2*p.T)*(2*p.T))≤n*(n*n) := Nat.mul_le_mul hTn (Nat.mul_le_mul hTn hTn)
    have e : n^3=n*(n*n) := by ring
    nlinarith
  have hdep : k.dep p.T≤k.dep ((n-5)/2) := le_rfl
  set L := k.dep ((n-5)/2)
  -- four quadrants of side `T` with `2T ≤ n`
  have h4T : 4*(p.T*p.T)≤n^2 := by
    have := Nat.mul_le_mul hTn hTn
    rw [sq]; nlinarith
  have hK : 4*(k.Kl*(p.T*p.T)+k.K0*(p.T*p.T)*k.dep p.T)≤k.Kl*n^2+C1 k*n^2*L := by
    have a1 : 4*(k.Kl*(p.T*p.T))≤k.Kl*n^2 := by
      calc 4*(k.Kl*(p.T*p.T))=k.Kl*(4*(p.T*p.T)) := by ring
        _≤_ := Nat.mul_le_mul_left _ h4T
    have a2 : 4*(k.K0*(p.T*p.T)*k.dep p.T)≤C1 k*n^2*L := by
      calc 4*(k.K0*(p.T*p.T)*k.dep p.T)=k.K0*(4*(p.T*p.T))*k.dep p.T := by ring
        _≤k.K0*n^2*L := Nat.mul_le_mul (Nat.mul_le_mul_left _ h4T) hdep
    have e : 4*(k.Kl*(p.T*p.T)+k.K0*(p.T*p.T)*k.dep p.T)=
        4*(k.Kl*(p.T*p.T))+4*(k.K0*(p.T*p.T)*k.dep p.T) := by ring
    omega
  have hC : CrootK k*(n*n)=CrootK k*n^2 := by rw [sq]
  have hlin : (ClinK k+922)*n≤Ledger.cdiv (ClinK k+922) (N0 k)*n^2 := by
    have h0 : 0<N0 k := by unfold N0; omega
    have h1 := Ledger.le_mul_cdiv (x:=ClinK k+922) h0
    calc (ClinK k+922)*n≤N0 k*Ledger.cdiv (ClinK k+922) (N0 k)*n := Nat.mul_le_mul_right _ h1
      _≤n*Ledger.cdiv (ClinK k+922) (N0 k)*n := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hn)
      _=_ := by ring
  have hsmall : 2*n+54*n*8+2*n+54*n*(8+1+(n+n))=108*n^2+922*n := by ring
  have e : C2 k*n^2=k.Kl*n^2+CrootK k*n^2+Ledger.cdiv (ClinK k+922) (N0 k)*n^2+108*n^2 := by
    unfold C2; ring
  have e2 : (ClinK k+922)*n=ClinK k*n+922*n := by ring
  omega

/-- **God's number.** For every `n ≥ N0 k` and mutually reachable boards `B, T`,
some path joins them in at most `n³ + C1·n²·log_b n + (C2+2)·n²` slides. -/
theorem pair_bound_of (k : Consts) (n : Nat) [NeZero n] (hn : N0 k≤n) (B T : Board n)
    (reach : Nonempty (Path B T)) :
    ∃ path : Path B T, path.length≤n^3+C1 k*n^2*k.dep ((n-5)/2)+(C2 k+2)*n^2 := by
  have solver : ∀ A : Board n, Reachable A →
      ∃ p : Path A (target n), (p.length : Real)≤((n^3+C1 k*n^2*k.dep ((n-5)/2)+C2 k*n^2 : Nat) : Real) := by
    intro A hA
    obtain ⟨p,hp⟩ := canonical k n hn A hA
    exact ⟨p,by exact_mod_cast hp⟩
  obtain ⟨path,hl⟩ := pair_bound_of_canonical _ solver B T reach
  refine ⟨path,?_⟩
  have h2 : 2*n≤2*n^2 := by
    have : n≤n^2 := by rw [sq]; exact Nat.le_mul_of_pos_right n (Nat.pos_of_ne_zero (NeZero.ne n))
    omega
  have : (path.length : Real)≤((n^3+C1 k*n^2*k.dep ((n-5)/2)+C2 k*n^2+2*n : Nat) : Real) := by
    push_cast at hl ⊢; linarith
  have h3 : path.length≤n^3+C1 k*n^2*k.dep ((n-5)/2)+C2 k*n^2+2*n := by exact_mod_cast this
  have e : (C2 k+2)*n^2=C2 k*n^2+2*n^2 := by ring
  omega

theorem std_N0 : N0 std=256 := by decide
theorem std_C1 : C1 std=4570 := by decide
theorem std_C2 : C2 std=10659 := by decide

/-- `ln 3 > 1.098546`, from `3¹² > 2¹⁹` and `ln x ≥ 1 - 1/x`. -/
theorem log3_gt : (1.098546 : ℝ)<Real.log 3 := by
  have e : Real.log ((3:ℝ)^12)=Real.log ((2:ℝ)^19)+Real.log (531441/524288) := by
    rw [←Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [Real.log_pow,Real.log_pow] at e
  have hl := Real.one_sub_inv_le_log_of_pos (x:=(531441:ℝ)/524288) (by norm_num)
  have h2 := Real.log_two_gt_d9
  push_cast at e
  norm_num at hl
  linarith

/-- `log₃ 722 > 5.99117`, from `ln(722/729) ≥ 1 - 729/722`. -/
theorem log722_gt : (5.99117 : ℝ)*Real.log 3<Real.log 722 := by
  have e : Real.log 722=Real.log ((3:ℝ)^6)+Real.log (722/729) := by
    rw [←Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [Real.log_pow] at e
  have hl := Real.one_sub_inv_le_log_of_pos (x:=(722:ℝ)/729) (by norm_num)
  have h3 := log3_gt
  norm_num at hl
  push_cast at e
  nlinarith

/-- The depth of the quadrant trees, against the natural logarithm: stars
have side at least `Tbig = 361`, so `d ≤ log₃(n/722) + 1`, and
`4570·d ≤ 4161·ln n - 22809`. -/
theorem dep_le (n : Nat) (hn : 256≤n) : (4570*std.dep ((n-5)/2) : ℝ)≤4161*Real.log n-22809 := by
  have h3 := log3_gt
  have hpos : 0<Real.log 3 := by linarith
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  -- `ln n ≥ ln 243 = 5 ln 3`
  have hlog : 5*Real.log 3≤Real.log n := by
    have h243 : ((243:Nat) : ℝ)≤(n : ℝ) := by exact_mod_cast (show 243≤n by omega)
    have := Real.log_le_log (x:=(3:ℝ)^5) (y:=(n:ℝ)) (by norm_num) (by push_cast at h243; norm_num; linarith)
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hTb : std.Tbig=361 := rfl
  have hb : std.b=3 := rfl
  by_cases h : std.Tbig≤(n-5)/2
  · have hd := std.dep_le_log_div ((n-5)/2) h
    rw [hTb,hb] at hd
    set m := (n-5)/2/361 with hm
    have m1 : 1≤m := by rw [hTb] at h; omega
    have m722 : 722*m≤n := by omega
    have hd' : (std.dep ((n-5)/2) : ℝ)≤Real.logb 3 m+1 := by
      have : (Nat.log 3 m : ℝ)≤Real.logb 3 m := by exact_mod_cast Real.natLog_le_logb m 3
      have : (std.dep ((n-5)/2) : ℝ)≤(Nat.log 3 m : ℝ)+1 := by exact_mod_cast hd
      linarith
    have hm0 : (0:ℝ)<m := by exact_mod_cast (show 0<m by omega)
    have hlm : Real.log m≤Real.log n-Real.log 722 := by
      rw [←Real.log_div (by positivity) (by norm_num)]
      apply Real.log_le_log hm0
      rw [le_div_iff₀ (by norm_num)]
      have : ((722*m : Nat) : ℝ)≤(n : ℝ) := by exact_mod_cast m722
      push_cast at this; linarith
    have e : Real.logb 3 m*Real.log 3=Real.log m := by unfold Real.logb; field_simp
    have h722 := log722_gt
    have key : (std.dep ((n-5)/2) : ℝ)*Real.log 3≤Real.log n-4.99117*Real.log 3 := by
      nlinarith
    -- `4570/ln 3 ≤ 4161`
    have hn1 : 0≤Real.log n := by linarith
    nlinarith
  · rw [std.dep_leaf h]
    simp only [Nat.cast_zero,mul_zero]
    nlinarith

/-- **God's number, explicitly.** For `n ≥ 256`, any two mutually reachable
`n × n` boards are joined by a path of at most
`n³ + 4161·n²·ln n - 12148·n²` slides. -/
theorem pair_bound : ∀ (n : Nat) [NeZero n], 256≤n → ∀ B T : Board n, Nonempty (Path B T) →
    ∃ path : Path B T, (path.length : ℝ)≤n^3+4161*n^2*Real.log n-12148*n^2 := by
  intro n _ hn B T reach
  obtain ⟨path,hl⟩ := pair_bound_of std n (by rw [std_N0]; exact hn) B T reach
  refine ⟨path,?_⟩
  rw [std_C1,std_C2] at hl
  have hl' : (path.length : ℝ)≤n^3+4570*n^2*std.dep ((n-5)/2)+(10659+2)*n^2 := by exact_mod_cast hl
  have key := dep_le n hn
  have hn2 : (0 : ℝ)≤(n : ℝ)^2 := by positivity
  have : (4570 : ℝ)*n^2*std.dep ((n-5)/2)≤n^2*(4161*Real.log n-22809) := by
    calc (4570 : ℝ)*n^2*std.dep ((n-5)/2)=n^2*(4570*std.dep ((n-5)/2)) := by ring
      _≤_ := mul_le_mul_of_nonneg_left key hn2
  nlinarith

end SlidingPuzzle.NestedRouting.Central
