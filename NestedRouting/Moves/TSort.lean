import NestedRouting.Moves.GoalCompletion

/-! Sorting by `t`-cycles. With the blank parked at `s = (1,0)` of a frame,
the block cells `p = (0,0)` and `q = (0,1)` serve as a two-cell buffer: when
the buffer holds the goal tile of a cell `y`, one `t`-cycle puts it there;
when it holds only its own tiles, one `t`-cycle loads the misplaced tile of
least weight into it, and the next `t`-cycle places that tile, at a cell of
at least that weight. A misplaced cell is charged three halves of its weight,
or one if it holds a buffer tile, so `R` is sorted within `(3/2)·Σ_R w`. Parity is settled as in
`LocalBlockFinish`, by two cells of `R` with interchangeable goals; the
buffer then ends restored. -/
namespace SlidingPuzzle.NestedRouting.Cycle3
open Finset Routes MarkedCleanup

variable {n : Nat} [NeZero n] (F : Frame n)

/-- A cell of the frame outside its block. -/
def Out (x : Cell n) : Prop := ∃ r c, r<F.R ∧ c<F.C ∧ (2≤r ∨ 2≤c) ∧ F.loc r c=x

section
variable {F} (hR : 3≤F.R) (hC : 6≤F.C) (G : Board n) (R : Finset (Cell n)) (hRF : ∀ x∈R, Out F x)
  (w : Cell n → Nat) (hw : ∀ x∈R, ∀ r c, r<F.R → c<F.C → F.loc r c=x → tw r c+2≤w x)

open Classical in
/-- Twice the charge of a misplaced cell: twice its weight if it holds a
buffer tile (one that belongs to `p` or `q`), three times otherwise. -/
noncomputable def term (F : Frame n) (G : Board n) (w : Cell n → Nat) (B : Board n) (x : Cell n) : Nat :=
  if G.symm (B x)=F.loc 0 0 ∨ G.symm (B x)=F.loc 0 1 then 2*w x else 3*w x

open Classical in
/-- The potential: the charges of the misplaced cells of `R`. -/
noncomputable def psi (F : Frame n) (G : Board n) (R : Finset (Cell n)) (w : Cell n → Nat) (B : Board n) : Nat :=
  ∑ x∈R.filter (fun x => B x≠G x), term F G w B x

omit [NeZero n] in
include hR hC hRF in
theorem out_ne {x : Cell n} (hx : x∈R) {i j : Nat} (hi : i<2) (hj : j<2) : x≠F.loc i j := by
  obtain ⟨r,c,hr,hc,o,rfl⟩ := hRF x hx
  exact ne_loc F hr hc (by omega) (by omega) (by omega)

/-- The invariant of the sort: blank at `s`, even sign, `G` off `R` and the buffer. -/
def Ready (F : Frame n) (G : Board n) (R : Finset (Cell n)) (B : Board n) : Prop :=
  blank B=F.loc 1 0 ∧ relativeSign B G=1 ∧ ∀ x, x∉R → x≠F.loc 0 0 → x≠F.loc 0 1 → B x=G x

include hR hC hRF hw in
/-- A `t`-cycle at a cell `y` of `R`, in either direction. -/
theorem tcyc (B : Board n) (hB : Ready F G R B) (y : Cell n) (hy : y∈R) (plus : Bool) :
    ∃ C : Board n, ∃ path : Path B C, 2≤w y ∧ path.length≤w y ∧ Ready F G R C ∧
      IsCycle B C y (if plus then F.loc 0 0 else F.loc 0 1) (if plus then F.loc 0 1 else F.loc 0 0) := by
  obtain ⟨hb,hsign,hout⟩ := hB
  obtain ⟨r,c,hr,hc,o,rfl⟩ := hRF y hy
  obtain ⟨C,path,len,bC,h⟩ := tcycle_s_at F hR hC B hb r c hr hc o plus
  have hwy := hw _ hy r c hr hc rfl
  refine ⟨C,path,by omega,by omega,⟨bC,?_,?_⟩,h⟩
  · rw [relativeSign_after_closed_path G path (bC.trans hb.symm),hsign]
  · intro x hx xp xq
    have xy : x≠F.loc r c := fun e => hx (e ▸ hy)
    rw [h.2.2.2 x xy (by cases plus <;> simpa using (by first | exact xp | exact xq))
      (by cases plus <;> simpa using (by first | exact xq | exact xp))]
    exact hout x hx xp xq

omit [NeZero n] in
/-- Placing a tile at `y`: the cell leaves the misplaced set. -/
theorem place (B C : Board n) (y : Cell n) (hy : y∈R) (hCy : C y=G y) (hBy : B y≠G y)
    (fix : ∀ x∈R, x≠y → C x=B x) : psi F G R w C+term F G w B y=psi F G R w B := by
  classical
  have eq : R.filter (fun x => C x≠G x)=(R.filter (fun x => B x≠G x)).erase y := by
    ext x
    simp only [mem_filter,mem_erase]
    constructor
    · rintro ⟨hx,hne⟩
      have xy : x≠y := fun e => hne (e ▸ hCy)
      exact ⟨xy,hx,by rw [←fix x hx xy]; exact hne⟩
    · rintro ⟨xy,hx,hne⟩
      exact ⟨hx,by rw [fix x hx xy]; exact hne⟩
  have mem : y∈R.filter (fun x => B x≠G x) := mem_filter.mpr ⟨hy,hBy⟩
  unfold psi
  rw [eq,←add_sum_erase _ _ mem]
  have : ∑ x∈(R.filter (fun x => B x≠G x)).erase y, term F G w C x=
      ∑ x∈(R.filter (fun x => B x≠G x)).erase y, term F G w B x := by
    apply sum_congr rfl
    intro x hx
    have := (mem_erase.mp hx)
    unfold term; rw [fix x (mem_filter.mp this.2).1 this.1]
  rw [this]
  omega

include hR hC hRF hw in
/-- One or two `t`-cycles lower twice the potential by at least twice their length. -/
theorem tsort_step (B : Board n) (hB : Ready F G R B) (hne : B≠G) :
    ∃ C : Board n, ∃ path : Path B C, psi F G R w C<psi F G R w B ∧
      2*path.length+psi F G R w C≤psi F G R w B ∧ Ready F G R C := by
  classical
  obtain ⟨hb,hsign,hout⟩ := hB
  set p := F.loc 0 0 with hp
  set q := F.loc 0 1 with hq
  have pq : p≠q := ne_loc F (by omega) (by omega) (by omega) (by omega) (by omega)
  have inR (x : Cell n) (hx : x∈R) : x≠p ∧ x≠q :=
    ⟨out_ne hR hC R hRF hx (by omega) (by omega),out_ne hR hC R hRF hx (by omega) (by omega)⟩
  have tge (D : Board n) (y : Cell n) : 2*w y≤term F G w D y := by unfold term; split_ifs <;> omega
  by_cases hA : ∃ y∈R, G y=B p
  · obtain ⟨y,hy,hgy⟩ := hA
    obtain ⟨C,path,pos,len,rC,h⟩ := tcyc hR hC G R hRF w hw B ⟨hb,hsign,hout⟩ y hy true
    simp only [if_true] at h
    have hBy : B y≠G y := fun e => (inR y hy).1 (B.injective (e.trans hgy))
    have := place (F:=F) G R w B C y hy (h.1.trans hgy.symm) hBy
      (fun x hx xy => h.2.2.2 x xy (inR x hx).1 (inR x hx).2)
    have := tge B y
    exact ⟨C,path,by omega,by omega,rC⟩
  by_cases hB' : ∃ y∈R, G y=B q
  · obtain ⟨y,hy,hgy⟩ := hB'
    obtain ⟨C,path,pos,len,rC,h⟩ := tcyc hR hC G R hRF w hw B ⟨hb,hsign,hout⟩ y hy false
    simp only [Bool.false_eq_true,if_false] at h
    have hBy : B y≠G y := fun e => (inR y hy).2 (B.injective (e.trans hgy))
    have := place (F:=F) G R w B C y hy (h.1.trans hgy.symm) hBy
      (fun x hx xy => h.2.2.2 x xy (inR x hx).2 (inR x hx).1)
    have := tge B y
    exact ⟨C,path,by omega,by omega,rC⟩
  -- the buffer is idle: its tiles belong to the buffer
  have hA := hA; have hB := hB'
  push Not at hA hB
  have own (t : Cell n) (ht : t=p ∨ t=q) (hR' : ∀ y∈R, G y≠B t) : G.symm (B t)=p ∨ G.symm (B t)=q := by
    set w := G.symm (B t) with hw
    have gw : G w=B t := by rw [hw]; simp
    by_contra hpq
    push Not at hpq
    have wR : w∉R := fun h => hR' w h gw
    have := hout w wR hpq.1 hpq.2
    have wt : w=t := B.injective (this.trans gw)
    rcases ht with rfl | rfl
    · exact hpq.1 wt
    · exact hpq.2 wt
  have ownP := own p (Or.inl rfl) hA
  have ownQ := own q (Or.inr rfl) hB
  -- some cell of `R` is misplaced, by parity
  obtain ⟨x,hx,hBx⟩ : ∃ x∈R, B x≠G x := by
    by_contra hall
    push Not at hall
    have sub : relativeSupport B G⊆{p,q} := by
      intro y hy
      have hy' := (mem_relativeSupport B G y).mp hy
      by_cases yR : y∈R
      · exact absurd (hall y yR) hy'
      by_cases yp : y=p
      · simp [yp]
      by_cases yq : y=q
      · simp [yq]
      exact absurd (hout y yR yp yq) hy'
    have hpos : 0<(relativeSupport B G).card := by
      obtain ⟨y,hy⟩ : ∃ y, B y≠G y := by
        by_contra h; push Not at h; exact hne (Equiv.ext h)
      exact card_pos.mpr ⟨y,(mem_relativeSupport B G y).mpr hy⟩
    have h3 := relativeSupport_three_le B G hsign hpos
    have h2 := card_le_card sub
    have : ({p,q} : Finset (Cell n)).card≤2 := card_le_two
    omega
  -- load the misplaced cell of least weight
  obtain ⟨x,hxM,xmin⟩ := (R.filter (fun y => B y≠G y)).exists_min_image w ⟨x,mem_filter.mpr ⟨hx,hBx⟩⟩
  have hx' : x∈R := (mem_filter.mp hxM).1
  have hBx' : B x≠G x := (mem_filter.mp hxM).2
  clear hx hBx
  obtain ⟨C,path,pos,len,rC,h⟩ := tcyc hR hC G R hRF w hw B ⟨hb,hsign,hout⟩ x hx' true
  simp only [if_true] at h
  have toG {t u : Cell n} (e : G.symm (B t)=u) : B t=G u := G.symm_apply_eq.mp e
  have hx := hx'
  -- the loaded tile belongs in `R`
  have loaded : G.symm (B x)∈R := by
    set y := G.symm (B x) with hy
    have gy : G y=B x := by rw [hy]; simp
    by_contra yR
    have xp := (inR x hx).1
    have xq := (inR x hx).2
    by_cases yp : y=p
    · rw [yp] at gy
      rcases ownP with e | e
      · exact xp (B.injective (gy.symm.trans (toG e).symm))
      · rcases ownQ with e' | e'
        · exact xq (B.injective (gy.symm.trans (toG e').symm))
        · exact pq (B.injective ((toG e).trans (toG e').symm))
    by_cases yq : y=q
    · rw [yq] at gy
      rcases ownQ with e | e
      · rcases ownP with e' | e'
        · exact pq (B.injective ((toG e').trans (toG e).symm))
        · exact xp (B.injective (gy.symm.trans (toG e').symm))
      · exact xq (B.injective (gy.symm.trans (toG e).symm))
    have := hout y yR yp yq
    have yx : y=x := B.injective (this.trans gy)
    exact yR (yx ▸ hx)
  have ownB (t : Tile n) (ht : G.symm t=p ∨ G.symm t=q) : t=B p ∨ t=B q := by
    have bpq : G.symm (B p)≠G.symm (B q) := fun e => pq (B.injective (G.symm.injective e))
    rcases ht with e | e <;> rcases ownP with e1 | e1 <;> rcases ownQ with e2 | e2
    all_goals first
      | exact Or.inl (G.symm.injective (e.trans e1.symm))
      | exact Or.inr (G.symm.injective (e.trans e2.symm))
      | exact absurd (e1.trans e2.symm) bpq
  have notOwn (y : Cell n) (hy : y∈R) : ¬(G.symm (B y)=p ∨ G.symm (B y)=q) := by
    intro ho
    rcases ownB _ ho with e | e
    · exact (inR y hy).1 (B.injective e)
    · exact (inR y hy).2 (B.injective e)
  have tB : term F G w B x=3*w x := by unfold term; rw [if_neg (notOwn x hx)]
  have tC : term F G w C x=2*w x := by
    unfold term
    rw [if_pos]; rw [h.1]; exact ownP
  have Cx : C x≠G x := by
    rw [h.1]; intro e
    rcases ownP with e' | e'
    · exact (inR x hx).1 (G.injective ((toG e').symm.trans e).symm)
    · exact (inR x hx).2 (G.injective ((toG e').symm.trans e).symm)
  have same (y : Cell n) (hy : y∈R) (yx : y≠x) : C y=B y := h.2.2.2 y yx (inR y hy).1 (inR y hy).2
  have eq : R.filter (fun y => C y≠G y)=R.filter (fun y => B y≠G y) := by
    ext y
    simp only [mem_filter]
    constructor
    · rintro ⟨hy,hne'⟩
      by_cases yx : y=x
      · subst yx; exact ⟨hy,hBx'⟩
      · exact ⟨hy,by rw [←same y hy yx]; exact hne'⟩
    · rintro ⟨hy,hne'⟩
      by_cases yx : y=x
      · subst yx; exact ⟨hy,Cx⟩
      · exact ⟨hy,by rw [same y hy yx]; exact hne'⟩
  have mem : x∈R.filter (fun y => B y≠G y) := hxM
  have rest : ∑ y∈(R.filter (fun y => B y≠G y)).erase x, term F G w C y=
      ∑ y∈(R.filter (fun y => B y≠G y)).erase x, term F G w B y := by
    apply sum_congr rfl
    intro y hy
    have := mem_erase.mp hy
    unfold term; rw [same y (mem_filter.mp this.2).1 this.1]
  have e1 : psi F G R w C+w x=psi F G R w B := by
    unfold psi; rw [eq,←add_sum_erase _ _ mem,tC,rest,←add_sum_erase _ _ mem,tB]; ring
  -- place the loaded tile at its goal `g`, which weighs at least as much
  set g := G.symm (B x) with hg
  have gx : g≠x := by
    intro e
    have e' : G.symm (B x)=x := e
    exact hBx' (G.symm_apply_eq.mp e')
  have Gg : G g=B x := by rw [hg]; simp
  have hBg : B g≠G g := by rw [Gg]; intro e; exact gx (B.injective e)
  have wxg : w x≤w g := xmin g (mem_filter.mpr ⟨loaded,hBg⟩)
  obtain ⟨D,path2,pos2,len2,rD,h2⟩ := tcyc hR hC G R hRF w hw C rC g loaded false
  simp only [Bool.false_eq_true,if_false] at h2
  have Cg : C g=B g := same g loaded gx
  have := place (F:=F) G R w C D g loaded (h2.1.trans (h.2.2.1.trans Gg.symm)) (by rw [Cg]; exact hBg)
    (fun y hy yg => h2.2.2.2 y yg (inR y hy).2 (inR y hy).1)
  have tg : term F G w C g=3*w g := by unfold term; rw [Cg,if_neg (notOwn g loaded)]
  refine ⟨D,path.append path2,by omega,?_,rD⟩
  rw [Path.length_append]
  omega

include hR hC hRF hw in
/-- Sorting: a board agreeing with `G` off `R` and the buffer, with the same
blank and an even relative sign, reaches `G` within half its potential. -/
theorem tsort : ∀ (B : Board n), Ready F G R B → ∃ path : Path B G, 2*path.length≤psi F G R w B := by
  intro B
  induction h : psi F G R w B using Nat.strong_induction_on generalizing B with
  | _ k ih =>
  intro hB
  by_cases hne : B=G
  · subst hne; exact ⟨Path.nil _,by simp⟩
  obtain ⟨C,path,lt,len,rC⟩ := tsort_step hR hC G R hRF w hw B hB hne
  obtain ⟨rest,hrest⟩ := ih (psi F G R w C) (h ▸ lt) C rfl rC
  refine ⟨path.append rest,?_⟩
  rw [Path.length_append]
  omega

omit [NeZero n] in
theorem psi_le (B : Board n) : psi F G R w B≤3*∑ x∈R, w x := by
  classical
  unfold psi
  rw [mul_sum]
  calc ∑ x∈R.filter (fun x => B x≠G x), term F G w B x≤∑ x∈R.filter (fun x => B x≠G x), 3*w x :=
        sum_le_sum (fun x _ => by unfold term; split_ifs <;> omega)
    _≤∑ x∈R, 3*w x := sum_le_sum_of_subset (filter_subset _ _)

end

/-- Finishing by `t`-cycles: place the goal tiles `T` on `Fx ⊆ R`, keep
everything off `R`, with the blank at `s`. -/
theorem exists_tfinish (hR : 3≤F.R) (hC : 6≤F.C) (B T : Board n) (hb : blank B=F.loc 1 0)
    (R Fx : Finset (Cell n)) (hRF : ∀ x∈R, Out F x) (w : Cell n → Nat)
    (hw : ∀ x∈R, ∀ r c, r<F.R → c<F.C → F.loc r c=x → tw r c+2≤w x) (inside : Fx⊆R)
    (hnonzero : ∀ x∈Fx, T x≠0) (hpresent : ∀ x∈Fx, ∃ y∈R, B y=T x) (room : Fx.card+3≤R.card) :
    ∃ C : Board n, ∃ path : Path B C,
      2*path.length≤3*∑ x∈R, w x ∧ blank C=blank B ∧
      (∀ x, x∉R → C x=B x) ∧ ∀ x∈Fx, C x=T x := by
  classical
  have blankR : blank B∉R := fun h => out_ne hR hC R hRF h (i:=1) (j:=0) (by omega) (by omega) hb
  have free : blank B∉Fx := fun h => blankR (inside h)
  obtain ⟨G,blankG,goals,support⟩ := LocalBlockFinish.exists_supported_goal B R Fx inside free T
    (fun x _ y _ e => T.injective e) hnonzero hpresent
  obtain ⟨a,b,haR,hbR,hab,haF,hbF,haB,hbB⟩ := LocalBlockFinish.exists_two_free_slots_in B R Fx room
  have nonblank (x : Cell n) (hx : x≠blank B) : G x≠0 := by
    intro zero
    apply hx
    rw [←blankG]
    apply G.injective
    simpa [blank,position] using zero
  obtain ⟨G',_,blank',sign',adjusted⟩ := exists_even_goal_adjustment B G a b hab
    (nonblank a haB) (nonblank b hbB)
  have confined := adjusted_relativeSupport_subset B G G' R support a b haR hbR adjusted
  have off (x : Cell n) (hx : x∉R) : B x=G' x := (relativeSupport_subset_iff B G' R).mp confined x hx
  obtain ⟨path,len⟩ := tsort hR hC G' R hRF w hw B ⟨hb,sign',fun x hx _ _ => off x hx⟩
  refine ⟨G',path,len.trans (psi_le G' R w B),?_,fun x hx => (off x hx).symm,?_⟩
  · rw [blank',blankG]
  · intro x hx
    exact (adjusted x (fun e => haF (e ▸ hx)) (fun e => hbF (e ▸ hx))).trans (goals x hx)

end SlidingPuzzle.NestedRouting.Cycle3
