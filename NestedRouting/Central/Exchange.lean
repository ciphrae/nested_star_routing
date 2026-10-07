import NestedRouting.Central.Spec
import NestedRouting.Moves.TSort

/-! The root's direct exchange by `t`-cycles. The entry pair lies on the
middle row, `eP = (c, c-2)` left of `zP = (c, c-1)`. A frame whose block is
`p = eP`, `s = zP` runs right along the row from `eP` (its first axis) and
up or down (its second), so it covers the columns `≥ c-2`. After one move
of the blank onto `eP`, a frame with `p = zP`, `s = eP` runs left and covers
the columns `≤ c-1`. Either way the frame is about half the board, so the
exchange costs `8n + O(1)` instead of the `54n` of a square three-cycle over
the whole board. The four cells next to the block in rows `c ± 1` lie in
every such block; they are exchanged by a three-cycle in a `6 × 6` square. -/
namespace SlidingPuzzle.NestedRouting.Central
open Interface Placement Finset Corner Routes

set_option linter.unusedSectionVars false

variable {n : Nat} [NeZero n]

/-- One half: the cycle `(cc c0 a, x, y)` with the blank on `cc c0 (a ± 1)`, for
`x` in the half-plane of the frame, `y` four or five cells along the row. -/
theorem half_cycle (c0 a : Nat) (dr dc : Bool) (hc0 : c0<n) (ha : a<n)
    (h7 : dc=true → 7≤a+1) (h7' : dc=false → a+7≤n)
    (h6 : dr=true → 6≤c0+1) (h6' : dr=false → c0+6≤n)
    (B : Board n) (hb : blank B=cc c0 (ax dc a 1))
    (i j : Nat) (hi : i<(if dc then a+1 else n-a)) (hj : j<(if dr then c0+1 else n-c0)) (out : 2 ≤ i ∨ 2 ≤ j)
    (k : Nat) (hk : 2≤k) (hk7 : k<7) (xy : cc (ax dr c0 j) (ax dc a i)≠cc (n:=n) c0 (ax dc a k)) :
    ∃ E : Board n, ∃ path : Path B E,
      path.length≤2*(112+2)+(2*(2*((if dc then a+1 else n-a)+(if dr then c0+1 else n-c0))+
        4*max (if dc then a+1 else n-a) (if dr then c0+1 else n-c0))+4+2) ∧
      blank E=cc c0 (ax dc a 1) ∧
      Cycle3.IsCycle B E (cc c0 a) (cc (ax dr c0 j) (ax dc a i)) (cc c0 (ax dc a k)) := by
  set R := (if dc then a+1 else n-a) with hRdef
  set C := (if dr then c0+1 else n-c0) with hCdef
  let F := hframe (n:=n) c0 a R C dr dc hc0 ha
    (fun h => by rw [hRdef,if_pos h]) (fun h => by rw [hRdef,if_neg (by simp [h])]; omega)
    (fun h => by rw [hCdef,if_pos h]) (fun h => by rw [hCdef,if_neg (by simp [h])]; omega)
  let G := hframe (n:=n) c0 a 7 6 dr dc hc0 ha
    (fun h => h7 h) (fun h => h7' h) (fun h => h6 h) (fun h => h6' h)
  have hRn : 7≤R := by
    rw [hRdef]; cases dc
    · have := h7' rfl; simp; omega
    · have := h7 rfl; simp; omega
  have hCn : 6≤C := by
    rw [hCdef]; cases dr
    · have := h6' rfl; simp; omega
    · have := h6 rfl; simp; omega
  have e00 : F.loc 0 0=cc c0 a := by
    show cc (ax dr c0 0) (ax dc a 0)=_; simp [ax]
  have e10 : F.loc 1 0=cc c0 (ax dc a 1) := by
    show cc (ax dr c0 0) (ax dc a 1)=_; simp [ax]
  have eG : G.loc k 0=cc c0 (ax dc a k) := by
    show cc (ax dr c0 0) (ax dc a k)=_; simp [ax]
  obtain ⟨E,path,len,bE,cyc⟩ := Cycle3.tdirect F G (by change 3≤R; omega) (by change 6≤C; omega)
    (by change 3≤7; omega) (by change 6≤6; omega) (fun _ _ _ _ => rfl) B (by rw [e10]; exact hb)
    i j hi hj out k 0 (by change k<7; omega) (by change 0<6; omega) (Or.inl hk) (by rw [eG]; exact xy)
  rw [eG] at cyc
  have tG : Cycle3.tcost G=112 := rfl
  refine ⟨E,path,?_,by rw [bE,e10],by rw [←e00]; exact cyc⟩
  rw [tG] at len
  exact len

theorem out_arith {c qr qc : Nat} (h6 : 6 ≤ c) (hA2 : ¬(qc ≤ c - 1 ∧ qr ≤ c + 1 ∧ c ≤ qr + 1)) :
    2 ≤ qc-(c-2) ∨ 2 ≤ (if qr<c then c-qr else qr-c) := by
  by_cases h : qr<c <;> simp only [h,if_true,if_false] <;> omega

namespace CParams
variable (p : CParams n)

theorem N_n : p.N≤n := by have := p.N_le; unfold N; omega

theorem mid_cc {c0 : Nat} (h : c0<p.N) : p.mid c0=cc p.c c0 := by
  have := p.N_n; have := p.c_lt
  have a1 : (p.mid c0).1.val=p.c := p.q0_row (by omega) h
  have a2 : (p.mid c0).2.val=c0 := p.q0_col (by omega) h
  have b := cc_val (n:=n) (r:=p.c) (c:=c0) (by omega) (by omega)
  exact cell_eq (a1.trans b.1.symm) (a2.trans b.2.symm)

theorem six_le_c : 14≤p.c := by have := p.T_big; have := p.W_two; have := p.m_two; unfold c; omega

/-- The parking cells: two on each side of the entry on the middle row. -/
def rpark (y : Cell n) : Prop :=
  y=p.mid (p.c+2) ∨ y=p.mid (p.c+3) ∨ y=p.mid (p.c-5) ∨ y=p.mid (p.c-6)

/-- The cost of a direct exchange at the root. -/
def rdcost : Nat := 16*(n-p.c)+260

/-- The direct exchange `(eP q p₁)` at the root. -/
theorem root_dX (B : Board n) (q : Cell n) (atZ : blank B=p.zP) (qe : q≠p.eP) (qz : q≠p.zP) :
    ∃ C : Board n, ∃ path : Path B C, ∃ p1 : Cell n, p.rpark p1 ∧ p1≠q ∧ blank C=p.zP ∧
      C p.eP=B q ∧ C q=B p1 ∧ C p1=B p.eP ∧
      (∀ y, y≠p.eP → y≠q → y≠p1 → C y=B y) ∧ path.length≤p.rdcost := by
  have hN := p.N_n; have h6 := p.six_le_c; have hcl := p.c_lt
  have hNc : p.N=2*p.c+1 := by unfold N c; omega
  have ecc : p.eP=cc p.c (p.c-2) := p.mid_cc (by omega)
  have zcc : p.zP=cc p.c (p.c-1) := p.mid_cc (by omega)
  set c := p.c with hc
  set qr := q.1.val with hqr
  set qc := q.2.val with hqc
  have hq : q=cc qr qc := (cc_self q).symm
  have qrn : qr<n := q.1.isLt
  have qcn : qc<n := q.2.isLt
  clear_value c qr qc
  have cyc_out {E : Board n} {a b d : Cell n} (h : Cycle3.IsCycle B E a b d) :
      E a=B b ∧ E b=B d ∧ E d=B a ∧ ∀ y, y≠a → y≠b → y≠d → E y=B y := h
  unfold rdcost
  by_cases hA : c-2≤qc ∧ ¬(qc ≤ c - 1 ∧ qr ≤ c + 1 ∧ c ≤ qr + 1)
  · -- right of the entry
    obtain ⟨hA1,hA2⟩ := hA
    have hout : 2 ≤ qc-(c-2) ∨ 2 ≤ (if qr<c then c-qr else qr-c) := by
      exact out_arith (by omega) hA2
    have hk : ∃ k, (k=4 ∨ k=5) ∧ q≠cc c (c-2+k) := by
      by_cases h4 : q=cc c (c-2+4)
      · refine ⟨5,Or.inr rfl,fun e => ?_⟩
        rw [h4] at e; exact cc_ne (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega)) e
      · exact ⟨4,Or.inl rfl,h4⟩
    obtain ⟨k,hk45,hqk⟩ := hk
    have dq : q=cc (ax (decide (qr<c)) c (if qr<c then c-qr else qr-c)) (ax false (c-2) (qc-(c-2))) := by
      rw [hq]; congr 1
      · by_cases h : qr<c <;> simp [h,ax] <;> omega
      · simp [ax]; omega
    have bZ : blank B=cc c (ax false (c-2) 1) := by rw [atZ,zcc]; simp [ax]; congr 1; omega
    obtain ⟨E,path,len,bE,cyc⟩ := half_cycle (n:=n) c (c-2) (decide (qr<c)) false (by omega) (by omega)
      (fun h => by cases h) (fun _ => by omega) (fun _ => by omega) (fun _ => by omega) B bZ
      (qc-(c-2)) (if qr<c then c-qr else qr-c)
      (by simp; omega) (by by_cases h : qr<c <;> simp only [h,decide_true,decide_false,if_true,if_false,Bool.false_eq_true] <;> omega)
      hout k (by omega) (by omega)
      (by rw [←dq]; simpa [ax] using hqk)
    rw [←dq] at cyc
    obtain ⟨c1,c2,c3,c4⟩ := cyc_out cyc
    have yk : cc c (ax false (c-2) k)=p.mid (c+2) ∨ cc c (ax false (c-2) k)=p.mid (c+3) := by
      rcases hk45 with rfl | rfl
      · left; rw [p.mid_cc (by omega)]; simp [ax]; congr 1; omega
      · right; rw [p.mid_cc (by omega)]; simp [ax]; congr 1; omega
    refine ⟨E,path,cc c (ax false (c-2) k),?_,?_,by rw [bE,zcc]; simp [ax]; congr 1; omega,
      by rw [ecc]; exact c1,c2,by rw [ecc]; exact c3,fun y h1 h2 h3 => c4 y (by rw [←ecc]; exact h1) h2 h3,?_⟩
    · unfold rpark; rw [←hc]
      rcases yk with e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
    · intro e; apply hqk; rw [←e]; simp [ax]
    · revert len; by_cases h : qr<c <;> simp [h] <;> intro len <;> omega
  by_cases hL : qc<c-2
  · -- left of the entry: the blank steps onto `eP` first
    have hk : ∃ k, (k=4 ∨ k=5) ∧ q≠cc c (c-1-k) := by
      by_cases h4 : q=cc c (c-1-4)
      · refine ⟨5,Or.inr rfl,fun e => ?_⟩
        rw [h4] at e; exact cc_ne (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega)) e
      · exact ⟨4,Or.inl rfl,h4⟩
    obtain ⟨k,hk45,hqk⟩ := hk
    have adj : gridDistance p.zP p.eP=1 := by
      rw [zcc,ecc]; unfold cc
      rw [(CParams.boardP (n:=n)).loc_dist (by omega) (by omega) (by omega) (by omega)]
      simp [Nat.dist]; omega
    obtain ⟨C1,P1,l1,b1,s1,f1⟩ := Cycle3.move B p.zP p.eP atZ adj
    have dq : q=cc (ax (decide (qr<c)) c (if qr<c then c-qr else qr-c)) (ax true (c-1) (c-1-qc)) := by
      rw [hq]; congr 1
      · by_cases h : qr<c <;> simp [h,ax] <;> omega
      · simp only [ax,if_true]; omega
    have bE : blank C1=cc c (ax true (c-1) 1) := by rw [b1,ecc]; simp only [ax,if_true]; congr 1
    obtain ⟨E,path,len,bE',cyc⟩ := half_cycle (n:=n) c (c-1) (decide (qr<c)) true (by omega) (by omega)
      (fun _ => by omega) (fun h => by cases h) (fun _ => by omega) (fun _ => by omega) C1 bE
      (c-1-qc) (if qr<c then c-qr else qr-c)
      (by simp) (by by_cases h : qr<c <;> simp only [h,decide_true,decide_false,if_true,if_false,Bool.false_eq_true] <;> omega)
      (Or.inl (by omega)) k (by omega) (by omega)
      (by rw [←dq]; simpa [ax] using hqk)
    rw [←dq] at cyc
    obtain ⟨E',R,lR,bR,cR⟩ := Cycle3.conj P1 path (bE'.trans bE.symm) cyc
    have ak : ax true (c-1) k=c-1-k := by simp [ax]
    have y_e : cc c (ax true (c-1) k)≠p.eP := by
      rw [ecc,ak]; exact cc_ne (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega))
    have y_z : cc c (ax true (c-1) k)≠p.zP := by
      rw [zcc,ak]; exact cc_ne (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega))
    have k1 : B.symm (C1 (cc c (ax true (c-1) 0)))=p.eP := by
      have : cc c (ax true (c-1) 0)=p.zP := by rw [zcc]; simp [ax]
      rw [this,s1]; simp
    have k2 : B.symm (C1 q)=q := by rw [f1 q qz qe]; simp
    have k3 : B.symm (C1 (cc c (ax true (c-1) k)))=cc c (ax true (c-1) k) := by
      rw [f1 _ y_z y_e]; simp
    have e0 : cc (n:=n) c (c-1)=cc c (ax true (c-1) 0) := by simp [ax]
    rw [e0,k1,k2,k3] at cR
    obtain ⟨c1,c2,c3,c4⟩ := cyc_out cR
    have yk : cc c (ax true (c-1) k)=p.mid (c-5) ∨ cc c (ax true (c-1) k)=p.mid (c-6) := by
      rcases hk45 with rfl | rfl
      · left; rw [p.mid_cc (by omega),←hc]; simp only [ax,if_true]; exact congrArg _ (by omega)
      · right; rw [p.mid_cc (by omega),←hc]; simp only [ax,if_true]; exact congrArg _ (by omega)
    refine ⟨E',R,cc c (ax true (c-1) k),?_,?_,by rw [bR,atZ],c1,c2,c3,c4,?_⟩
    · unfold rpark; rw [←hc]
      rcases yk with e | e
      · exact Or.inr (Or.inr (Or.inl e))
      · exact Or.inr (Or.inr (Or.inr e))
    · intro e; apply hqk; rw [←e]; simp [ax]
    · rw [lR,l1]
      revert len; by_cases h : qr<c <;> simp [h] <;> intro len <;> omega
  · -- the four cells next to the block: a three-cycle in a `6 × 6` square
    have hsp : (qc=c-2 ∨ qc=c-1) ∧ (qr=c-1 ∨ qr=c+1) := by
      have : ¬(qr=c ∧ (qc=c-2 ∨ qc=c-1)) := by
        rintro ⟨h1,h2|h2⟩
        · exact qe (by rw [hq,ecc,h1,h2])
        · exact qz (by rw [hq,zcc,h1,h2])
      omega
    let sq : Placement 6 n := ⟨c-1,c-2,false,false,by omega,by omega⟩
    have inR {r c' : Nat} (h1 : c-1≤r) (h2 : r<c+5) (h3 : c-2≤c') (h4 : c'<c+4) :
        cc r c'∈Set.range sq.embed := by
      refine ⟨(⟨r-(c-1),by omega⟩,⟨c'-(c-2),by omega⟩),?_⟩
      have := cc_val (n:=n) (r:=r) (c:=c') (by omega) (by omega)
      apply cell_eq
      · rw [this.1]; simp [sq,axis]; omega
      · rw [this.2]; simp [sq,axis]; omega
    have u_e : cc c (c+2)≠p.eP := by
      rw [ecc]; exact cc_ne (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega))
    have u_z : cc c (c+2)≠p.zP := by
      rw [zcc]; exact cc_ne (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega))
    have u_q : q≠cc c (c+2) := by
      rw [hq]; exact cc_ne (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))
    have z_e : p.zP≠p.eP := by
      rw [zcc,ecc]; exact cc_ne (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega))
    obtain ⟨C,path,len,bC,cyc⟩ := range_cycle sq.embed (fun a b h => by rw [sq.distance]; exact h)
      (le_refl 6) (x:=p.eP) (y:=q) (z:=cc c (c+2)) (c:=p.zP)
      (by rw [ecc]; exact inR (by omega) (by omega) (by omega) (by omega))
      (by rw [hq]; exact inR (by omega) (by omega) (by omega) (by omega))
      (inR (by omega) (by omega) (by omega) (by omega))
      (by rw [zcc]; exact inR (by omega) (by omega) (by omega) (by omega))
      (Ne.symm qe) u_e.symm u_q z_e (Ne.symm qz) u_z.symm B atZ
    obtain ⟨c1,c2,c3,c4⟩ := cyc_out cyc
    refine ⟨C,path,cc c (c+2),?_,Ne.symm u_q,bC,c1,c2,c3,c4,?_⟩
    · unfold rpark; rw [←hc]; left; rw [p.mid_cc (by omega),←hc]
    · omega

/-- The wrapper cycles at the root, by `t`-cycles in a `7 × 6` frame at the
entry: the carrier `K` and the third cell `u` are three and four cells
right of `eP` on the middle row. -/
theorem root_wX (B : Board n) (atZ : blank B=p.zP) (plus : Bool) :
    ∃ C : Board n, ∃ path : Path B C, path.length≤186 ∧ blank C=p.zP ∧
      (if plus then Cycle3.IsCycle B C (p.hub K) p.eP (p.hub u)
        else Cycle3.IsCycle B C p.eP (p.hub K) (p.hub u)) := by
  have hN := p.N_n; have h6 := p.six_le_c; have hcl := p.c_lt
  have hNc : p.N=2*p.c+1 := by unfold N c; omega
  let F := hframe (n:=n) p.c (p.c-2) 7 6 false false (by omega) (by omega) (fun h => by cases h)
    (fun _ => by omega) (fun h => by cases h) (fun _ => by omega)
  have Floc (i j : Nat) : F.loc i j=cc (p.c+j) (p.c-2+i) := by
    show cc (ax false p.c j) (ax false (p.c-2) i)=_; simp [ax]
  have e00 : F.loc 0 0=p.eP := by
    rw [Floc]; change _=p.mid (p.c-2); rw [p.mid_cc (by omega)]; congr 1
  have e10 : F.loc 1 0=p.zP := by
    rw [Floc]; change _=p.mid (p.c-1); rw [p.mid_cc (by omega)]; congr 1; omega
  have e30 : F.loc 3 0=p.hub K := by rw [Floc,p.hubK',p.mid_cc (by omega)]; congr 1; omega
  have e40 : F.loc 4 0=p.hub u := by rw [Floc,p.hubU',p.mid_cc (by omega)]; congr 1; omega
  have ne34 : F.loc 3 0≠F.loc 4 0 := ne_loc F (by change 3<7; omega) (by change 0<6; omega)
    (by change 4<7; omega) (by change 0<6; omega) (by omega)
  cases plus
  · obtain ⟨C,path,len,bC,cyc⟩ := Cycle3.tdirect_at2 F F (by change 3≤7; omega) (by change 6≤6; omega)
      (by change 3≤7; omega) (by change 6≤6; omega) (fun _ _ _ _ => rfl) B (by rw [e10]; exact atZ)
      3 0 (by change 3<7; omega) (by change 0<6; omega) (Or.inl (by omega))
      4 0 (by change 4<7; omega) (by change 0<6; omega) (Or.inl (by omega)) ne34
    rw [e00,e30,e40] at cyc
    refine ⟨C,path,?_,by rw [bC,e10],cyc⟩
    have : Cycle3.tw 4 0=64 := rfl
    have : Cycle3.tw 3 0=52 := rfl
    omega
  · obtain ⟨C,path,len,bC,cyc⟩ := Cycle3.tdirect_at2 F F (by change 3≤7; omega) (by change 6≤6; omega)
      (by change 3≤7; omega) (by change 6≤6; omega) (fun _ _ _ _ => rfl) B (by rw [e10]; exact atZ)
      4 0 (by change 4<7; omega) (by change 0<6; omega) (Or.inl (by omega))
      3 0 (by change 3<7; omega) (by change 0<6; omega) (Or.inl (by omega)) (Ne.symm ne34)
    rw [e00,e30,e40] at cyc
    refine ⟨C,path,?_,by rw [bC,e10],cyc.rotate.rotate⟩
    have : Cycle3.tw 4 0=64 := rfl
    have : Cycle3.tw 3 0=52 := rfl
    omega

/-- The sort weight at the root: three halves of the `t`-cycle bound `16n` of
the whole board, plus a share of the walk to the corner and back. -/
def rfw : Nat := 12*n+n/3+2

/-- The root's final sort. The blank walks up its column to row `0` and left
to `(0,1)`; there the corner block `(0,0),(1,0),(0,1),(1,1)` of the
transposed board frame serves the `t`-cycle sort; the walk is undone by
conjugation. The block cells hold child homes, which `R` avoids. -/
theorem root_fsort (B T : Board n) (R F : Finset (Cell n)) (atZ : blank B=p.zP)
    (zR : p.zP∉R) (corner : cc 0 0∉R ∧ cc 1 0∉R ∧ cc 1 1∉R) (inside : F⊆R)
    (hnonzero : ∀ x∈F, T x≠0) (hpresent : ∀ x∈F, ∃ y∈R, B y=T x) (room : F.card+3≤R.card) :
    ∃ C : Board n, ∃ path : Path B C, path.length≤2*∑ _x∈R, rfw (n:=n) ∧ blank C=blank B ∧
      (∀ x, x∉R → C x=B x) ∧ ∀ x∈F, C x=T x := by
  classical
  have hN := p.N_n; have h6 := p.six_le_c; have hcl := p.c_lt
  have hNc : p.N=2*p.c+1 := by unfold N c; omega
  have zcc : p.zP=cc p.c (p.c-1) := p.mid_cc (by omega)
  set c := p.c with hc
  clear_value c
  let F0 : Routes.Frame n := (CParams.boardP (n:=n)).toFrame
  have F0loc (r c' : Nat) : F0.loc r c'=cc r c' := rfl
  -- the walk: up column `c-1` to row `0`, then left along row `0` to column `1`
  obtain ⟨C1,w1,l1,b1,f1⟩ := walkColUp F0 B (c-1) 0 c (by change _<n; omega) (by change _<n; omega)
    (by rw [F0loc,atZ,zcc]; congr 1; omega)
  obtain ⟨C,w2,l2,b2,f2⟩ := walkRowLeft F0 C1 0 1 (c-2) (by change _<n; omega) (by change _<n; omega)
    (by rw [b1,F0loc]; congr 1; omega)
  have fixC (r c' : Nat) (hr : r<n) (hc' : c'<n) (h1 : c'≠c-1) (h2 : r≠0 ∨ c'<1) : C (cc r c')=B (cc r c') := by
    rw [←F0loc,f2 r c' hr hc' (by rcases h2 with h | h <;> omega),f1 r c' hr hc' (Or.inl h1)]
  have bC : blank C=cc 0 1 := by rw [b2,F0loc]
  have k00 : C (cc 0 0)=B (cc 0 0) := fixC 0 0 (by omega) (by omega) (by omega) (Or.inr (by omega))
  have k10 : C (cc 1 0)=B (cc 1 0) := fixC 1 0 (by omega) (by omega) (by omega) (Or.inl (by omega))
  have k11 : C (cc 1 1)=B (cc 1 1) := fixC 1 1 (by omega) (by omega) (by omega) (Or.inl (by omega))
  -- the conjugated region and goals
  let π : Cell n → Cell n := fun x => C.symm (B x)
  have πinj : Function.Injective π := fun x y e => B.injective (C.symm.injective e)
  have Cπ (x : Cell n) : C (π x)=B x := by simp [π]
  let R' := R.image π
  let F' := F.image π
  let T' : Board n := (C.trans B.symm).trans T
  have T'π (x : Cell n) : T' (π x)=T x := by simp [T',π]
  let SF := hframe (n:=n) 0 0 n n false false (by omega) (by omega) (fun h => by cases h) (fun _ => by omega)
    (fun h => by cases h) (fun _ => by omega)
  have SFloc (i j : Nat) : SF.loc i j=cc j i := by
    show cc (ax false 0 j) (ax false 0 i)=_; simp [ax]
  have blkOut (y : Cell n) (hy : y∈R') : Cycle3.Out SF y := by
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
    have hv := cc_val (n:=n) (π x).1.isLt (π x).2.isLt
    refine ⟨(π x).2.val,(π x).1.val,(π x).2.isLt,(π x).1.isLt,?_,by rw [SFloc]; exact cc_self _⟩
    by_contra hsmall
    have e : π x=cc (π x).1.val (π x).2.val := (cc_self _).symm
    have k : (π x).1.val<2 ∧ (π x).2.val<2 := by omega
    have xB (y : Cell n) (hy : C y=B y) (e' : π x=y) : x=y := by
      apply B.injective; rw [←Cπ x,e',hy]
    rcases Nat.lt_or_ge (π x).1.val 1 with r0 | r1 <;> rcases Nat.lt_or_ge (π x).2.val 1 with c0 | c1
    · exact corner.1 (xB _ k00 (by rw [e]; congr 1 <;> omega) ▸ hx)
    · -- the blank cell `(0,1)`
      have e' : π x=cc 0 1 := by rw [e]; congr 1 <;> omega
      have : B x=0 := by rw [←Cπ x,e',←bC]; simp [blank,position]
      have xz : x=p.zP := by
        apply B.injective; rw [this,←atZ]; simp [blank,position]
      exact zR (xz ▸ hx)
    · exact corner.2.1 (xB _ k10 (by rw [e]; congr 1 <;> omega) ▸ hx)
    · exact corner.2.2 (xB _ k11 (by rw [e]; congr 1 <;> omega) ▸ hx)
  obtain ⟨D,ps,lps,bD,offD,onD⟩ := Cycle3.exists_tfinish SF (by change 3≤n; omega) (by change 6≤n; omega)
    C T' (by rw [bC,SFloc]) R' F' blkOut (fun _ => 16*n+2)
    (by
      intro x _ r c' hr hc' _
      change r<n at hr; change c'<n at hc'
      unfold Cycle3.tw; omega)
    (image_subset_image inside)
    (by
      intro y hy
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
      rw [T'π]; exact hnonzero x hx)
    (by
      intro y hy
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
      obtain ⟨z,hz,e⟩ := hpresent x hx
      exact ⟨π z,mem_image_of_mem _ hz,by rw [Cπ,T'π,e]⟩)
    (by rw [card_image_of_injective _ πinj,card_image_of_injective _ πinj]; exact room)
  obtain ⟨E,r,lr,bE,eff⟩ := (w1.append w2).exists_unstaged ps (by rw [bD])
  refine ⟨E,r,?_,bE,?_,?_⟩
  · rw [lr,Path.length_append]
    rw [sum_const,smul_eq_mul,card_image_of_injective _ πinj] at lps
    have hRc : 3≤R.card := by omega
    unfold rfw
    rw [sum_const,smul_eq_mul]
    have a1 : 2*(R.card*(12*n+n/3+2))=24*(n*R.card)+2*(R.card*(n/3))+4*R.card := by ring
    have a2 : 3*(n/3)≤R.card*(n/3) := Nat.mul_le_mul_right _ hRc
    have a3 : 3*(R.card*(16*n+2))=48*(n*R.card)+6*R.card := by ring
    have a4 : n≤3*(n/3)+2 := by omega
    rw [a1]; rw [a3] at lps
    generalize n*R.card=X at lps ⊢
    generalize R.card*(n/3)=Y at a2 ⊢
    omega
  · intro x hx
    rw [eff]
    have : π x∉R' := by
      intro hm; obtain ⟨y,hy,e⟩ := mem_image.mp hm
      exact hx (πinj e ▸ hy)
    change D (π x)=B x
    rw [offD _ this,Cπ]
  · intro x hx
    rw [eff]
    change D (π x)=T x
    rw [onD _ (mem_image_of_mem _ hx),T'π]

variable (Q : Fin 4 → Region n)
  (hcells : ∀ j y, y∈(Q j).cells → ∃ r c', p.A+p.W≤r ∧ r<p.N ∧ p.A≤c' ∧ c'<p.N ∧ (p.frame j).loc r c'=y)
  (hstrip : ∀ j y, y∈(Q j).strip → ∃ r c', p.A≤r ∧ r<p.A+p.W ∧ p.A≤c' ∧ c'<p.N ∧ (p.frame j).loc r c'=y)
  (hentry : ∀ j, (Q j).Entry (p.e j) (p.z j))
  (G : Board n) (hgoalQ : ∀ j, (Q j).goal=G) (hG : ∀ y, y≠p.zP → G y≠0)
  (hcorner : ∀ y, (y=cc 0 0 ∨ y=cc 1 0 ∨ y=cc 1 1) → ∃ j, y∈(Q j).coreCells∪(Q j).reserveCells)

theorem rpark_mid {y : Cell n} (h : p.rpark y) :
    ∃ c0, y=p.mid c0 ∧ c0<p.N ∧ c0≠p.c-2 ∧ c0≠p.c-1 ∧ c0<p.c+5 ∧ c0≠p.c+1 := by
  have := p.six_le_c; have := p.c_lt10
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨_,rfl,by omega,by omega,by omega,by omega,by omega⟩
  · exact ⟨_,rfl,by omega,by omega,by omega,by omega,by omega⟩
  · exact ⟨_,rfl,by omega,by omega,by omega,by omega,by omega⟩
  · exact ⟨_,rfl,by omega,by omega,by omega,by omega,by omega⟩

include hcells hstrip hentry hgoalQ hG hcorner in
/-- The root star: the default exchanges, with the direct exchange and the
final sort by `t`-cycles. -/
def spec : StarSpec n 4 :=
  { (p.base Q hcells hstrip hentry G hgoalQ hG).square with
    wcost := 186
    wX := fun B hB => p.root_wX B hB true
    wX' := fun B hB => p.root_wX B hB false
    park := p.rpark
    stat := ∅
    stat_own := by simp
    stat_loop := by simp
    stat_K := by simp
    stat_park := by simp
    dw := fun _ => 0
    dXw := by intro B q _ hq; simp at hq
    dcost := p.rdcost
    dX := by
      intro B q atZ hq
      have S := p.base Q hcells hstrip hentry G hgoalQ hG
      have qe : q≠p.eP := by
        rintro rfl
        rcases hq with ⟨j,hj⟩ | hq | hq
        · exact (p.base Q hcells hstrip hentry G hgoalQ hG).eP_child j hj
        · exact (p.base Q hcells hstrip hentry G hgoalQ hG).eP_own hq
        · exact (p.base Q hcells hstrip hentry G hgoalQ hG).eP_markers hq
      have qz : q≠p.zP := by
        rintro rfl
        rcases hq with ⟨j,hj⟩ | hq | hq
        · exact (p.base Q hcells hstrip hentry G hgoalQ hG).zP_child j hj
        · exact (p.base Q hcells hstrip hentry G hgoalQ hG).zP_own hq
        · exact (p.base Q hcells hstrip hentry G hgoalQ hG).zP_markers hq
      exact p.root_dX B q atZ qe qz
    park_own := by
      intro y hy
      obtain ⟨c0,rfl,h0,h1,h2,h3,_⟩ := p.rpark_mid hy
      exact p.mid_own Q hcells h0 h1 h2 h3
    park_loop := by
      intro y hy j h
      obtain ⟨c0,rfl,h0,_,_,_,_⟩ := p.rpark_mid hy
      have := p.A_lt
      change p.mid c0∈_ at h
      obtain ⟨r,c',hp,e⟩ := (p.mem_loop j).mp h
      have l := p.loopP_range hp
      exact p.frame_ne_mid j l.1 (by omega) (by omega) h0 e
    park_child := by
      intro y hy j
      obtain ⟨c0,rfl,h0,_,_,_,_⟩ := p.rpark_mid hy
      exact p.mid_notChild Q hcells h0 j
    park_K := by
      intro y hy h
      obtain ⟨c0,rfl,h0,_,_,_,h4⟩ := p.rpark_mid hy
      have := p.c_lt10
      change p.mid c0=p.hub K at h
      rw [p.hubK'] at h
      exact h4 (p.mid_inj h0 (by omega) h)
    fw := fun _ => rfw (n:=n)
    fsort := by
      intro B T R F hB hR hR' inside hnonzero hpresent room
      have S := p.base Q hcells hstrip hentry G hgoalQ hG
      have zR : p.zP∉R := by
        intro h
        rcases hR _ h with ⟨j,hj⟩ | h | h
        · exact (p.base Q hcells hstrip hentry G hgoalQ hG).zP_child j hj
        · exact (p.base Q hcells hstrip hentry G hgoalQ hG).zP_own h
        · exact (p.base Q hcells hstrip hentry G hgoalQ hG).zP_markers h
      have cor (y : Cell n) (hy : y=cc 0 0 ∨ y=cc 1 0 ∨ y=cc 1 1) : y∉R := by
        intro h
        obtain ⟨j,hj⟩ := hcorner y hy
        have := hR' y h j
        rcases mem_union.mp hj with h1 | h1
        · exact this.1 h1
        · exact this.2 h1
      exact p.root_fsort B T R F hB zR ⟨cor _ (Or.inl rfl),cor _ (Or.inr (Or.inl rfl)),cor _ (Or.inr (Or.inr rfl))⟩
        inside hnonzero hpresent room }

end CParams
end SlidingPuzzle.NestedRouting.Central
