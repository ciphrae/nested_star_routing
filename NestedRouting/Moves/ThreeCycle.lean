import NestedRouting.Moves.Routes
import NestedRouting.Moves.Conjugation

/-! A three-cycle of any three non-blank cells in at most `54n` moves, with
the blank and every other cell restored.

Fix a corner 2×2 block `K` (local cells `(0,0),(0,1),(1,0),(1,1)` of a
reflected frame `F`) that contains none of the three cells, and put the
blank at `z = (1,1)`. For a cell `x` outside `K`, carry its tile to
`s = (1,0)` by pushing it up its column and left along row 1, never
touching `p = (0,0)` and `q = (0,1)`; rotate the block; undo the trip by
conjugation (`Path.exists_unstaged`). The net effect is a three-cycle on
`(x, p, q)`, in either orientation. Four of these give `(a b c)`:
`a⁺ c⁻ b⁺ a⁻`, where `x⁺ = (x p q)` and `x⁻ = (x q p)`. -/
namespace SlidingPuzzle.NestedRouting.Cycle3
open Placement Routes

variable {n : Nat} [NeZero n]

/-- `E` is `B` with the contents of `a, b, c` cycled: `E a = B b`, … -/
def IsCycle (B E : Board n) (a b c : Cell n) : Prop :=
  E a=B b ∧ E b=B c ∧ E c=B a ∧ ∀ y, y≠a → y≠b → y≠c → E y=B y

variable (F : Frame n)

/-! ### Pushing one tile

`p = (0,0)` and `q = (0,1)` are never touched. -/

/-- Push the tile at `(1,c)` left to `s = (1,0)`, the blank starting at
`(1,c-1)` and ending at `z = (1,1)`. Detours use row 2. -/
theorem pushLeft (hR : 3≤F.R) (hC : 6≤F.C) (c : Nat) (B : Board n) (hc1 : 1≤c) (hc : c<F.C)
    (hb : blank B=F.loc 1 (c-1)) :
    ∃ C : Board n, ∃ path : Path B C, path.length≤5*c ∧ C (F.loc 1 0)=B (F.loc 1 c) ∧
      blank C=F.loc 1 1 ∧ C (F.loc 0 0)=B (F.loc 0 0) ∧ C (F.loc 0 1)=B (F.loc 0 1) := by
  induction c generalizing B with
  | zero => omega
  | succ c ih =>
    rcases Nat.eq_zero_or_pos c with rfl | hc0
    · have chain : Chained [F.loc 1 0,F.loc 1 1] := by chain_tac
      obtain ⟨C,path,len,blankC,fix,head⟩ := route B _ _ chain hb
      refine ⟨C,path,by simp [len],head _ _ rfl (by notmem_tac),blankC,
        fix _ (by notmem_tac),fix _ (by notmem_tac)⟩
    · have chain : Chained [F.loc 1 c,F.loc 1 (c+1),F.loc 2 (c+1),F.loc 2 c,F.loc 2 (c-1),
          F.loc 1 (c-1)] := by chain_tac
      obtain ⟨C1,path1,len1,blank1,fix1,head1⟩ := route B _ _ chain (by simpa using hb)
      obtain ⟨C,path,len,cs,blankC,fp,fq⟩ := ih C1 hc0 (by omega) blank1
      refine ⟨C,path1.append path,by simp [len1]; omega,?_,blankC,?_,?_⟩
      · rw [cs,head1 _ _ rfl (by notmem_tac)]
      · rw [fp,fix1 _ (by notmem_tac)]
      · rw [fq,fix1 _ (by notmem_tac)]

/-- The column used for detours beside column `c`. -/
def side (n c : Nat) : Nat := if c+1<n then c+1 else c-1

omit [NeZero n] in
theorem side_lt {c : Nat} (hn : 6≤n) (hc : c<n) : side n c<n := by
  unfold side; split_ifs <;> omega

omit [NeZero n] in
theorem side_dist {c : Nat} (hn : 6≤n) (hc : c<n) : Nat.dist c (side n c)=1 := by
  unfold side Nat.dist; split_ifs <;> omega

/-- Push the tile at `(r+1,c)` up to `(1,c)`, the blank starting at `(r,c)`
and ending at `(2,c)`. Detours use the column `side c`. -/
theorem pushUp (hR : 3≤F.R) (hC : 6≤F.C) (r c : Nat) (B : Board n) (hr1 : 1≤r) (hr : r+1<F.R) (hc : c<F.C)
    (hb : blank B=F.loc r c) :
    ∃ C : Board n, ∃ path : Path B C, path.length≤5*r ∧ C (F.loc 1 c)=B (F.loc (r+1) c) ∧
      blank C=F.loc 2 c ∧ C (F.loc 0 0)=B (F.loc 0 0) ∧ C (F.loc 0 1)=B (F.loc 0 1) := by
  have hs := side_lt hC hc
  have hd := side_dist hC hc
  have hsc : side F.C c≠c := by intro h; rw [h] at hd; simp [Nat.dist] at hd
  induction r generalizing B with
  | zero => omega
  | succ r ih =>
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · have chain : Chained [F.loc 1 c,F.loc 2 c] := by chain_tac
      obtain ⟨C,path,len,blankC,fix,head⟩ := route B _ _ chain hb
      refine ⟨C,path,by simp [len],head _ _ rfl (by notmem_tac),blankC,
        fix _ (by notmem_tac),fix _ (by notmem_tac)⟩
    · have chain : Chained [F.loc (r+1) c,F.loc (r+2) c,F.loc (r+2) (side F.C c),
          F.loc (r+1) (side F.C c),F.loc r (side F.C c),F.loc r c] := by
        simp only [Chained,List.isChain_cons_cons,List.isChain_singleton,and_true]
        refine ⟨?_,?_,?_,?_,?_⟩
        all_goals apply adj_loc <;> first | omega | (unfold Nat.dist at hd ⊢; omega)
      obtain ⟨C1,path1,len1,blank1,fix1,head1⟩ := route B _ _ chain hb
      obtain ⟨C,path,len,cs,blankC,fp,fq⟩ := ih C1 hr0 (by omega) blank1
      refine ⟨C,path1.append path,by simp [len1]; omega,?_,blankC,?_,?_⟩
      · rw [cs,head1 _ _ rfl (by notmem_tac)]
      · rw [fp,fix1 _ (by notmem_tac)]
      · rw [fq,fix1 _ (by notmem_tac)]

/-- Push the tile diagonally up-left `k` times, 6 moves each: from `(R,C)`
with the blank just above, to `(R-k,C-k)` with the blank just above.
Rows stay at least `r-1 ≥ 1`. -/
theorem pushDiag (hR : 3≤F.R) (hC : 6≤F.C) (r c k : Nat) (B : Board n) (hr : 2≤r) (hrk : r+k<F.R) (hck : c+k<F.C)
    (hb : blank B=F.loc (r+k-1) (c+k)) :
    ∃ C : Board n, ∃ path : Path B C, path.length≤6*k ∧ C (F.loc r c)=B (F.loc (r+k) (c+k)) ∧
      blank C=F.loc (r-1) c ∧ C (F.loc 0 0)=B (F.loc 0 0) ∧ C (F.loc 0 1)=B (F.loc 0 1) := by
  induction k generalizing B with
  | zero => exact ⟨B,.nil B,by simp,by simp,by simpa using hb,rfl,rfl⟩
  | succ k ih =>
    -- tile at (R,C) = (r+k+1,c+k+1), blank at (R-1,C)
    have chain1 : Chained [F.loc (r+k) (c+k+1),F.loc (r+k+1) (c+k+1),F.loc (r+k+1) (c+k),
        F.loc (r+k) (c+k)] := by chain_tac
    obtain ⟨C1,p1,l1,b1,f1,h1⟩ := route B _ _ chain1 (by rw [hb]; congr 1)
    have chain2 : Chained [F.loc (r+k) (c+k),F.loc (r+k) (c+k+1),F.loc (r+k-1) (c+k+1),
        F.loc (r+k-1) (c+k)] := by
      simp only [Chained,List.isChain_cons_cons,List.isChain_singleton,and_true]
      refine ⟨?_,?_,?_⟩ <;> apply adj_loc <;> first | omega | (unfold Nat.dist; omega)
    obtain ⟨C2,p2,l2,b2,f2,h2⟩ := route C1 _ _ chain2 b1
    obtain ⟨C,p3,l3,s3,b3,fp,fq⟩ := ih C2 (by omega) (by omega) b2
    refine ⟨C,(p1.append p2).append p3,by simp [l1,l2]; omega,?_,b3,?_,?_⟩
    · rw [s3,h2 _ _ rfl (by notmem_tac),h1 _ _ rfl (by notmem_tac)]
      congr 1
    · rw [fp,f2 _ (by notmem_tac),f1 _ (by notmem_tac)]
    · rw [fq,f2 _ (by notmem_tac),f1 _ (by notmem_tac)]

/-- Carry the tile at `(r,c)`, outside the corner block, to `s = (1,0)`; the
blank starts and ends at `z = (1,1)`, and `p, q` are untouched. The cost
depends on the position only. -/
theorem transport_at (hR : 3≤F.R) (hC : 6≤F.C) (B : Board n) (hb : blank B=F.loc 1 1) (r c : Nat) (hr : r<F.R)
    (hc : c<F.C) (out : 2≤r ∨ 2≤c) :
    ∃ C : Board n, ∃ path : Path B C, path.length≤2*(r+c)+4*max r c+6 ∧ C (F.loc 1 0)=B (F.loc r c) ∧
      blank C=F.loc 1 1 ∧ C (F.loc 0 0)=B (F.loc 0 0) ∧ C (F.loc 0 1)=B (F.loc 0 1) := by
  rcases Nat.lt_or_ge r 2 with hr2 | hr2
  · have hc2 : 2≤c := by omega
    rcases Nat.lt_or_ge r 1 with hr1 | hr1
    · -- row 0: bring the blank under the tile, pull the tile down
      have r0 : r=0 := by omega
      subst r0
      obtain ⟨C1,p1,l1,b1,f1⟩ := walkRow F B 1 1 (c-1) (by omega) (by omega) hb
      have b1' : blank C1=F.loc 1 c := by rw [b1]; congr 1; omega
      rcases Nat.lt_or_ge c 3 with hc3 | hc3
      · have c2 : c=2 := by omega
        subst c2
        have chain : Chained [F.loc 1 2,F.loc 0 2,F.loc 0 3,F.loc 1 3,F.loc 2 3,F.loc 2 2,
            F.loc 2 1,F.loc 1 1] := by chain_tac
        obtain ⟨C2,p2,l2,b2,f2,h2⟩ := route C1 _ _ chain b1'
        obtain ⟨C,p3,l3,s3,b3,fp,fq⟩ := pushLeft F hR hC 2 C2 (by omega) (by omega) (by simpa using b2)
        refine ⟨C,(p1.append p2).append p3,by simp [l1,l2]; omega,?_,b3,?_,?_⟩
        · rw [s3,h2 _ _ rfl (by notmem_tac),f1 0 2 (by omega) (by omega) (by omega)]
        · rw [fp,f2 _ (by notmem_tac),f1 0 0 (by omega) (by omega) (by omega)]
        · rw [fq,f2 _ (by notmem_tac),f1 0 1 (by omega) (by omega) (by omega)]
      · have chain : Chained [F.loc 1 c,F.loc 0 c,F.loc 0 (c-1),F.loc 1 (c-1)] := by chain_tac
        obtain ⟨C2,p2,l2,b2,f2,h2⟩ := route C1 _ _ chain b1'
        obtain ⟨C,p3,l3,s3,b3,fp,fq⟩ := pushLeft F hR hC c C2 (by omega) hc (by simpa using b2)
        refine ⟨C,(p1.append p2).append p3,by simp [l1,l2]; omega,?_,b3,?_,?_⟩
        · rw [s3,h2 _ _ rfl (by notmem_tac),f1 0 c (by omega) hc (by omega)]
        · rw [fp,f2 _ (by notmem_tac),f1 0 0 (by omega) (by omega) (by omega)]
        · rw [fq,f2 _ (by notmem_tac),f1 0 1 (by omega) (by omega) (by omega)]
    · -- row 1: bring the blank beside the tile, push left
      have r1 : r=1 := by omega
      subst r1
      obtain ⟨C1,p1,l1,b1,f1⟩ := walkRow F B 1 1 (c-2) (by omega) (by omega) hb
      obtain ⟨C,p3,l3,s3,b3,fp,fq⟩ := pushLeft F hR hC c C1 (by omega) hc
        (by rw [b1]; congr 1; omega)
      refine ⟨C,p1.append p3,by simp [l1]; omega,?_,b3,?_,?_⟩
      · rw [s3,f1 1 c (by omega) hc (by omega)]
      · rw [fp,f1 0 0 (by omega) (by omega) (by omega)]
      · rw [fq,f1 0 1 (by omega) (by omega) (by omega)]
  · -- rows ≥ 2: blank above the tile, diagonal steps, push up, then left
    obtain ⟨C1,p1,l1,b1,f1⟩ := walkCol F B 1 1 (r-2) (by omega) (by omega) hb
    have b1' : blank C1=F.loc (r-1) 1 := by rw [b1]; congr 1; omega
    obtain ⟨C2,p2,l2,b2,f2⟩ : ∃ C2 : Board n, ∃ p2 : Path C1 C2, p2.length≤c+1 ∧
        blank C2=F.loc (r-1) c ∧ ∀ y, y=F.loc r c ∨ y=F.loc 0 0 ∨ y=F.loc 0 1 → C2 y=C1 y := by
      rcases Nat.eq_zero_or_pos c with c0 | c0
      · subst c0
        have chain : Chained [F.loc (r-1) 1,F.loc (r-1) 0] := by chain_tac
        obtain ⟨C2,p2,l2,b2,f2,_⟩ := route C1 _ _ chain b1'
        refine ⟨C2,p2,by simp [l2],b2,?_⟩
        rintro y (rfl|rfl|rfl) <;> exact f2 _ (by notmem_tac)
      · obtain ⟨C2,p2,l2,b2,f2⟩ := walkRow F C1 (r-1) 1 (c-1) (by omega) (by omega) b1'
        refine ⟨C2,p2,by omega,by rw [b2]; congr 1; omega,?_⟩
        rintro y (rfl|rfl|rfl)
        · exact f2 r c hr hc (by omega)
        · exact f2 0 0 (by omega) (by omega) (by omega)
        · exact f2 0 1 (by omega) (by omega) (by omega)
    have keep (y : Cell n) (hy : y=F.loc r c ∨ y=F.loc 0 0 ∨ y=F.loc 0 1) : C2 y=B y := by
      rw [f2 y hy]
      rcases hy with rfl|rfl|rfl
      · exact f1 r c hr hc (by omega)
      · exact f1 0 0 (by omega) (by omega) (by omega)
      · exact f1 0 1 (by omega) (by omega) (by omega)
    -- diagonal steps while row ≥ 2 and column ≥ 0 allow
    set k := min (r-2) c with hk
    have hk1 : k≤r-2 := min_le_left _ _
    have hk2 : k≤c := min_le_right _ _
    obtain ⟨C3,p3,l3,s3,b3,fp3,fq3⟩ := pushDiag F hR hC (r-k) (c-k) k C2 (by omega) (by omega) (by omega)
      (by rw [b2]; congr 1 <;> omega)
    have e3 : F.loc (r-k+k) (c-k+k)=F.loc r c := by congr 1 <;> omega
    rw [e3] at s3
    obtain ⟨C4,p4,l4,s4,b4,fp4,fq4⟩ := pushUp F hR hC (r-k-1) (c-k) C3 (by omega) (by omega) (by omega)
      b3
    have e4 : F.loc (r-k-1+1) (c-k)=F.loc (r-k) (c-k) := by congr 1; omega
    rw [e4,s3] at s4
    have hc4 : C4 (F.loc 1 (c-k))=B (F.loc r c) := by rw [s4,keep _ (Or.inl rfl)]
    have hp4 : C4 (F.loc 0 0)=B (F.loc 0 0) := by rw [fp4,fp3,keep _ (Or.inr (Or.inl rfl))]
    have hq4 : C4 (F.loc 0 1)=B (F.loc 0 1) := by rw [fq4,fq3,keep _ (Or.inr (Or.inr rfl))]
    rcases Nat.eq_zero_or_pos (c-k) with c0 | c0
    · rw [c0] at hc4 b4
      have chain : Chained [F.loc 2 0,F.loc 2 1,F.loc 1 1] := by chain_tac
      obtain ⟨C,p5,l5,b5,f5,_⟩ := route C4 _ _ chain b4
      have hck : c≤r-2 := by omega
      refine ⟨C,(((p1.append p2).append p3).append p4).append p5,?_,?_,b5,?_,?_⟩
      · simp only [Path.length_append]; simp at l5
        have : k=c := by omega
        rw [this] at l3 l4; omega
      · rw [f5 _ (by notmem_tac),hc4]
      · rw [f5 _ (by notmem_tac),hp4]
      · rw [f5 _ (by notmem_tac),hq4]
    · have chain : Chained [F.loc 2 (c-k),F.loc 2 (c-k-1),F.loc 1 (c-k-1)] := by chain_tac
      obtain ⟨C5,p5,l5,b5,f5,_⟩ := route C4 _ _ chain b4
      obtain ⟨C,p6,l6,s6,b6,fp,fq⟩ := pushLeft F hR hC (c-k) C5 c0 (by omega) (by simpa using b5)
      have hk' : k=r-2 := by omega
      refine ⟨C,((((p1.append p2).append p3).append p4).append p5).append p6,?_,?_,b6,?_,?_⟩
      · simp only [Path.length_append]; simp at l5
        rw [hk'] at l3 l4 l6; omega
      · rw [s6,f5 _ (by notmem_tac),hc4]
      · rw [fp,f5 _ (by notmem_tac),hp4]
      · rw [fq,f5 _ (by notmem_tac),hq4]

theorem transport (hR : 3≤F.R) (hC : 6≤F.C) (B : Board n) (hb : blank B=F.loc 1 1) (r c : Nat) (hr : r<F.R)
    (hc : c<F.C) (out : 2≤r ∨ 2≤c) :
    ∃ C : Board n, ∃ path : Path B C, path.length≤2*(F.R+F.C)+4*max F.R F.C ∧ C (F.loc 1 0)=B (F.loc r c) ∧
      blank C=F.loc 1 1 ∧ C (F.loc 0 0)=B (F.loc 0 0) ∧ C (F.loc 0 1)=B (F.loc 0 1) := by
  obtain ⟨C,path,len,h⟩ := transport_at F hR hC B hb r c hr hc out
  exact ⟨C,path,by omega,h⟩

/-! ### Cycles -/

omit [NeZero n] in
theorem IsCycle.rotate {B E : Board n} {a b c : Cell n} (h : IsCycle B E a b c) :
    IsCycle B E b c a :=
  ⟨h.2.1,h.2.2.1,h.1,fun y hb hc ha => h.2.2.2 y ha hb hc⟩

/-- One move of the blank to an adjacent cell. -/
theorem move (B : Board n) (u w : Cell n) (hb : blank B=u) (adj : gridDistance u w=1) :
    ∃ C : Board n, ∃ path : Path B C, path.length=1 ∧ blank C=w ∧ C u=B w ∧
      ∀ y, y≠u → y≠w → C y=B y := by
  have chain : Chained [u,w] := List.isChain_pair.mpr adj
  have uw : u≠w := by rintro rfl; simp at adj
  obtain ⟨C,path,len,blankC,fix,head⟩ := route B u [w] chain hb
  refine ⟨C,path,len,blankC,head w [] rfl (by simpa using uw),fun y hu hw => fix y (by simp [hu,hw])⟩

/-- Walking the blank once around a 2×2 block `z → u₁ → u₂ → u₃ → z` cycles
the other three cells. -/
theorem rotate (B : Board n) (z u1 u2 u3 : Cell n) (hb : blank B=z)
    (a1 : gridDistance z u1=1) (a2 : gridDistance u1 u2=1) (a3 : gridDistance u2 u3=1)
    (a4 : gridDistance u3 z=1) (d12 : u1≠u2) (d13 : u1≠u3) (d23 : u2≠u3)
    (dz1 : z≠u1) (dz2 : z≠u2) (dz3 : z≠u3) :
    ∃ C : Board n, ∃ path : Path B C, path.length=4 ∧ blank C=z ∧ IsCycle B C u1 u2 u3 := by
  obtain ⟨C1,p1,l1,b1,h1,f1⟩ := move B z u1 hb a1
  obtain ⟨C2,p2,l2,b2,h2,f2⟩ := move C1 u1 u2 b1 a2
  obtain ⟨C3,p3,l3,b3,h3,f3⟩ := move C2 u2 u3 b2 a3
  obtain ⟨C,p4,l4,b4,h4,f4⟩ := move C3 u3 z b3 a4
  refine ⟨C,((p1.append p2).append p3).append p4,by simp [l1,l2,l3,l4],b4,?_,?_,?_,?_⟩
  · rw [f4 _ d13 (Ne.symm dz1),f3 _ d12 d13,h2,f1 _ (Ne.symm dz2) (Ne.symm d12)]
  · rw [f4 _ d23 (Ne.symm dz2),h3,f2 _ (Ne.symm d13) (Ne.symm d23),f1 _ (Ne.symm dz3) (Ne.symm d13)]
  · rw [h4,f3 _ dz2 dz3,f2 _ dz1 dz2,h1]
  · intro y y1 y2 y3
    by_cases yz : y=z
    · subst yz
      have e1 : C (blank C)=0 := by simp [blank,position]
      have e2 : B (blank B)=0 := by simp [blank,position]
      rw [b4] at e1; rw [hb] at e2
      rw [e1,e2]
    · rw [f4 _ y3 yz,f3 _ y2 y3,f2 _ y1 y2,f1 _ yz y1]

/-- Conjugation: a cycle performed after a staging path `P` is a cycle of the
original cells of the staged tiles. -/
theorem conj {B C D : Board n} (P : Path B C) (Q : Path C D) (hbl : blank D=blank C)
    {u v w : Cell n} (h : IsCycle C D u v w) :
    ∃ E : Board n, ∃ r : Path B E, r.length=2*P.length+Q.length ∧ blank E=blank B ∧
      IsCycle B E (B.symm (C u)) (B.symm (C v)) (B.symm (C w)) := by
  obtain ⟨E,r,len,blankE,eff⟩ := P.exists_unstaged Q hbl
  refine ⟨E,r,len,blankE,?_,?_,?_,?_⟩
  · simp [eff,h.1]
  · simp [eff,h.2.1]
  · simp [eff,h.2.2.1]
  · intro y yu yv yw
    have ne (x : Cell n) (hx : y≠B.symm (C x)) : C.symm (B y)≠x := by
      intro e; apply hx; rw [← e]; simp
    rw [eff,h.2.2.2 _ (ne u yu) (ne v yv) (ne w yw)]
    simp

/-- The length bound of a `t`-cycle at `(r,c)`. -/
def tw (r c : Nat) : Nat := 2*(2*(r+c)+4*max r c+6)+4

/-- `t_x`: with the blank at `z`, cycle `(x, p, q)` (`plus`) or `(x, q, p)`
for a cell `x = (r,c)` outside the corner block. -/
theorem tcycle_at (hR : 3≤F.R) (hC : 6≤F.C) (B : Board n) (hb : blank B=F.loc 1 1) (r c : Nat)
    (hr : r<F.R) (hc : c<F.C) (out : 2≤r ∨ 2≤c) (plus : Bool) :
    ∃ E : Board n, ∃ path : Path B E, path.length≤tw r c ∧ blank E=F.loc 1 1 ∧
      IsCycle B E (F.loc r c) (if plus then F.loc 0 0 else F.loc 0 1)
        (if plus then F.loc 0 1 else F.loc 0 0) := by
  obtain ⟨C,P,lP,sC,bC,pC,qC⟩ := transport_at F hR hC B hb r c hr hc out
  have d (r c r' c' : Nat) (h1 : r<2) (h2 : c<2) (h3 : r'<2) (h4 : c'<2) (h : r≠r' ∨ c≠c') :=
    ne_loc F (r:=r) (c:=c) (r':=r') (c':=c') (by omega) (by omega) (by omega) (by omega) h
  have g (r c r' c' : Nat) (h1 : r<2) (h2 : c<2) (h3 : r'<2) (h4 : c'<2)
      (h : Nat.dist r r'+Nat.dist c c'=1) :=
    adj_loc F (r:=r) (c:=c) (r':=r') (c':=c') (by omega) (by omega) (by omega) (by omega) h
  have sx : B.symm (C (F.loc 1 0))=F.loc r c := by rw [sC]; simp
  have sp : B.symm (C (F.loc 0 0))=F.loc 0 0 := by rw [pC]; simp
  have sq : B.symm (C (F.loc 0 1))=F.loc 0 1 := by rw [qC]; simp
  cases plus
  · -- z → q → p → s → z cycles (q, p, s), that is (x, q, p) after conjugation
    obtain ⟨D,Q,lQ,bD,cyc⟩ := rotate C (F.loc 1 1) (F.loc 0 1) (F.loc 0 0) (F.loc 1 0) bC
      (g 1 1 0 1 (by omega) (by omega) (by omega) (by omega) (by simp [Nat.dist]))
      (g 0 1 0 0 (by omega) (by omega) (by omega) (by omega) (by simp [Nat.dist]))
      (g 0 0 1 0 (by omega) (by omega) (by omega) (by omega) (by simp [Nat.dist]))
      (g 1 0 1 1 (by omega) (by omega) (by omega) (by omega) (by simp [Nat.dist]))
      (d 0 1 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))
      (d 0 1 1 0 (by omega) (by omega) (by omega) (by omega) (by omega))
      (d 0 0 1 0 (by omega) (by omega) (by omega) (by omega) (by omega))
      (d 1 1 0 1 (by omega) (by omega) (by omega) (by omega) (by omega))
      (d 1 1 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))
      (d 1 1 1 0 (by omega) (by omega) (by omega) (by omega) (by omega))
    obtain ⟨E,R,lR,bE,cE⟩ := conj P Q (bD.trans bC.symm) cyc
    rw [sx,sp,sq] at cE
    refine ⟨E,R,by unfold tw; omega,bE.trans hb,?_⟩
    simpa using cE.rotate.rotate
  · -- z → s → p → q → z cycles (s, p, q), that is (x, p, q)
    obtain ⟨D,Q,lQ,bD,cyc⟩ := rotate C (F.loc 1 1) (F.loc 1 0) (F.loc 0 0) (F.loc 0 1) bC
      (g 1 1 1 0 (by omega) (by omega) (by omega) (by omega) (by simp [Nat.dist]))
      (g 1 0 0 0 (by omega) (by omega) (by omega) (by omega) (by simp [Nat.dist]))
      (g 0 0 0 1 (by omega) (by omega) (by omega) (by omega) (by simp [Nat.dist]))
      (g 0 1 1 1 (by omega) (by omega) (by omega) (by omega) (by simp [Nat.dist]))
      (d 1 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))
      (d 1 0 0 1 (by omega) (by omega) (by omega) (by omega) (by omega))
      (d 0 0 0 1 (by omega) (by omega) (by omega) (by omega) (by omega))
      (d 1 1 1 0 (by omega) (by omega) (by omega) (by omega) (by omega))
      (d 1 1 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))
      (d 1 1 0 1 (by omega) (by omega) (by omega) (by omega) (by omega))
    obtain ⟨E,R,lR,bE,cE⟩ := conj P Q (bD.trans bC.symm) cyc
    rw [sx,sp,sq] at cE
    refine ⟨E,R,by unfold tw; omega,bE.trans hb,?_⟩
    simpa using cE

/-- The length bound of one `t`-cycle in `F`. -/
def tcost : Nat := 2*(2*(F.R+F.C)+4*max F.R F.C)+4

omit [NeZero n] in
theorem tw_le {r c : Nat} (hr : r<F.R) (hc : c<F.C) : tw r c≤tcost F := by
  unfold tw tcost; omega

theorem tcycle (hR : 3≤F.R) (hC : 6≤F.C) (B : Board n) (hb : blank B=F.loc 1 1) (r c : Nat)
    (hr : r<F.R) (hc : c<F.C) (out : 2≤r ∨ 2≤c) (plus : Bool) :
    ∃ E : Board n, ∃ path : Path B E, path.length≤tcost F ∧ blank E=F.loc 1 1 ∧
      IsCycle B E (F.loc r c) (if plus then F.loc 0 0 else F.loc 0 1)
        (if plus then F.loc 0 1 else F.loc 0 0) := by
  obtain ⟨E,path,len,h⟩ := tcycle_at F hR hC B hb r c hr hc out plus
  exact ⟨E,path,len.trans (tw_le F hr hc),h⟩

/-- `t_x` with the blank starting and ending at `s = (1,0)`. -/
theorem tcycle_s_at (hR : 3≤F.R) (hC : 6≤F.C) (B : Board n) (hb : blank B=F.loc 1 0) (r c : Nat)
    (hr : r<F.R) (hc : c<F.C) (out : 2≤r ∨ 2≤c) (plus : Bool) :
    ∃ E : Board n, ∃ path : Path B E, path.length≤tw r c+2 ∧ blank E=F.loc 1 0 ∧
      IsCycle B E (F.loc r c) (if plus then F.loc 0 0 else F.loc 0 1)
        (if plus then F.loc 0 1 else F.loc 0 0) := by
  have d (r c r' c' : Nat) (h1 : r<F.R) (h2 : c<F.C) (h3 : r'<F.R) (h4 : c'<F.C) (h : r≠r' ∨ c≠c') :=
    ne_loc F h1 h2 h3 h4 h
  obtain ⟨C,P,lP,bC,sC,fC⟩ := move B (F.loc 1 0) (F.loc 1 1) hb
    (adj_loc F (by omega) (by omega) (by omega) (by omega) (by simp [Nat.dist]))
  obtain ⟨D,Q,lQ,bD,cyc⟩ := tcycle_at F hR hC C bC r c hr hc out plus
  obtain ⟨E,R,lR,bE,cE⟩ := conj P Q (bD.trans bC.symm) cyc
  have keep {x : Cell n} (h1 : x≠F.loc 1 0) (h2 : x≠F.loc 1 1) : B.symm (C x)=x := by
    rw [fC x h1 h2]; simp
  have kx := keep (d r c 1 0 hr hc (by omega) (by omega) (by omega))
    (d r c 1 1 hr hc (by omega) (by omega) (by omega))
  have kp := keep (d 0 0 1 0 (by omega) (by omega) (by omega) (by omega) (by omega))
    (d 0 0 1 1 (by omega) (by omega) (by omega) (by omega) (by omega))
  have kq := keep (d 0 1 1 0 (by omega) (by omega) (by omega) (by omega) (by omega))
    (d 0 1 1 1 (by omega) (by omega) (by omega) (by omega) (by omega))
  refine ⟨E,R,?_,bE.trans hb,?_⟩
  · omega
  · cases plus <;> simpa [kx,kp,kq] using cE

theorem tcycle_s (hR : 3≤F.R) (hC : 6≤F.C) (B : Board n) (hb : blank B=F.loc 1 0) (r c : Nat)
    (hr : r<F.R) (hc : c<F.C) (out : 2≤r ∨ 2≤c) (plus : Bool) :
    ∃ E : Board n, ∃ path : Path B E, path.length≤tcost F+2 ∧ blank E=F.loc 1 0 ∧
      IsCycle B E (F.loc r c) (if plus then F.loc 0 0 else F.loc 0 1)
        (if plus then F.loc 0 1 else F.loc 0 0) := by
  obtain ⟨E,path,len,h⟩ := tcycle_s_at F hR hC B hb r c hr hc out plus
  exact ⟨E,path,by have := tw_le F hr hc; omega,h⟩

/-- `t_x` with the blank starting and ending at a cell `w` next to `q = (0,1)`
outside the block: the walk `w → q → z` puts `z`'s tile on `q`, so the cycle
is `(x, p, z)` (`plus`) or `(x, z, p)`. -/
theorem tcycle_w (hR : 3≤F.R) (hC : 6≤F.C) (w : Cell n) (hw : gridDistance w (F.loc 0 1)=1)
    (wp : w≠F.loc 0 0) (wz : w≠F.loc 1 1) (B : Board n) (hb : blank B=w) (r c : Nat)
    (hr : r<F.R) (hc : c<F.C) (out : 2≤r ∨ 2≤c) (wx : w≠F.loc r c) (plus : Bool) :
    ∃ E : Board n, ∃ path : Path B E, path.length≤tcost F+4 ∧ blank E=w ∧
      IsCycle B E (F.loc r c) (if plus then F.loc 0 0 else F.loc 1 1)
        (if plus then F.loc 1 1 else F.loc 0 0) := by
  have d (r c r' c' : Nat) (h1 : r<F.R) (h2 : c<F.C) (h3 : r'<F.R) (h4 : c'<F.C) (h : r≠r' ∨ c≠c') :=
    ne_loc F h1 h2 h3 h4 h
  have wq : w≠F.loc 0 1 := by rintro rfl; simp at hw
  obtain ⟨C1,P1,l1,b1,s1,f1⟩ := move B w (F.loc 0 1) hb hw
  obtain ⟨C,P2,l2,bC,s2,f2⟩ := move C1 (F.loc 0 1) (F.loc 1 1) b1
    (adj_loc F (by omega) (by omega) (by omega) (by omega) (by simp [Nat.dist]))
  obtain ⟨D,Q,lQ,bD,cyc⟩ := tcycle F hR hC C bC r c hr hc out plus
  obtain ⟨E,R,lR,bE,cE⟩ := conj (P1.append P2) Q (bD.trans bC.symm) cyc
  have q11 : F.loc 0 1≠F.loc 1 1 := d 0 1 1 1 (by omega) (by omega) (by omega) (by omega) (by omega)
  have keep {x : Cell n} (h0 : x≠w) (h1 : x≠F.loc 0 1) (h2 : x≠F.loc 1 1) : B.symm (C x)=x := by
    rw [f2 x h1 h2,f1 x h0 h1]; simp
  have kx := keep (Ne.symm wx) (d r c 0 1 hr hc (by omega) (by omega) (by omega))
    (d r c 1 1 hr hc (by omega) (by omega) (by omega))
  have kp := keep (Ne.symm wp) (d 0 0 0 1 (by omega) (by omega) (by omega) (by omega) (by omega))
    (d 0 0 1 1 (by omega) (by omega) (by omega) (by omega) (by omega))
  have kq : B.symm (C (F.loc 0 1))=F.loc 1 1 := by rw [s2,f1 _ (Ne.symm wz) q11.symm]; simp
  refine ⟨E,R,?_,bE.trans hb,?_⟩
  · simp only [Path.length_append] at lR; omega
  · cases plus <;> simpa [kx,kp,kq] using cE

/-- `tcycle_w`, charged by the position of `x`. -/
theorem tcycle_w_at (hR : 3≤F.R) (hC : 6≤F.C) (w : Cell n) (hw : gridDistance w (F.loc 0 1)=1)
    (wp : w≠F.loc 0 0) (wz : w≠F.loc 1 1) (B : Board n) (hb : blank B=w) (r c : Nat)
    (hr : r<F.R) (hc : c<F.C) (out : 2≤r ∨ 2≤c) (wx : w≠F.loc r c) (plus : Bool) :
    ∃ E : Board n, ∃ path : Path B E, path.length≤tw r c+4 ∧ blank E=w ∧
      IsCycle B E (F.loc r c) (if plus then F.loc 0 0 else F.loc 1 1)
        (if plus then F.loc 1 1 else F.loc 0 0) := by
  have d (r c r' c' : Nat) (h1 : r<F.R) (h2 : c<F.C) (h3 : r'<F.R) (h4 : c'<F.C) (h : r≠r' ∨ c≠c') :=
    ne_loc F h1 h2 h3 h4 h
  have wq : w≠F.loc 0 1 := by rintro rfl; simp at hw
  obtain ⟨C1,P1,l1,b1,s1,f1⟩ := move B w (F.loc 0 1) hb hw
  obtain ⟨C,P2,l2,bC,s2,f2⟩ := move C1 (F.loc 0 1) (F.loc 1 1) b1
    (adj_loc F (by omega) (by omega) (by omega) (by omega) (by simp [Nat.dist]))
  obtain ⟨D,Q,lQ,bD,cyc⟩ := tcycle_at F hR hC C bC r c hr hc out plus
  obtain ⟨E,R,lR,bE,cE⟩ := conj (P1.append P2) Q (bD.trans bC.symm) cyc
  have q11 : F.loc 0 1≠F.loc 1 1 := d 0 1 1 1 (by omega) (by omega) (by omega) (by omega) (by omega)
  have keep {x : Cell n} (h0 : x≠w) (h1 : x≠F.loc 0 1) (h2 : x≠F.loc 1 1) : B.symm (C x)=x := by
    rw [f2 x h1 h2,f1 x h0 h1]; simp
  have kx := keep (Ne.symm wx) (d r c 0 1 hr hc (by omega) (by omega) (by omega))
    (d r c 1 1 hr hc (by omega) (by omega) (by omega))
  have kp := keep (Ne.symm wp) (d 0 0 0 1 (by omega) (by omega) (by omega) (by omega) (by omega))
    (d 0 0 1 1 (by omega) (by omega) (by omega) (by omega) (by omega))
  have kq : B.symm (C (F.loc 0 1))=F.loc 1 1 := by rw [s2,f1 _ (Ne.symm wz) q11.symm]; simp
  refine ⟨E,R,?_,bE.trans hb,?_⟩
  · simp only [Path.length_append] at lR; omega
  · cases plus <;> simpa [kx,kp,kq] using cE

/-- A three-cycle `(p, x, y)` through the block corner `p = (0,0)`: `t_x⁺`
conjugated by `t_y⁻`, where `t_y` runs in a second frame `G` with the same
block. The blank starts and ends at `s = (1,0)`. -/
theorem tdirect (G : Frame n) (hR : 3≤F.R) (hC : 6≤F.C) (hR' : 3≤G.R) (hC' : 6≤G.C)
    (blk : ∀ i j, i<2 → j<2 → G.loc i j=F.loc i j) (B : Board n) (hb : blank B=F.loc 1 0)
    (r c : Nat) (hr : r<F.R) (hc : c<F.C) (out : 2≤r ∨ 2≤c)
    (r' c' : Nat) (hr' : r'<G.R) (hc' : c'<G.C) (out' : 2≤r' ∨ 2≤c') (xy : F.loc r c≠G.loc r' c') :
    ∃ E : Board n, ∃ path : Path B E, path.length≤2*(tcost G+2)+(tcost F+2) ∧ blank E=F.loc 1 0 ∧
      IsCycle B E (F.loc 0 0) (F.loc r c) (G.loc r' c') := by
  obtain ⟨C,P,lP,bC,cP⟩ := tcycle_s G hR' hC' B (by rw [blk 1 0 (by omega) (by omega)]; exact hb)
    r' c' hr' hc' out' false
  simp only [Bool.false_eq_true,if_false,blk 0 1 (by omega) (by omega),blk 0 0 (by omega) (by omega)] at cP
  rw [blk 1 0 (by omega) (by omega)] at bC
  obtain ⟨D,Q,lQ,bD,cQ⟩ := tcycle_s F hR hC C bC r c hr hc out true
  simp only [if_true] at cQ
  obtain ⟨E,R,lR,bE,cE⟩ := conj P Q (bD.trans bC.symm) cQ
  have ex : F.loc r c≠F.loc 0 1 := ne_loc F hr hc (by omega) (by omega) (by omega)
  have ep : F.loc r c≠F.loc 0 0 := ne_loc F hr hc (by omega) (by omega) (by omega)
  have kx : B.symm (C (F.loc r c))=F.loc r c := by rw [cP.2.2.2 _ xy ex ep]; simp
  have kp : B.symm (C (F.loc 0 0))=G.loc r' c' := by rw [cP.2.2.1]; simp
  have kq : B.symm (C (F.loc 0 1))=F.loc 0 0 := by rw [cP.2.1]; simp
  rw [kx,kp,kq] at cE
  exact ⟨E,R,by omega,bE.trans hb,cE.rotate.rotate⟩

/-- `tdirect` charged by the position of `x`: `t_x⁺` costs its own weight. -/
theorem tdirect_at (G : Frame n) (hR : 3≤F.R) (hC : 6≤F.C) (hR' : 3≤G.R) (hC' : 6≤G.C)
    (blk : ∀ i j, i<2 → j<2 → G.loc i j=F.loc i j) (B : Board n) (hb : blank B=F.loc 1 0)
    (r c : Nat) (hr : r<F.R) (hc : c<F.C) (out : 2≤r ∨ 2≤c)
    (r' c' : Nat) (hr' : r'<G.R) (hc' : c'<G.C) (out' : 2≤r' ∨ 2≤c') (xy : F.loc r c≠G.loc r' c') :
    ∃ E : Board n, ∃ path : Path B E, path.length≤2*(tcost G+2)+(tw r c+2) ∧ blank E=F.loc 1 0 ∧
      IsCycle B E (F.loc 0 0) (F.loc r c) (G.loc r' c') := by
  obtain ⟨C,P,lP,bC,cP⟩ := tcycle_s G hR' hC' B (by rw [blk 1 0 (by omega) (by omega)]; exact hb)
    r' c' hr' hc' out' false
  simp only [Bool.false_eq_true,if_false,blk 0 1 (by omega) (by omega),blk 0 0 (by omega) (by omega)] at cP
  rw [blk 1 0 (by omega) (by omega)] at bC
  obtain ⟨D,Q,lQ,bD,cQ⟩ := tcycle_s_at F hR hC C bC r c hr hc out true
  simp only [if_true] at cQ
  obtain ⟨E,R,lR,bE,cE⟩ := conj P Q (bD.trans bC.symm) cQ
  have ex : F.loc r c≠F.loc 0 1 := ne_loc F hr hc (by omega) (by omega) (by omega)
  have ep : F.loc r c≠F.loc 0 0 := ne_loc F hr hc (by omega) (by omega) (by omega)
  have kx : B.symm (C (F.loc r c))=F.loc r c := by rw [cP.2.2.2 _ xy ex ep]; simp
  have kp : B.symm (C (F.loc 0 0))=G.loc r' c' := by rw [cP.2.2.1]; simp
  have kq : B.symm (C (F.loc 0 1))=F.loc 0 0 := by rw [cP.2.1]; simp
  rw [kx,kp,kq] at cE
  exact ⟨E,R,by omega,bE.trans hb,cE.rotate.rotate⟩

/-- `tdirect` with both `t`-cycles charged by position. -/
theorem tdirect_at2 (G : Frame n) (hR : 3≤F.R) (hC : 6≤F.C) (hR' : 3≤G.R) (hC' : 6≤G.C)
    (blk : ∀ i j, i<2 → j<2 → G.loc i j=F.loc i j) (B : Board n) (hb : blank B=F.loc 1 0)
    (r c : Nat) (hr : r<F.R) (hc : c<F.C) (out : 2≤r ∨ 2≤c)
    (r' c' : Nat) (hr' : r'<G.R) (hc' : c'<G.C) (out' : 2≤r' ∨ 2≤c') (xy : F.loc r c≠G.loc r' c') :
    ∃ E : Board n, ∃ path : Path B E, path.length≤2*(tw r' c'+2)+(tw r c+2) ∧ blank E=F.loc 1 0 ∧
      IsCycle B E (F.loc 0 0) (F.loc r c) (G.loc r' c') := by
  obtain ⟨C,P,lP,bC,cP⟩ := tcycle_s_at G hR' hC' B (by rw [blk 1 0 (by omega) (by omega)]; exact hb)
    r' c' hr' hc' out' false
  simp only [Bool.false_eq_true,if_false,blk 0 1 (by omega) (by omega),blk 0 0 (by omega) (by omega)] at cP
  rw [blk 1 0 (by omega) (by omega)] at bC
  obtain ⟨D,Q,lQ,bD,cQ⟩ := tcycle_s_at F hR hC C bC r c hr hc out true
  simp only [if_true] at cQ
  obtain ⟨E,R,lR,bE,cE⟩ := conj P Q (bD.trans bC.symm) cQ
  have ex : F.loc r c≠F.loc 0 1 := ne_loc F hr hc (by omega) (by omega) (by omega)
  have ep : F.loc r c≠F.loc 0 0 := ne_loc F hr hc (by omega) (by omega) (by omega)
  have kx : B.symm (C (F.loc r c))=F.loc r c := by rw [cP.2.2.2 _ xy ex ep]; simp
  have kp : B.symm (C (F.loc 0 0))=G.loc r' c' := by rw [cP.2.2.1]; simp
  have kq : B.symm (C (F.loc 0 1))=F.loc 0 0 := by rw [cP.2.1]; simp
  rw [kx,kp,kq] at cE
  exact ⟨E,R,by omega,bE.trans hb,cE.rotate.rotate⟩

omit [NeZero n] in
/-- `a⁺ c⁻ b⁺ a⁻ = (a b c)` when `a, b, c, p, q` are distinct. -/
theorem compose {B0 B1 B2 B3 B4 : Board n} {a b c p q : Cell n}
    (h1 : IsCycle B0 B1 a p q) (h2 : IsCycle B1 B2 c q p) (h3 : IsCycle B2 B3 b p q)
    (h4 : IsCycle B3 B4 a q p) (ab : a≠b) (ac : a≠c) (bc : b≠c) (ap : a≠p) (aq : a≠q)
    (bp : b≠p) (bq : b≠q) (cp : c≠p) (cq : c≠q) (pq : p≠q) : IsCycle B0 B4 a b c := by
  obtain ⟨a1,p1,q1,f1⟩ := h1
  obtain ⟨c2,q2,p2,f2⟩ := h2
  obtain ⟨b3,p3,q3,f3⟩ := h3
  obtain ⟨a4,q4,p4,f4⟩ := h4
  refine ⟨?_,?_,?_,?_⟩
  · rw [a4,q3,f2 _ bc bq bp,f1 _ (Ne.symm ab) bp bq]
  · rw [f4 _ (Ne.symm ab) bq bp,b3,p2,f1 _ (Ne.symm ac) cp cq]
  · rw [f4 _ (Ne.symm ac) cq cp,f3 _ (Ne.symm bc) cp cq,c2,q1]
  · intro y ya yb yc
    by_cases yp : y=p
    · subst yp; rw [p4,f3 _ ab ap aq,f2 _ ac aq ap,a1]
    by_cases yq : y=q
    · subst yq; rw [q4,p3,q2,p1]
    rw [f4 _ ya yq yp,f3 _ yb yp yq,f2 _ yc yq yp,f1 _ ya yp yq]

/-- The corner block of the frame. -/
def InBlock (x : Cell n) : Prop := ∃ i j, i<2 ∧ j<2 ∧ F.loc i j=x

omit [NeZero n] in
theorem out_coords (full : ∀ y, ∃ r c, r<F.R ∧ c<F.C ∧ F.loc r c=y) {x : Cell n}
    (hx : ¬InBlock F x) : ∃ r c, r<F.R ∧ c<F.C ∧ (2≤r ∨ 2≤c) ∧ F.loc r c=x := by
  obtain ⟨r,c,hr,hc,e⟩ := full x
  refine ⟨r,c,hr,hc,?_,e⟩
  by_contra h
  exact hx ⟨r,c,by omega,by omega,e⟩

/-- With the blank at `z`, cycle any three distinct cells outside the block.
Stage `a` into `s` once. On the staged board, `ρ⁺ c'⁻ b'⁺ ρ⁻` (with `ρ` the
block rotation and `x'±` the cycles of the moved tiles) is the cycle
`(s b' c')`, because each `t_x` is a conjugation and restores `s`. Six tile
trips in all. -/
theorem core (hR : 3≤F.R) (hC : 6≤F.C) (full : ∀ y, ∃ r c, r<F.R ∧ c<F.C ∧ F.loc r c=y)
    (B : Board n) (hb : blank B=F.loc 1 1) {a b c : Cell n}
    (ha : ¬InBlock F a) (hb' : ¬InBlock F b) (hc : ¬InBlock F c) (ab : a≠b) (ac : a≠c) (bc : b≠c) :
    ∃ E : Board n, ∃ path : Path B E, path.length≤6*(2*(F.R+F.C)+4*max F.R F.C)+16 ∧ blank E=F.loc 1 1 ∧
      IsCycle B E a b c := by
  obtain ⟨ra,ca,hra,hca,oa,rfl⟩ := out_coords F full ha
  obtain ⟨C,P,lP,sC,bC,pC,qC⟩ := transport F hR hC B hb ra ca hra hca oa
  have d (r c r' c' : Nat) (h1 : r<2) (h2 : c<2) (h3 : r'<2) (h4 : c'<2) (h : r≠r' ∨ c≠c') :=
    ne_loc F (r:=r) (c:=c) (r':=r') (c':=c') (by omega) (by omega) (by omega) (by omega) h
  have g (r c r' c' : Nat) (h1 : r<2) (h2 : c<2) (h3 : r'<2) (h4 : c'<2)
      (h : Nat.dist r r'+Nat.dist c c'=1) :=
    adj_loc F (r:=r) (c:=c) (r':=r') (c':=c') (by omega) (by omega) (by omega) (by omega) h
  have zero : C (blank C)=0 := by simp [blank,position]
  have bz : B (blank B)=0 := by simp [blank,position]
  -- the other two tiles are still outside the block
  have moved {x : Cell n} (hx : ¬InBlock F x) (hxa : x≠F.loc ra ca) : ¬InBlock F (C.symm (B x)) := by
    rintro ⟨i,j,hi,hj,e⟩
    have e' : C (F.loc i j)=B x := by rw [e]; simp
    have xb : B x≠0 := fun h =>
      hx ⟨1,1,by omega,by omega,by rw [← hb]; exact (B.injective (h.trans bz.symm)).symm⟩
    rcases (by omega : (i=0∧j=0) ∨ (i=0∧j=1) ∨ (i=1∧j=0) ∨ (i=1∧j=1)) with
      ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · rw [pC] at e'; exact hx ⟨0,0,by omega,by omega,B.injective e'⟩
    · rw [qC] at e'; exact hx ⟨0,1,by omega,by omega,B.injective e'⟩
    · rw [sC] at e'; exact hxa (B.injective e').symm
    · rw [← bC,zero] at e'; exact xb e'.symm
  set b' := C.symm (B b) with hbdef
  set c' := C.symm (B c) with hcdef
  have ob' := moved hb' (Ne.symm ab)
  have oc' := moved hc (Ne.symm ac)
  have bc' : b'≠c' := fun e => bc (B.injective (C.symm.injective e))
  obtain ⟨rb,cb,hrb,hcb,obb,eb⟩ := out_coords F full ob'
  obtain ⟨rc,cc,hrc,hcc,occ,ec⟩ := out_coords F full oc'
  -- ρ⁺ : cycle (s p q)
  obtain ⟨D1,q1,l1,bD1,h1⟩ := rotate C (F.loc 1 1) (F.loc 1 0) (F.loc 0 0) (F.loc 0 1) bC
    (g 1 1 1 0 (by omega) (by omega) (by omega) (by omega) (by simp [Nat.dist]))
    (g 1 0 0 0 (by omega) (by omega) (by omega) (by omega) (by simp [Nat.dist]))
    (g 0 0 0 1 (by omega) (by omega) (by omega) (by omega) (by simp [Nat.dist]))
    (g 0 1 1 1 (by omega) (by omega) (by omega) (by omega) (by simp [Nat.dist]))
    (d 1 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))
    (d 1 0 0 1 (by omega) (by omega) (by omega) (by omega) (by omega))
    (d 0 0 0 1 (by omega) (by omega) (by omega) (by omega) (by omega))
    (d 1 1 1 0 (by omega) (by omega) (by omega) (by omega) (by omega))
    (d 1 1 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))
    (d 1 1 0 1 (by omega) (by omega) (by omega) (by omega) (by omega))
  obtain ⟨D2,q2,l2,bD2,h2⟩ := tcycle F hR hC D1 bD1 rc cc hrc hcc occ false
  obtain ⟨D3,q3,l3,bD3,h3⟩ := tcycle F hR hC D2 bD2 rb cb hrb hcb obb true
  -- ρ⁻ : cycle (q p s), that is (s q p)
  obtain ⟨D4,q4,l4,bD4,h4⟩ := rotate D3 (F.loc 1 1) (F.loc 0 1) (F.loc 0 0) (F.loc 1 0) bD3
    (g 1 1 0 1 (by omega) (by omega) (by omega) (by omega) (by simp [Nat.dist]))
    (g 0 1 0 0 (by omega) (by omega) (by omega) (by omega) (by simp [Nat.dist]))
    (g 0 0 1 0 (by omega) (by omega) (by omega) (by omega) (by simp [Nat.dist]))
    (g 1 0 1 1 (by omega) (by omega) (by omega) (by omega) (by simp [Nat.dist]))
    (d 0 1 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))
    (d 0 1 1 0 (by omega) (by omega) (by omega) (by omega) (by omega))
    (d 0 0 1 0 (by omega) (by omega) (by omega) (by omega) (by omega))
    (d 1 1 0 1 (by omega) (by omega) (by omega) (by omega) (by omega))
    (d 1 1 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))
    (d 1 1 1 0 (by omega) (by omega) (by omega) (by omega) (by omega))
  simp only [if_true,Bool.false_eq_true,if_false] at h2 h3
  rw [ec] at h2
  rw [eb] at h3
  have blk {x : Cell n} (hx : ¬InBlock F x) (i j : Nat) (hi : i<2) (hj : j<2) : x≠F.loc i j :=
    fun e => hx ⟨i,j,hi,hj,e.symm⟩
  have cyc : IsCycle C D4 (F.loc 1 0) b' c' :=
    compose h1 h2 h3 h4.rotate.rotate (blk ob' 1 0 (by omega) (by omega)).symm
      (blk oc' 1 0 (by omega) (by omega)).symm bc'
      (d 1 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))
      (d 1 0 0 1 (by omega) (by omega) (by omega) (by omega) (by omega))
      (blk ob' 0 0 (by omega) (by omega)) (blk ob' 0 1 (by omega) (by omega))
      (blk oc' 0 0 (by omega) (by omega)) (blk oc' 0 1 (by omega) (by omega))
      (d 0 0 0 1 (by omega) (by omega) (by omega) (by omega) (by omega))
  obtain ⟨E,R,lR,bE,cE⟩ := conj P (((q1.append q2).append q3).append q4) (bD4.trans bC.symm) cyc
  have e1 : B.symm (C (F.loc 1 0))=F.loc ra ca := by rw [sC]; simp
  have e2 : B.symm (C b')=b := by rw [hbdef]; simp
  have e3 : B.symm (C c')=c := by rw [hcdef]; simp
  rw [e1,e2,e3] at cE
  refine ⟨E,R,?_,bE.trans hb,cE⟩
  simp only [Path.length_append] at lR
  unfold tcost at l2 l3
  omega

/-- Bring the blank to `z`. Afterwards no tile from outside the block is in it. -/
theorem normalize (hR : 6≤F.R) (hC : 6≤F.C) (full : ∀ y, ∃ r c, r<F.R ∧ c<F.C ∧ F.loc r c=y)
    (B : Board n) :
    ∃ C : Board n, ∃ path : Path B C, path.length+2≤F.R+F.C ∧ blank C=F.loc 1 1 ∧
      ∀ x, ¬InBlock F x → B x≠0 → ∀ y, InBlock F y → C y≠B x := by
  obtain ⟨r,c,hr,hc,hw⟩ := full (blank B)
  have hb : blank B=F.loc r c := hw.symm
  have zero (D : Board n) : D (blank D)=0 := by simp [blank,position]
  -- inside the block: a route through block cells only
  have inside (C : Board n) (path : Path B C) (len : path.length+2≤F.R+F.C) (bC : blank C=F.loc 1 1)
      (l : List (Cell n)) (lin : ∀ y∈l, InBlock F y) (fix : ∀ y, y∉l → C y=B y) :
      ∃ C : Board n, ∃ path : Path B C, path.length+2≤F.R+F.C ∧ blank C=F.loc 1 1 ∧
        ∀ x, ¬InBlock F x → B x≠0 → ∀ y, InBlock F y → C y≠B x := by
    refine ⟨C,path,len,bC,fun x hx _ y hy e => ?_⟩
    have cx : C x=B x := fix x (fun m => hx (lin x m))
    have := C.injective (e.trans cx.symm)
    subst this; exact hx hy
  -- outside the block: enter it only at `z`
  have outside (C : Board n) (path : Path B C) (len : path.length+2≤F.R+F.C) (bC : blank C=F.loc 1 1)
      (f0 : C (F.loc 0 0)=B (F.loc 0 0)) (f1 : C (F.loc 0 1)=B (F.loc 0 1))
      (f2 : C (F.loc 1 0)=B (F.loc 1 0)) :
      ∃ C : Board n, ∃ path : Path B C, path.length+2≤F.R+F.C ∧ blank C=F.loc 1 1 ∧
        ∀ x, ¬InBlock F x → B x≠0 → ∀ y, InBlock F y → C y≠B x := by
    refine ⟨C,path,len,bC,fun x hx hx0 y hy e => ?_⟩
    obtain ⟨i,j,hi,hj,rfl⟩ := hy
    have ne : F.loc i j≠x := fun h => hx ⟨i,j,hi,hj,h⟩
    have key : C (F.loc i j)=B (F.loc i j) ∨ F.loc i j=F.loc 1 1 := by
      rcases (by omega : (i=0∧j=0) ∨ (i=0∧j=1) ∨ (i=1∧j=0) ∨ (i=1∧j=1)) with
        ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact Or.inl f0
      · exact Or.inl f1
      · exact Or.inl f2
      · exact Or.inr rfl
    rcases key with k | k
    · exact ne (B.injective (k.symm.trans e))
    · rw [k,← bC,zero] at e; exact hx0 e.symm
  rcases Nat.lt_or_ge r 2 with hr2 | hr2 <;> rcases Nat.lt_or_ge c 2 with hc2 | hc2
  · -- in the block
    rcases (by omega : (r=0∧c=0) ∨ (r=0∧c=1) ∨ (r=1∧c=0) ∨ (r=1∧c=1)) with
      ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · have chain : Chained [F.loc 0 0,F.loc 0 1,F.loc 1 1] := by chain_tac
      obtain ⟨C,p,l,bC,fix,_⟩ := route B _ _ chain hb
      exact inside C p (by simp at l; omega) bC _
        (by simp only [List.mem_cons,List.not_mem_nil,or_false]; rintro y (rfl|rfl|rfl) <;>
          exact ⟨_,_,by omega,by omega,rfl⟩) fix
    · have chain : Chained [F.loc 0 1,F.loc 1 1] := by chain_tac
      obtain ⟨C,p,l,bC,fix,_⟩ := route B _ _ chain hb
      exact inside C p (by simp at l; omega) bC _
        (by simp only [List.mem_cons,List.not_mem_nil,or_false]; rintro y (rfl|rfl) <;>
          exact ⟨_,_,by omega,by omega,rfl⟩) fix
    · have chain : Chained [F.loc 1 0,F.loc 1 1] := by chain_tac
      obtain ⟨C,p,l,bC,fix,_⟩ := route B _ _ chain hb
      exact inside C p (by simp at l; omega) bC _
        (by simp only [List.mem_cons,List.not_mem_nil,or_false]; rintro y (rfl|rfl) <;>
          exact ⟨_,_,by omega,by omega,rfl⟩) fix
    · exact inside B (.nil B) (by simp; omega) hb [] (by simp) (fun _ _ => rfl)
  · -- top rows, right of the block
    have toRow1 : ∃ C1 : Board n, ∃ p1 : Path B C1, p1.length≤r+1 ∧ blank C1=F.loc 1 c ∧
        C1 (F.loc 0 0)=B (F.loc 0 0) ∧ C1 (F.loc 0 1)=B (F.loc 0 1) ∧ C1 (F.loc 1 0)=B (F.loc 1 0) := by
      rcases Nat.lt_or_ge r 1 with h0 | h1
      · have r0 : r=0 := by omega
        subst r0
        have chain : Chained [F.loc 0 c,F.loc 1 c] := by chain_tac
        obtain ⟨C,p,l,bC,fix,_⟩ := route B _ _ chain hb
        refine ⟨C,p,by simp at l; omega,bC,fix _ (by notmem_tac),fix _ (by notmem_tac),
          fix _ (by notmem_tac)⟩
      · have r1 : r=1 := by omega
        subst r1
        exact ⟨B,.nil B,by simp,hb,rfl,rfl,rfl⟩
    obtain ⟨C1,p1,l1,b1,g0,g1,g2⟩ := toRow1
    obtain ⟨C,p2,l2,b2,f2⟩ := walkRowLeft F C1 1 1 (c-1) (by omega) (by omega)
      (by rw [b1]; congr 1; omega)
    exact outside C (p1.append p2) (by simp; omega) b2
      (by rw [f2 0 0 (by omega) (by omega) (by omega),g0])
      (by rw [f2 0 1 (by omega) (by omega) (by omega),g1])
      (by rw [f2 1 0 (by omega) (by omega) (by omega),g2])
  · -- left columns, below the block
    obtain ⟨C1,p1,l1,b1,f1⟩ := walkColUp F B c 2 (r-2) hc (by omega) (by rw [hb]; congr 1; omega)
    have g (i j : Nat) (hi : i<2) (hj : j<2) : C1 (F.loc i j)=B (F.loc i j) :=
      f1 i j (by omega) (by omega) (by omega)
    rcases (by omega : c=0 ∨ c=1) with rfl|rfl
    · have chain : Chained [F.loc 2 0,F.loc 2 1,F.loc 1 1] := by chain_tac
      obtain ⟨C,p2,l2,b2,f2,_⟩ := route C1 _ _ chain b1
      exact outside C (p1.append p2) (by simp at l2 ⊢; omega) b2
        (by rw [f2 _ (by notmem_tac),g 0 0 (by omega) (by omega)])
        (by rw [f2 _ (by notmem_tac),g 0 1 (by omega) (by omega)])
        (by rw [f2 _ (by notmem_tac),g 1 0 (by omega) (by omega)])
    · have chain : Chained [F.loc 2 1,F.loc 1 1] := by chain_tac
      obtain ⟨C,p2,l2,b2,f2,_⟩ := route C1 _ _ chain b1
      exact outside C (p1.append p2) (by simp at l2 ⊢; omega) b2
        (by rw [f2 _ (by notmem_tac),g 0 0 (by omega) (by omega)])
        (by rw [f2 _ (by notmem_tac),g 0 1 (by omega) (by omega)])
        (by rw [f2 _ (by notmem_tac),g 1 0 (by omega) (by omega)])
  · -- elsewhere: up the column to row 1, then left along row 1
    obtain ⟨C1,p1,l1,b1,f1⟩ := walkColUp F B c 1 (r-1) hc (by omega) (by rw [hb]; congr 1; omega)
    obtain ⟨C,p2,l2,b2,f2⟩ := walkRowLeft F C1 1 1 (c-1) (by omega) (by omega)
      (by rw [b1]; congr 1; omega)
    exact outside C (p1.append p2) (by simp; omega) b2
      (by rw [f2 0 0 (by omega) (by omega) (by omega),f1 0 0 (by omega) (by omega) (by omega)])
      (by rw [f2 0 1 (by omega) (by omega) (by omega),f1 0 1 (by omega) (by omega) (by omega)])
      (by rw [f2 1 0 (by omega) (by omega) (by omega),f1 1 0 (by omega) (by omega) (by omega)])

/-! ### Choosing the corner -/

/-- Which end of an axis a coordinate is near, if any. -/
def side2 (n v : Nat) : Option Bool := if v<2 then some false else if n-2≤v then some true else none

/-- The corner block a cell lies in, if any. -/
def corner (y : Cell n) : Option (Bool × Bool) :=
  match side2 n y.1.val,side2 n y.2.val with
  | some a,some b => some (a,b)
  | _,_ => none

theorem corner_of_block (hn : 6≤n) (fr fc : Bool) {y : Cell n} (h : InBlock (frame n fr fc).toFrame y) :
    corner y=some (fr,fc) := by
  obtain ⟨i,j,hi,hj,rfl⟩ := h
  have e := (frame n fr fc).loc_eq (r:=i) (c:=j) (by omega) (by omega)
  have r1 : ((frame n fr fc).loc i j).1.val=axis n 0 fr i := by rw [e]; rfl
  have c1 : ((frame n fr fc).loc i j).2.val=axis n 0 fc j := by rw [e]; rfl
  have sd (fl : Bool) (x : Nat) (hx : x<2) : side2 n (axis n 0 fl x)=some fl := by
    cases fl <;> simp only [side2,axis,Bool.false_eq_true,if_false,if_true] <;> split_ifs <;>
      first | rfl | omega
  unfold corner
  change (match side2 n ((frame n fr fc).loc i j).1.val,side2 n ((frame n fr fc).loc i j).2.val with
    | some a,some b => some (a,b)
    | _,_ => none)=_
  rw [r1,c1,sd fr i hi,sd fc j hj]

theorem exists_free_corner (o1 o2 o3 : Option (Bool × Bool)) :
    ∃ k : Bool × Bool, some k≠o1 ∧ some k≠o2 ∧ some k≠o3 := by
  revert o1 o2 o3; decide

end SlidingPuzzle.NestedRouting.Cycle3

namespace SlidingPuzzle
open NestedRouting NestedRouting.Routes NestedRouting.Cycle3

/-- Cycle the tiles of any three distinct non-blank cells in at most `54n`
moves, restoring the blank and every other cell. -/
theorem exists_three_cycle {n : Nat} [NeZero n] (B : Board n) (hn : 6≤n) (a b c : Cell n)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c) (ha : B a≠0) (hb : B b≠0) (hc : B c≠0) :
    ∃ C : Board n, ∃ p : Path B C, p.length≤54*n ∧ blank C=blank B ∧
      C a=B b ∧ C b=B c ∧ C c=B a ∧ ∀ x, x≠a → x≠b → x≠c → C x=B x := by
  obtain ⟨⟨fr,fc⟩,k1,k2,k3⟩ := exists_free_corner (corner a) (corner b) (corner c)
  set F := (frame n fr fc).toFrame
  have FR : F.R=n := rfl
  have FC : F.C=n := rfl
  have full : ∀ y, ∃ r c, r<F.R ∧ c<F.C ∧ F.loc r c=y := fun y => exists_loc (frame n fr fc) y
  have out {x : Cell n} (k : some (fr,fc)≠corner x) : ¬InBlock F x :=
    fun h => k (corner_of_block hn fr fc h).symm
  obtain ⟨C,N,lN,bC,keep⟩ := normalize F (by omega) (by omega) full B
  have moved {x : Cell n} (k : some (fr,fc)≠corner x) (hx : B x≠0) : ¬InBlock F (C.symm (B x)) :=
    fun h => keep x (out k) hx _ h (by simp)
  have sne {x y : Cell n} (h : x≠y) : C.symm (B x)≠C.symm (B y) :=
    fun e => h (B.injective (C.symm.injective e))
  obtain ⟨E,Q,lQ,bE,cyc⟩ := core F (by omega) (by omega) full C bC (moved k1 ha) (moved k2 hb) (moved k3 hc)
    (sne hab) (sne hac) (sne hbc)
  obtain ⟨G,R,lR,bG,h1,h2,h3,h4⟩ := conj N Q (bE.trans bC.symm) cyc
  simp only [Equiv.apply_symm_apply,Equiv.symm_apply_apply] at h1 h2 h3 h4
  rw [FR,FC] at lQ lN
  have : max n n=n := max_self n
  exact ⟨G,R,by omega,bG,h1,h2,h3,h4⟩

end SlidingPuzzle
