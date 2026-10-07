import NestedRouting.Star.Congr

/-! The wrapper of a request: swap the input at `eP` into the carrier,
walk the blank to the hub, run an inner operation, walk back and swap the
carrier's final tile out to `eP`. Everything outside the services'
footprint is restored, the carrier gets its seed back. -/
namespace SlidingPuzzle.NestedRouting.Interface
open Finset TileRoles
open SlidingPuzzle.NestedRouting.ReservePolicy

variable {n : Nat} [NeZero n] {J : Nat}

namespace StarSpec
variable (P : StarSpec n J)

def conn : List (Cell n) := P.zP :: P.connTail

def wrapCost : Nat := 2*P.wcost+2*P.connTail.length

theorem eP_cells : P.eP∉P.frame.cells := (P.frame.entry_input ⟨rfl,rfl⟩)
theorem zP_cells : P.zP∉P.frame.cells := (P.frame.entry_blank ⟨rfl,rfl⟩)

theorem foot_ne_eP {y : Cell n} (hy : P.foot y) : y≠P.eP := fun e => P.eP_cells (e ▸ P.foot_cells hy)

/-- A cell off every loop and child, other than the carrier, is no part of a
service footprint. -/
theorem not_foot {c : Cell n} (hl : ∀ j, c∉P.L.loop j) (hc : ∀ j, c∉(P.Q j).cells)
    (hK : c≠P.L.hub P.L.K) : ¬P.foot c := by
  rintro (⟨j,h | h | h⟩ | h)
  · exact hl j (P.L.mem_loop_of_exportQ h)
  · exact hl j (P.L.mem_loop_of_deliveryQ h)
  · exact hc j h
  · exact hK h

theorem not_foot_wc : ¬P.foot P.wc := P.not_foot P.wc_loop P.wc_child P.wc_K

theorem conn_not_foot {c : Cell n} (hc : c∈P.conn) : ¬P.foot c := by
  obtain ⟨hl,hK⟩ := P.conn_free c hc
  rintro (⟨j,h | h | h⟩ | h)
  · exact (hl j).1 h
  · exact (hl j).2.1 h
  · exact (hl j).2.2 h
  · exact hK h

theorem foot_not_conn {y : Cell n} (hy : P.foot y) : y∉P.conn := fun hc => P.conn_not_foot hc hy

/-- The wrapper. `Φ` is whatever the inner operation guarantees about its
final board and its length. -/
theorem exists_wrapped {B : Board n} (atZ : blank B=P.zP) (Φ : Board n → Nat → Prop)
    (inner : ∀ B2 : Board n, Path B B2 → blank B2=P.L.hub P.L.w →
      (∀ y, P.foot y → y≠P.L.hub P.L.K → B2 y=B y) → B2 (P.L.hub P.L.K)=B P.eP →
      ∃ D : Board n, ∃ q : Path B2 D, blank D=P.L.hub P.L.w ∧ (∀ y, ¬P.foot y → D y=B2 y) ∧
        Φ D q.length) :
    ∃ C : Board n, ∃ path : Path B C, ∃ D : Board n, ∃ len : Nat, ∃ _ : Path D C,
      Φ D len ∧ blank C=P.zP ∧ C P.eP=D (P.L.hub P.L.K) ∧ C (P.L.hub P.L.K)=B (P.L.hub P.L.K) ∧
      (∀ y, P.foot y → y≠P.L.hub P.L.K → C y=D y) ∧
      (∀ y, ¬P.foot y → y≠P.eP → C y=B y) ∧
      path.length≤P.wrapCost+len := by
  classical
  -- first cycle: the input into `K`, `K`'s seed into `wc`, `wc`'s token out to `eP`
  obtain ⟨B1,p1,len1,blank1',s1K,s1e,s1u,fix1'⟩ := P.wX B atZ
  have fix1 (y : Cell n) (h1 : y≠P.eP) (h2 : y≠P.L.hub P.L.K) (h3 : y≠P.wc) : B1 y=B y :=
    fix1' y h2 h1 h3
  -- walk to the hub
  obtain ⟨B2,p2,len2,eff2⟩ := exists_walk P.zP P.connTail P.conn_chain B1 blank1'
  have blank2 : blank B2=P.L.hub P.L.w := (walk_blank _ _ eff2 blank1').trans P.conn_last
  have off2 (y : Cell n) (hy : y∉P.conn) : B2 y=B1 y := walk_fixed _ eff2 hy
  have K2 : B2 (P.L.hub P.L.K)=B P.eP := by
    rw [off2 _ (P.foot_not_conn (Or.inr rfl)),s1K]
  have foot2 (y : Cell n) (hy : P.foot y) (hK : y≠P.L.hub P.L.K) : B2 y=B y := by
    rw [off2 y (P.foot_not_conn hy)]
    exact fix1 y (P.foot_ne_eP hy) hK (by rintro rfl; exact P.not_foot_wc hy)
  obtain ⟨D,q,blankD,fixD,phi⟩ := inner B2 (p1.append p2) blank2 foot2 K2
  -- conjugate by the walk
  obtain ⟨E,r,lenr,blankE,effE⟩ := Path.exists_unstaged p2 q (blankD.trans blank2.symm)
  have blankE' : blank E=P.zP := blankE.trans blank1'
  set σ := P.conn.formPerm with hσ
  have preimage (y : Cell n) : B2.symm (B1 y)=σ⁻¹ y := by
    apply B2.symm_apply_eq.mpr
    rw [eff2]
    change B1 y=B1 (σ (σ⁻¹ y))
    simp
  have Eon (y : Cell n) (hy : y∈P.conn) : E y=B1 y := by
    rw [effE,preimage]
    have hm : σ⁻¹ y∈P.conn := by
      rw [←List.formPerm_mem_iff_mem (l:=P.conn)]
      change σ (σ⁻¹ y)∈P.conn
      simpa using hy
    rw [fixD _ (P.conn_not_foot hm),eff2]
    change B1 (σ (σ⁻¹ y))=B1 y
    simp
  have Eoff (y : Cell n) (hy : y∉P.conn) : E y=D y := by
    rw [effE,preimage]
    congr 1
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact (List.formPerm_apply_of_notMem hy).symm
  -- second cycle: the final carrier out to `eP`, the seed back into `K`, `wc`'s token back
  obtain ⟨C,p7,len7,blank7,s7e,s7K,s7u,fix7'⟩ := P.wX' E blankE'
  have fix7 (y : Cell n) (h1 : y≠P.eP) (h2 : y≠P.L.hub P.L.K) (h3 : y≠P.wc) : C y=E y :=
    fix7' y h1 h2 h3
  have eConn : P.eP∉P.conn := P.conn_eP
  have KConn := P.foot_not_conn (Or.inr rfl)
  have EK : E (P.L.hub P.L.K)=D (P.L.hub P.L.K) := Eoff _ KConn
  have Ee : E P.eP=B P.wc := by
    rw [Eoff _ eConn,fixD _ (fun hf => P.foot_ne_eP hf rfl),off2 _ eConn,s1e]
  have Eu : E P.wc=B (P.L.hub P.L.K) := by
    rw [Eoff _ P.wc_conn,fixD _ P.not_foot_wc,off2 _ P.wc_conn,s1u]
  let back : Path D C := ((p2.append q).reverse).append (r.append p7)
  refine ⟨C,(p1.append r).append p7,D,q.length,back,phi,blank7,?_,?_,?_,?_,?_⟩
  · rw [s7e,EK]
  · rw [s7K,Eu]
  · intro y hy hK
    rw [fix7 y (P.foot_ne_eP hy) hK (fun e => P.not_foot_wc (e ▸ hy)),
      Eoff y (P.foot_not_conn hy)]
  · intro y hy he
    by_cases hK : y=P.L.hub P.L.K
    · exact absurd (Or.inr hK) hy
    by_cases hu : y=P.wc
    · rw [hu,s7u,Ee]
    rw [fix7 y he hK hu]
    by_cases hc : y∈P.conn
    · rw [Eon y hc,fix1 y he hK hu]
    · rw [Eoff y hc,fixD y hy,off2 y hc,fix1 y he hK hu]
  · simp only [Path.length_append,lenr,len2,wrapCost]
    omega

end StarSpec
end SlidingPuzzle.NestedRouting.Interface
