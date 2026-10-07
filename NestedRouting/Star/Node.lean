import NestedRouting.Star.Direct
import NestedRouting.Interface.ExceptionLedger

/-! A star node's records and invariant, and the facts shared by all its
requests. -/
namespace SlidingPuzzle.NestedRouting.Interface
open Finset TileRoles
open SlidingPuzzle.NestedRouting.ReservePolicy

variable {n : Nat} [NeZero n] {J : Nat}

omit [NeZero n] in
/-- One exchange at `e`: the board is unchanged off `R` and `e`. -/
theorem image_exchange (R : Finset (Cell n)) {e : Cell n} (he : e∉R) {B C : Board n}
    (fix : ∀ x, x∉R → x≠e → C x=B x) (hne : C e≠B e) :
    R.image C=insert (B e) ((R.image B).erase (C e)) := by
  ext t
  simp only [mem_image,mem_insert,mem_erase]
  constructor
  · rintro ⟨x,hx,rfl⟩
    by_cases hte : C x=B e
    · exact Or.inl hte
    · refine Or.inr ⟨fun h => he ((C.injective h) ▸ hx),B.symm (C x),?_,B.apply_symm_apply _⟩
      by_contra hy
      have hye : B.symm (C x)≠e := by
        intro h
        apply hte
        have := congrArg B h
        rwa [B.apply_symm_apply] at this
      have h1 : C (B.symm (C x))=C x := by rw [fix _ hy hye,B.apply_symm_apply]
      exact hy ((C.injective h1).symm ▸ hx)
  · rintro (rfl | ⟨hne',x,hx,rfl⟩)
    · refine ⟨C.symm (B e),?_,C.apply_symm_apply _⟩
      by_contra hy
      have hye : C.symm (B e)≠e := by
        intro h; apply hne
        have := congrArg C h
        rw [C.apply_symm_apply] at this
        exact this.symm
      have h1 := fix _ hy hye
      rw [C.apply_symm_apply] at h1
      exact hye (B.injective h1.symm)
    · refine ⟨C.symm (B x),?_,C.apply_symm_apply _⟩
      by_contra hy
      have hye : C.symm (B x)≠e := by
        intro h; apply hne'
        have := congrArg C h
        rw [C.apply_symm_apply] at this
        exact this
      have h1 := fix _ hy hye
      rw [C.apply_symm_apply] at h1
      exact hy (by rw [←B.injective h1]; exact hx)

namespace StarSpec
variable (P : StarSpec n J)

/-- The records of a star node. -/
structure StarRec where
  roles : Roles n
  counts : Counts
  work : Nat
  led : Fin J → Ledger.Counter
  ch : (j : Fin J) → (P.Q j).Rec
  /-- Requests that used the wrapper. -/
  nreq : Nat
  /-- Direct exchanges. -/
  ndx : Nat
  /-- Late charges: helper exports and reserve arrivals exporting a core. -/
  late : Nat
  /-- Static cells still holding a reserve source. -/
  fresh : Finset (Cell n)
  /-- Reserve exports by a direct exchange not from a static cell. -/
  nf : Nat

def dxCost : Nat := P.dcost

/-- The static ledger: fresh cells hold reserve sources; exchanges not from a
fresh cell come only once none is left. -/
def StatInv (s : P.StarRec) (B : Board n) : Prop :=
  s.fresh⊆P.stat ∧ (∀ x∈s.fresh, B x∈s.roles .reserveSource) ∧
    s.nf+(P.stat.card-s.fresh.card)≤s.counts.er ∧ (s.fresh.Nonempty → s.nf=0)

structure Holds (β : Nat) (s : P.StarRec) (B : Board n) : Prop where
  sound : Sound P.frame B s.roles s.counts
  inner : P.Inner B s.roles s.led s.ch β s.counts.ec s.counts.ac false false
  lead : Lead β s.counts
  lateInv : LateInvariant P.frame.M P.frame.r β s.counts s.late
  ndx_le : s.ndx≤s.nf+s.late
  statInv : P.StatInv s B
  nreq_le : s.nreq≤s.counts.ec+s.counts.er+s.late
  work_le : s.work≤P.totalWork s.ch+P.ledCost s.led+P.wrapCost*s.nreq+P.dxCost*s.ndx+
    ∑ x∈P.stat \ s.fresh, P.dw x
  /-- No draining services before finishing. -/
  idle0 : ∀ j, (s.led j).idle=0

def insertRole (r : Roles n) (t : Tile n) (ρ : Role) : Roles n :=
  fun i => if i=ρ then insert t (r i) else r i

omit [NeZero n] in
theorem mem_insertRole {r : Roles n} {t x : Tile n} {ρ i : Role} :
    x∈insertRole r t ρ i ↔ (i=ρ ∧ x=t) ∨ x∈r i := by
  by_cases hi : i=ρ <;> simp [insertRole,hi]

omit [NeZero n] in
theorem insertRole_disjoint {r : Roles n} {t : Tile n} {ρ : Role}
    (disj : ∀ i i', i≠i' → Disjoint (r i) (r i')) (fresh : ∀ i, t∉r i) :
    ∀ i i', i≠i' → Disjoint (insertRole r t ρ i) (insertRole r t ρ i') := by
  intro i i' hii
  apply disjoint_left.mpr
  intro x h1 h2
  rw [mem_insertRole] at h1 h2
  rcases h1 with ⟨hi,rfl⟩ | h1 <;> rcases h2 with ⟨hi',hx⟩ | h2
  · exact hii (hi.trans hi'.symm)
  · exact fresh i' h2
  · exact fresh i (hx ▸ h1)
  · exact disjoint_left.mp (disj i i' hii) h1 h2

namespace Inner
variable {P} {B : Board n} {r : Roles n} {led : Fin J → Ledger.Counter}
  {ch : (j : Fin J) → (P.Q j).Rec} {cap ecNow acNow : Nat}

/-- At rest the carrier holds a token. -/
theorem carrier_token {cr : Bool} (h : P.Inner B r led ch cap ecNow acNow false cr) :
    B (P.L.hub P.L.K)∉r .coreSource := by
  intro hs
  rcases h.src_loc _ hs with ⟨j,hj⟩ | ⟨j,hj⟩ | ⟨hc,_⟩
  · obtain ⟨x,hx,eq⟩ := h.mem_childSrc_cell hj
    have := B.injective eq
    subst this
    exact (P.L.hub_child j).1 hx
  · obtain ⟨c,hc,eq⟩ := cell_of_ce hj
    have := B.injective eq
    subst this
    exact (P.L.hub_loop j).1 (P.L.mem_loop_of_exportQ hc)
  · exact absurd hc (by simp)

theorem carrier_token_fin {cs : Bool} (h : P.Inner B r led ch cap ecNow acNow cs false) :
    B (P.L.hub P.L.K)∉r .coreFinal := by
  intro hs
  rcases h.fin_loc _ hs with ⟨j,hj⟩ | ⟨j,hj⟩ | ⟨hc,_⟩
  · obtain ⟨x,hx,eq⟩ := h.mem_childFin_cell hj
    have := B.injective eq
    subst this
    exact (P.L.hub_child j).1 hx
  · obtain ⟨c,hc,eq⟩ := cell_of_cd hj
    have := B.injective eq
    subst this
    exact (P.L.hub_loop j).1 (P.L.mem_loop_of_deliveryQ hc)
  · exact absurd hc (by simp)

theorem lanes_agree {B' : Board n} (agree : ∀ y, P.foot y → y≠P.L.hub P.L.K → B' y=B y) :
    (∀ j, P.ce B' j=P.ce B j) ∧ (∀ j, P.cd B' j=P.cd B j) ∧ (∀ j, ∀ x∈(P.Q j).cells, B' x=B x) := by
  have notK {j : Fin J} {y : Cell n} (hy : y∈P.L.loop j) : y≠P.L.hub P.L.K :=
    fun e => (P.L.hub_loop j).1 (e ▸ hy)
  refine ⟨fun j => ?_,fun j => ?_,fun j x hx => agree x (Or.inl ⟨j,Or.inr (Or.inr hx)⟩)
    (fun e => (P.L.hub_child j).1 (e ▸ hx))⟩
  · exact List.map_congr_left (fun y hy => agree y (Or.inl ⟨j,Or.inl hy⟩) (notK (P.L.mem_loop_of_exportQ hy)))
  · exact List.map_congr_left (fun y hy => agree y (Or.inl ⟨j,Or.inr (Or.inl hy)⟩) (notK (P.L.mem_loop_of_deliveryQ hy)))

/-- The input enters the carrier and P's roles. -/
theorem start (h : P.Inner B r led ch cap ecNow acNow false false) {B2 : Board n} (path : Path B B2)
    (agree : ∀ y, P.foot y → y≠P.L.hub P.L.K → B2 y=B y) {t : Tile n}
    (hK2 : B2 (P.L.hub P.L.K)=t) (fresh : ∀ i, t∉r i) (ρ : Role) (hρ : ρ≠.coreSource) :
    P.Inner B2 (insertRole r t ρ) led ch cap ecNow acNow false (decide (ρ=.coreFinal)) := by
  classical
  obtain ⟨ce',cd',cells'⟩ := lanes_agree agree
  have srcEq : insertRole r t ρ .coreSource=r .coreSource := by simp [insertRole,Ne.symm hρ]
  have tok := h.carrier_token
  have tokF := h.carrier_token_fin
  apply h.recarrier (insertRole_disjoint h.disjoint fresh) ce' cd' cells'
    (fun j => (P.Q j).transport (h.child j) path (cells' j))
  · intro x _ _; rw [srcEq]
  · intro x _ hx2
    rw [mem_insertRole]
    constructor
    · rintro (⟨_,rfl⟩ | hx)
      · exact absurd hK2.symm hx2
      · exact hx
    · exact Or.inr
  · intro hs; rw [srcEq,hK2] at hs; exact absurd hs (fresh _)
  · intro hs
    rw [hK2,mem_insertRole] at hs
    rcases hs with ⟨hρ',_⟩ | hs
    · simp [← hρ']
    · exact absurd hs (fresh _)
  · intro hs; rw [srcEq] at hs; exact absurd hs tok
  · intro hs
    rw [mem_insertRole] at hs
    rcases hs with ⟨_,ht⟩ | hs
    · rw [ht,hK2]
    · exact absurd hs tokF

/-- The output leaves the carrier and P's roles; the seed returns. -/
theorem finishWrap {D : Board n} {r' : Roles n} (h : P.Inner D r' led ch cap ecNow acNow true false)
    {C : Board n} (path : Path D C) (agree : ∀ y, P.foot y → y≠P.L.hub P.L.K → C y=D y)
    (seedS : C (P.L.hub P.L.K)∉r' .coreSource) (seedF : C (P.L.hub P.L.K)∉r' .coreFinal)
    {r'' : Roles n} (h'' : ∀ i x, x∈r'' i ↔ x≠D (P.L.hub P.L.K) ∧ x∈r' i) :
    P.Inner C r'' led ch cap ecNow acNow false false := by
  obtain ⟨ce',cd',cells'⟩ := lanes_agree agree
  have disj'' : ∀ i i', i≠i' → Disjoint (r'' i) (r'' i') := by
    intro i i' hii
    apply disjoint_left.mpr
    intro x h1 h2
    exact disjoint_left.mp (h.disjoint i i' hii) ((h'' i x).mp h1).2 ((h'' i' x).mp h2).2
  apply h.recarrier disj'' ce' cd' cells' (fun j => (P.Q j).transport (h.child j) path (cells' j))
  · intro x hx1 _; rw [h'']; exact ⟨fun hh => hh.2,fun hh => ⟨hx1,hh⟩⟩
  · intro x hx1 _; rw [h'']; exact ⟨fun hh => hh.2,fun hh => ⟨hx1,hh⟩⟩
  · intro hs; exact absurd ((h'' _ _).mp hs).2 seedS
  · intro hs; exact absurd ((h'' _ _).mp hs).2 seedF
  · intro hs; exact absurd rfl ((h'' _ _).mp hs).1
  · intro hs; exact absurd rfl ((h'' _ _).mp hs).1

end Inner

/-- At rest the ledger's total credit is within the lead allowance. -/
theorem cap_ok {β : Nat} {s : P.StarRec} {B : Board n} (h : P.Holds β s B) :
    Ledger.totalCredit s.led≤β := by
  have hv := h.sound.valid
  have hl := h.lead
  simp only [Counts.Valid] at hv
  unfold Lead at hl
  have hS := h.inner.sumS
  have hG := h.inner.sumG
  unfold Ledger.totalCredit Ledger.Counter.credit
  rw [sum_sub_distrib,←Nat.cast_sum,←Nat.cast_sum,hS,hG]
  omega

end StarSpec

end SlidingPuzzle.NestedRouting.Interface
