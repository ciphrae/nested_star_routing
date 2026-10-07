import NestedRouting.Star.Inner

/-! One service preserves the inner invariant of a star node. -/
namespace SlidingPuzzle.NestedRouting.Interface
open Finset TileRoles
open SlidingPuzzle.NestedRouting.ReservePolicy

variable {n : Nat} [NeZero n] {J : Nat}

namespace StarSpec
variable (P : StarSpec n J)

def ehead (j : Fin J) : Cell n := (P.L.exportQ j).head (by simp [StarLayout.exportQ])

theorem map_head_tail {α β : Type*} (f : α → β) {l : List α} (h : l≠[]) :
    l.map f=f (l.head h) :: l.tail.map f := by
  obtain ⟨a,t,rfl⟩ := List.exists_cons_of_ne_nil h
  rfl

theorem ce_cons (B : Board n) (j : Fin J) :
    P.ce B j=B (P.ehead j) :: ((P.L.exportQ j).tail.map B) :=
  map_head_tail B _

theorem cd_cons (B : Board n) (j : Fin J) :
    P.cd B j=B (P.L.e j) :: ((P.L.deliveryLane j).map B) := by
  simp [cd,StarLayout.deliveryQ]

def serviceCost (j : Fin J) : Nat :=
  2*P.L.hcost j+2*(P.L.accessTail j).length+(P.L.exportQ j).length+(P.L.deliveryQ j).length+2

def totalWork (ch : (j : Fin J) → (P.Q j).Rec) : Nat := ∑ j, (P.Q j).work (ch j)

def hasSource (j : Fin J) (s : (P.Q j).Rec) : Prop :=
  ((P.Q j).counts s).ec<(P.Q j).M ∨ ((P.Q j).counts s).er<(P.Q j).r

open Classical in
/-- What the service does with the delivery head `t`: a P core final is
delivered as the child goal it is, anything else as a helper if the child
still has a source, and otherwise it turns around. -/
noncomputable def act (j : Fin J) (s : (P.Q j).Rec) (r : Roles n) (t : Tile n) : Option Arrival :=
  if t∈r .coreFinal then (if t∈(P.Q j).coreGoals then some .core else some .reserve)
  else if P.hasSource j s then some .helper else none

theorem select_eq_helper_iff (M r : Nat) (c : Counts) (a : Arrival) (guard : RequestGuard M r c a) :
    select M r c a=.helper ↔ ¬(c.ec<M ∨ c.er<r) := by
  cases a <;> simp only [select,RequestGuard] at guard ⊢ <;> split_ifs <;> simp_all

theorem advance_src (c : Counts) (a : Arrival) (o : Export) :
    (advance c a o).ec+(advance c a o).er=c.ec+c.er+(if o=.helper then 0 else 1) := by
  cases o <;> simp [advance] <;> omega

theorem advance_fin (c : Counts) (a : Arrival) (o : Export) :
    (advance c a o).ac+(advance c a o).ar=c.ac+c.ar+(if a=.helper then 0 else 1) := by
  cases a <;> simp [advance] <;> omega

theorem export_role_source {o : Export} (h : o≠.helper) :
    o.role=Role.coreSource ∨ o.role=Role.reserveSource := by
  cases o <;> simp_all [Export.role]

theorem e_ne_blank (j : Fin J) : P.L.e j≠P.L.hub P.L.w := by
  intro he
  have hl : P.L.e j∈P.L.loop j := P.L.mem_loop_of_deliveryQ (P.L.e_mem_deliveryQ j)
  have hx := P.L.access_loop j _ (by rw [he]; exact List.mem_cons_self) hl
  exact P.L.x_notMem_deliveryQ j (hx ▸ P.L.e_mem_deliveryQ j)

namespace Inner
variable {P} {B : Board n} {r : Roles n} {led : Fin J → Ledger.Counter}
  {ch : (j : Fin J) → (P.Q j).Rec} {cap ecNow acNow : Nat} {cs cr : Bool}

/-- The child request chosen by `act` is admissible, given lead slack. -/
theorem act_valid (h : P.Inner B r led ch cap ecNow acNow cs cr) (atW : blank B=P.L.hub P.L.w)
    (j : Fin J) (β' : Nat)
    (slack : ((P.Q j).counts (ch j)).ec+((P.Q j).counts (ch j)).er+1≤
      ((P.Q j).counts (ch j)).ac+((P.Q j).counts (ch j)).ar+β') :
    ∀ a, P.act j (ch j) r (B (P.L.e j))=some a → (P.Q j).Label a (B (P.L.e j)) ∧
      RequestGuard (P.Q j).M (P.Q j).r ((P.Q j).counts (ch j)) a ∧
      Lead β' (advance ((P.Q j).counts (ch j)) a (select (P.Q j).M (P.Q j).r ((P.Q j).counts (ch j)) a)) := by
  intro a ha
  have hs := (P.Q j).sound (h.child j)
  have he : P.L.e j∉(P.Q j).cells := (P.Q j).entry_input (P.L.entry j)
  have lead : Lead β' (advance ((P.Q j).counts (ch j)) a
      (select (P.Q j).M (P.Q j).r ((P.Q j).counts (ch j)) a)) := by
    unfold Lead
    have h1 := advance_src ((P.Q j).counts (ch j)) a (select (P.Q j).M (P.Q j).r ((P.Q j).counts (ch j)) a)
    have h2 := advance_fin ((P.Q j).counts (ch j)) a (select (P.Q j).M (P.Q j).r ((P.Q j).counts (ch j)) a)
    split_ifs at h1 h2 <;> omega
  unfold act at ha
  split_ifs at ha with hf hc hsrc
  · cases ha
    exact ⟨hc,hs.guard_core he hc,lead⟩
  · cases ha
    have hr : B (P.L.e j)∈(P.Q j).reserveGoals := by
      have := h.del_home j _ (by rw [cd_cons]; exact List.mem_cons_self) hf
      simp only [homeGoals,mem_union] at this
      tauto
    exact ⟨hr,hs.guard_reserve he hr,lead⟩
  · cases ha
    refine ⟨?_,hsrc,lead⟩
    exact StarLayout.ne_zero_of_ne_blank (by rw [atW]; exact e_ne_blank P j)

end Inner

namespace Inner
variable {P} {B : Board n} {r : Roles n} {led : Fin J → Ledger.Counter}
  {ch : (j : Fin J) → (P.Q j).Rec} {cap ecNow acNow : Nat} {cs cr : Bool}

/-- What the child request (or the turnaround) did, read in P's roles. -/
theorem outcome_facts (h : P.Inner B r led ch cap ecNow acNow cs cr) (j : Fin J) (β' : Nat)
    {next : (P.Q j).Rec} {out : Tile n}
    (valid : ∀ a, P.act j (ch j) r (B (P.L.e j))=some a → (P.Q j).Label a (B (P.L.e j)) ∧
      RequestGuard (P.Q j).M (P.Q j).r ((P.Q j).counts (ch j)) a ∧
      Lead β' (advance ((P.Q j).counts (ch j)) a (select (P.Q j).M (P.Q j).r ((P.Q j).counts (ch j)) a)))
    (nextValid : ((P.Q j).counts next).Valid (P.Q j).M (P.Q j).r)
    (outcome : (P.act j (ch j) r (B (P.L.e j))=none ∧ next=ch j ∧ out=B (P.L.e j)) ∨
      (∃ a, P.act j (ch j) r (B (P.L.e j))=some a ∧
        out∈(P.Q j).roles (ch j) (select (P.Q j).M (P.Q j).r ((P.Q j).counts (ch j)) a).role ∧
        (P.Q j).roles next=updateRoles ((P.Q j).roles (ch j)) out (B (P.L.e j)) a.role ∧
        (P.Q j).counts next=advance ((P.Q j).counts (ch j)) a
          (select (P.Q j).M (P.Q j).r ((P.Q j).counts (ch j)) a))) :
    out∉r .coreFinal ∧
    ((P.Q j).counts next).ec+((P.Q j).counts next).er=
      ((P.Q j).counts (ch j)).ec+((P.Q j).counts (ch j)).er+(if out∈r .coreSource then 1 else 0) ∧
    ((P.Q j).counts next).ac+((P.Q j).counts next).ar=
      ((P.Q j).counts (ch j)).ac+((P.Q j).counts (ch j)).ar+(if B (P.L.e j)∈r .coreFinal then 1 else 0) ∧
    (∀ t∈P.childSrc j next, t∈P.childSrc j (ch j)) ∧
    (∀ t∈P.childSrc j (ch j), t∈P.childSrc j next ∨ t=out) ∧
    (∀ t, t∈P.childFin j next ↔ t∈P.childFin j (ch j) ∨ (t=B (P.L.e j) ∧ B (P.L.e j)∈r .coreFinal)) ∧
    (P.sourceless j (ch j) → out∉r .coreSource) ∧
    (out∉r .coreSource → P.sourceless j next) := by
  classical
  have hs := (P.Q j).sound (h.child j)
  have eD : B (P.L.e j)∈P.cd B j := by rw [cd_cons]; exact List.mem_cons_self
  have eNotSrc := h.del_src j _ eD
  have srcless_of (c : Counts) (hv : c.Valid (P.Q j).M (P.Q j).r)
      (hn : ¬(c.ec<(P.Q j).M ∨ c.er<(P.Q j).r)) : c.ec=(P.Q j).M ∧ c.er=(P.Q j).r := by
    simp only [Counts.Valid] at hv; omega
  rcases outcome with ⟨hnone,rfl,rfl⟩ | ⟨a,hsome,hout,hroles,hcounts⟩
  · -- turnaround
    have hf : B (P.L.e j)∉r .coreFinal := by
      intro hf; unfold act at hnone; simp only [hf,if_true] at hnone; split_ifs at hnone
    have hsrc : ¬P.hasSource j (ch j) := by
      intro hsrc; unfold act at hnone; simp [hf,hsrc] at hnone
    refine ⟨hf,by simp [eNotSrc],by simp [hf],fun t ht => ht,fun t ht => Or.inl ht,
      fun t => by simp [hf],fun _ => eNotSrc,fun _ => srcless_of _ hs.valid hsrc⟩
  · obtain ⟨_,guard,_⟩ := valid a hsome
    set c := (P.Q j).counts (ch j) with hc
    set o := select (P.Q j).M (P.Q j).r c a with ho
    have hhelp := select_eq_helper_iff (P.Q j).M (P.Q j).r c a guard
    -- the output sits in the child, so P classifies it as the child does
    have outCell : ∃ x∈(P.Q j).cells, B x=out := by
      have : out∈contents ((P.Q j).roles (ch j)) := mem_biUnion.mpr ⟨_,mem_univ _,hout⟩
      rw [←hs.inventory.exact] at this
      simpa using this
    obtain ⟨x,hx,hxo⟩ := outCell
    have outFin : out∉r .coreFinal := by
      rw [←hxo,h.fin_iff_child j hx,hxo]
      intro hf
      simp only [childFin,mem_union] at hf
      have hne1 : o.role≠Role.coreFinal := by cases o <;> simp [Export.role]
      have hne2 : o.role≠Role.reserveFinal := by cases o <;> simp [Export.role]
      rcases hf with hf | hf
      · exact disjoint_left.mp (hs.inventory.disjoint _ _ hne1) hout hf
      · exact disjoint_left.mp (hs.inventory.disjoint _ _ hne2) hout hf
    have outSrc : out∈r .coreSource ↔ o≠.helper := by
      rw [←hxo,h.src_iff_child j hx,hxo]
      constructor
      · intro hsrc hoh
        rw [hoh] at hout
        simp only [childSrc,mem_union] at hsrc
        rcases hsrc with hsrc | hsrc
        · exact disjoint_left.mp (hs.inventory.disjoint Role.helper Role.coreSource (by decide)) hout hsrc
        · exact disjoint_left.mp (hs.inventory.disjoint Role.helper Role.reserveSource (by decide)) hout hsrc
      · intro hoh
        rcases export_role_source hoh with hr | hr <;> rw [hr] at hout <;> simp [childSrc,hout]
    have arole : a≠.helper ↔ B (P.L.e j)∈r .coreFinal := by
      unfold act at hsome
      split_ifs at hsome with hf <;> cases hsome <;> simp [hf]
    have notSrcRole : a.role≠Role.coreSource ∧ a.role≠Role.reserveSource := by
      cases a <;> simp [Arrival.role]
    have outNotFinRole : out∉(P.Q j).roles (ch j) .coreFinal ∧ out∉(P.Q j).roles (ch j) .reserveFinal := by
      have hne1 : o.role≠Role.coreFinal := by cases o <;> simp [Export.role]
      have hne2 : o.role≠Role.reserveFinal := by cases o <;> simp [Export.role]
      exact ⟨fun hf => disjoint_left.mp (hs.inventory.disjoint _ _ hne1) hout hf,
        fun hf => disjoint_left.mp (hs.inventory.disjoint _ _ hne2) hout hf⟩
    refine ⟨outFin,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [hcounts,advance_src]
      by_cases hoh : o=.helper
      · have : out∉r .coreSource := fun hh => (outSrc.mp hh) hoh
        simp [hoh,this]
      · simp [hoh,outSrc.mpr hoh]
    · rw [hcounts,advance_fin]
      by_cases hah : a=.helper
      · have : B (P.L.e j)∉r .coreFinal := fun hh => (arole.mpr hh) hah
        simp [hah,this]
      · simp [hah,arole.mp hah]
    · intro t ht
      simp only [childSrc,hroles,mem_union,mem_updateRoles] at ht ⊢
      rcases ht with ((⟨hr,_⟩) | ⟨_,ht⟩) | ((⟨hr,_⟩) | ⟨_,ht⟩)
      · exact absurd hr.symm notSrcRole.1
      · exact Or.inl ht
      · exact absurd hr.symm notSrcRole.2
      · exact Or.inr ht
    · intro t ht
      by_cases hto : t=out
      · exact Or.inr hto
      · left
        simp only [childSrc,hroles,mem_union,mem_updateRoles] at ht ⊢
        rcases ht with ht | ht
        · exact Or.inl (Or.inr ⟨hto,ht⟩)
        · exact Or.inr (Or.inr ⟨hto,ht⟩)
    · intro t
      simp only [childFin,hroles,mem_union,mem_updateRoles]
      constructor
      · rintro ((⟨hr,rfl⟩ | ⟨_,ht⟩) | (⟨hr,rfl⟩ | ⟨_,ht⟩))
        · exact Or.inr ⟨rfl,arole.mp (by rintro rfl; simp [Arrival.role] at hr)⟩
        · exact Or.inl (Or.inl ht)
        · exact Or.inr ⟨rfl,arole.mp (by rintro rfl; simp [Arrival.role] at hr)⟩
        · exact Or.inl (Or.inr ht)
      · rintro ((ht | ht) | ⟨rfl,hf⟩)
        · exact Or.inl (Or.inr ⟨fun e => outNotFinRole.1 (e ▸ ht),ht⟩)
        · exact Or.inr (Or.inr ⟨fun e => outNotFinRole.2 (e ▸ ht),ht⟩)
        · have hah := arole.mpr hf
          cases a with
          | helper => exact absurd rfl hah
          | core => exact Or.inl (Or.inl ⟨rfl,rfl⟩)
          | reserve => exact Or.inr (Or.inl ⟨rfl,rfl⟩)
    · intro hsl hsrc
      have hns : ¬(c.ec<(P.Q j).M ∨ c.er<(P.Q j).r) := by
        obtain ⟨h1,h2⟩ := hsl; simp only [hc]; omega
      exact (outSrc.mp hsrc) (hhelp.mpr hns)
    · intro hns
      have hoh : o=.helper := by by_contra hh; exact hns (outSrc.mpr hh)
      have hnc := hhelp.mp hoh
      have hv := hs.valid
      have hcn := hcounts
      have h1 : ((P.Q j).counts next).ec=c.ec ∧ ((P.Q j).counts next).er=c.er := by
        rw [hcn]; simp [advance,hoh]
      unfold sourceless
      rw [h1.1,h1.2]
      simp only [Counts.Valid] at hv
      omega

end Inner

namespace Inner
variable {P} {B : Board n} {r : Roles n} {led : Fin J → Ledger.Counter}
  {ch : (j : Fin J) → (P.Q j).Rec} {cap ecNow acNow : Nat} {cs cr : Bool}

/-- Cells of other spokes and other children are untouched by a service on `j`. -/
theorem other_fixed {C : Board n} (j : Fin J)
    (fixC : ∀ y, y∉P.L.exportQ j → y∉P.L.deliveryQ j → y∉(P.Q j).cells → y≠P.L.hub P.L.K → C y=B y)
    {i : Fin J} (hij : i≠j) :
    P.ce C i=P.ce B i ∧ P.cd C i=P.cd B i ∧ ∀ x∈(P.Q i).cells, C x=B x := by
  have loopFix (y : Cell n) (hy : y∈P.L.loop i) : C y=B y := by
    apply fixC y
    · exact fun he => P.L.loops_disjoint i j hij y hy (P.L.mem_loop_of_exportQ he)
    · exact fun hd => P.L.loops_disjoint i j hij y hy (P.L.mem_loop_of_deliveryQ hd)
    · exact P.L.loop_child i j y hy
    · rintro rfl; exact (P.L.hub_loop i).1 hy
  refine ⟨?_,?_,?_⟩
  · exact List.map_congr_left (fun y hy => loopFix y (P.L.mem_loop_of_exportQ hy))
  · exact List.map_congr_left (fun y hy => loopFix y (P.L.mem_loop_of_deliveryQ hy))
  · intro x hx
    apply fixC x
    · exact fun he => P.L.loop_child j i x (P.L.mem_loop_of_exportQ he) hx
    · exact fun hd => P.L.loop_child j i x (P.L.mem_loop_of_deliveryQ hd) hx
    · exact fun hj => disjoint_left.mp (P.L.children_disjoint i j hij) hx hj
    · rintro rfl; exact (P.L.hub_child i).1 hx

end Inner

namespace Inner
variable {P} {B : Board n} {r : Roles n} {led : Fin J → Ledger.Counter}
  {ch : (j : Fin J) → (P.Q j).Rec} {cap ecNow acNow : Nat} {cr : Bool}

omit [NeZero n] in
theorem countP_cons {l : List (Tile n)} (a : Tile n) (p : Tile n → Prop) [DecidablePred p] :
    (a :: l).countP p=l.countP p+(if p a then 1 else 0) := by
  rw [List.countP_cons]; simp

omit [NeZero n] in
theorem countP_concat {l : List (Tile n)} (a : Tile n) (p : Tile n → Prop) [DecidablePred p] :
    (l++[a]).countP p=l.countP p+(if p a then 1 else 0) := by
  rw [List.countP_append]; simp

theorem sum_update_add {J : Nat} (w : Fin J → Nat) (j : Fin J) (v : Nat) :
    ∑ i, Function.update w j v i+w j=∑ i, w i+v := by
  rw [sum_update_of_mem (mem_univ j),←sum_erase_add _ _ (mem_univ j),sdiff_singleton_eq_erase]
  omega

theorem sum_update_map {J : Nat} (f : Fin J → Ledger.Counter) (g : Ledger.Counter → Nat)
    (j : Fin J) (c : Ledger.Counter) :
    ∑ i, g (Function.update f j c i)+g (f j)=∑ i, g (f i)+g c := by
  have h := sum_update_add (fun i => g (f i)) j (g c)
  have e : ∀ i, g (Function.update f j c i)=Function.update (fun i => g (f i)) j (g c) i := by
    intro i; by_cases hij : i=j
    · subst hij; simp
    · simp [Function.update_of_ne hij]
  simp only [e]
  exact h

theorem slack_arith {ec er ac ar S G le ad E D : Nat} {peak : Int}
    (bS : ec+er=S+le) (bG : ac+ar+ad=G) (l1 : le≤E) (l2 : ad≤D)
    (hp : (S : Int)-G-1≤peak) (hp0 : 0≤peak) : ec+er+1≤ac+ar+(peak.toNat+E+D+2) := by
  have := Int.toNat_of_nonneg hp0
  omega

/-- One service on spoke `j` preserves the inner invariant. A real input
must be a goal of `j` in the carrier; a helper input must go to an active
spoke of least credit. The export head becomes the carrier. -/
theorem service (h : P.Inner B r led ch cap ecNow acNow false cr)
    (atW : blank B=P.L.hub P.L.w) (j : Fin J) (real : Bool) (hcr : cr=real)
    (carrierReal : real=true → B (P.L.hub P.L.K)∈r .coreFinal ∧ B (P.L.hub P.L.K)∈P.homeGoals j)
    (carrierTok : real=false → B (P.L.hub P.L.K)∉r .coreSource ∧ B (P.L.hub P.L.K)∉r .coreFinal)
    (spoke : real=false → (led j).S<P.pop j →
      ∀ i∈Ledger.active P.pop led, (led j).credit≤(led i).credit)
    (capOk : Ledger.totalCredit led≤cap) :
    ∃ C : Board n, ∃ path : Path B C, ∃ ch' : (j : Fin J) → (P.Q j).Rec,
      blank C=P.L.hub P.L.w ∧
      P.Inner C r (Function.update led j (Ledger.serve (led j) (P.pop j) real
          (decide (B (P.ehead j)∈r .coreSource)))) ch' cap
        (ecNow+(if B (P.ehead j)∈r .coreSource then 1 else 0)) (acNow+(if real then 1 else 0))
        (decide (B (P.ehead j)∈r .coreSource)) false ∧
      C (P.L.hub P.L.K)=B (P.ehead j) ∧ P.cd C j=(P.cd B j).tail++[B (P.L.hub P.L.K)] ∧
      (∀ y, y∉P.L.exportQ j → y∉P.L.deliveryQ j → y∉(P.Q j).cells → y≠P.L.hub P.L.K → C y=B y) ∧
      path.length+P.totalWork ch≤P.serviceCost j+P.totalWork ch' := by
  classical
  subst cr
  set head := B (P.ehead j) with hhead
  set src : Bool := decide (head∈r .coreSource) with hsrcdef
  set c' := Ledger.serve (led j) (P.pop j) real src with hc'
  set led' := Function.update led j c' with hled'
  have led'j : led' j=c' := by simp [led']
  have led'ne {i : Fin J} (hij : i≠j) : led' i=led i := by simp [led',Function.update_of_ne hij]
  have cpk : c'.peak=max (led j).peak c'.credit := Ledger.serve_peak _ _ _ _
  have ccr : c'.credit=(led j).credit+(if src then 1 else 0)-(if real then 1 else 0) :=
    Ledger.serve_credit _ _ _ _
  have pk0 := h.ledger.peak_nonneg j
  have pkc := h.ledger.credit_le j
  -- allowance for child j after this service
  set β' := P.childBeta led' j with hβ'
  have relaxβ : P.childBeta led j≤β' := by
    simp only [hβ',childBeta,led'j,cpk]
    have : (led j).peak.toNat≤(max (led j).peak c'.credit).toNat :=
      Int.toNat_le_toNat (le_max_left _ _)
    omega
  have hsj : (P.Q j).Holds β' (ch j) B := (P.Q j).relax (h.child j) relaxβ
  have slack : ((P.Q j).counts (ch j)).ec+((P.Q j).counts (ch j)).er+1≤
      ((P.Q j).counts (ch j)).ac+((P.Q j).counts (ch j)).ar+β' := by
    have l1 := List.countP_le_length (p:=fun t => decide (t∈r .coreSource)) (l:=P.ce B j)
    have l2 := List.countP_le_length (p:=fun t => decide (t∈r .coreFinal)) (l:=P.cd B j)
    simp only [ce,cd,List.length_map] at l1 l2
    have hpk' : c'.credit≤c'.peak := by rw [cpk]; exact le_max_right _ _
    have hpk0' : 0≤c'.peak := by rw [cpk]; exact le_max_of_le_left pk0
    have low : ((led j).S : Int)-(led j).G-1≤c'.credit := by
      rw [ccr]; simp only [Ledger.Counter.credit]; split_ifs <;> omega
    simp only [hβ',childBeta,led'j]
    exact slack_arith (h.bridgeS j) (h.bridgeG j) l1 l2 (low.trans hpk') hpk0'
  have valid := h.act_valid atW j β' slack
  obtain ⟨C,path,next,out,blankC,holdsC,expEq,delEq,fixC,costC,outcome⟩ :=
    P.L.exists_service j atW hsj (P.act j (ch j) r (B (P.L.e j))) valid
  have nextValid := ((P.Q j).sound holdsC).valid
  obtain ⟨outFin,srcEq,finEq,srcSub,srcLoss,finIff,slOut,slNext⟩ :=
    h.outcome_facts j β' valid nextValid outcome
  set ch' := Function.update ch j next with hch'
  have ch'j : ch' j=next := by simp [ch']
  have ch'ne {i : Fin J} (hij : i≠j) : ch' i=ch i := by simp [ch',Function.update_of_ne hij]
  -- the two lanes of `j`
  set tl := (P.L.exportQ j).tail.map B with htl
  have ceB : P.ce B j=head :: tl := P.ce_cons B j
  have expEq' : C (P.L.hub P.L.K) :: P.ce C j=(head :: tl)++[out] := by
    rw [←ceB]; exact expEq
  have CK : C (P.L.hub P.L.K)=head := (List.cons_eq_cons.mp expEq').1
  have ceC : P.ce C j=tl++[out] := (List.cons_eq_cons.mp expEq').2
  set dl := (P.L.deliveryLane j).map B with hdl
  have cdB : P.cd B j=B (P.L.e j) :: dl := P.cd_cons B j
  have delEq' : B (P.L.e j) :: P.cd C j=(B (P.L.e j) :: dl)++[B (P.L.hub P.L.K)] := by
    rw [←cdB]; exact delEq
  have cdC : P.cd C j=dl++[B (P.L.hub P.L.K)] := (List.cons_eq_cons.mp delEq').2
  have others := fun {i : Fin J} (hij : i≠j) => other_fixed (P:=P) (B:=B) j fixC hij
  have hsrcIff : src=true ↔ head∈r .coreSource := by simp [src]
  have carrierIff : B (P.L.hub P.L.K)∈r .coreFinal ↔ real=true := by
    cases real
    · simp [(carrierTok rfl).2]
    · simp [(carrierReal rfl).1]
  have carrierNotSrc : B (P.L.hub P.L.K)∉r .coreSource := by
    cases real
    · exact (carrierTok rfl).1
    · exact fun hs => disjoint_left.mp (h.disjoint _ _ (by decide)) hs (carrierReal rfl).1
  have hS' : c'.S=(led j).S+(if src then 1 else 0) := Ledger.serve_S _ _ _ _
  have hG' : c'.G=(led j).G+(if real then 1 else 0) := Ledger.serve_G _ _ _ _
  have hk' : c'.k=(led j).k+1 := Ledger.serve_k _ _ _ _
  have hvj := ((P.Q j).sound (h.child j)).valid
  refine ⟨C,path,ch',blankC,⟨h.disjoint,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,CK,
    by rw [cdC,cdB]; rfl,fixC,?_⟩
  · -- children
    intro i
    by_cases hij : i=j
    · subst hij; rw [ch'j]; exact holdsC
    · rw [ch'ne hij]
      have hb : P.childBeta led' i=P.childBeta led i := by simp [childBeta,led'ne hij]
      rw [hb]
      exact (P.Q i).transport (h.child i) path (fun x hx => (others hij).2.2 x hx)
  · -- ledger
    have al : Ledger.Allowed P.pop P.elen led j real src := by
      refine ⟨?_,?_,?_,?_⟩
      · intro hs
        have hm := hsrcIff.mp hs
        have bS := h.bridgeS j
        rw [ceB,countP_cons,if_pos hm] at bS
        simp only [Counts.Valid] at hvj
        unfold pop
        omega
      · intro hr
        exact h.real_room j (carrierReal hr).1 (carrierReal hr).2
      · exact fun hr hact => spoke hr hact
      · intro hs hact
        by_contra hk
        have hk' : P.elen j≤(led j).k := by omega
        have hlen : 0<(P.ce B j).length := by rw [ceB]; simp
        have h0 : (P.ce B j)[0]=head := by simp [ceB]
        have hnot : (P.ce B j)[0]∉r .coreSource := by
          rw [h0]; intro hm; simp [hsrcIff.mpr hm] at hs
        obtain ⟨sl,rest⟩ := h.entered j 0 hlen (by simp [ce,elen] at hk' ⊢; omega) hnot
        have zero : (P.ce B j).countP (fun t => t∈r .coreSource)=0 := by
          rw [List.countP_eq_zero]
          intro t ht
          obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp ht
          rcases Nat.eq_zero_or_pos i with rfl | hpos
          · simpa using hnot
          · simpa using rest i hi hpos
        have bS := h.bridgeS j
        rw [zero] at bS
        obtain ⟨s1,s2⟩ := sl
        unfold pop at hact
        omega
    exact h.ledger.step capOk al
  · -- bridgeS
    intro i
    by_cases hij : i=j
    · subst hij
      rw [ch'j,led'j,srcEq,ceC,countP_concat,hS']
      have bS := h.bridgeS i
      rw [ceB,countP_cons] at bS
      have : (if src=true then 1 else 0)=(if head∈r .coreSource then 1 else 0) := by
        by_cases hm : head∈r .coreSource <;> simp [hm,hsrcIff]
      rw [this]
      omega
    · rw [ch'ne hij,led'ne hij,(others hij).1]; exact h.bridgeS i
  · -- bridgeG
    intro i
    by_cases hij : i=j
    · subst hij
      rw [ch'j,led'j,finEq,cdC,countP_concat,hG']
      have bG := h.bridgeG i
      rw [cdB,countP_cons] at bG
      have : (if B (P.L.hub P.L.K)∈r .coreFinal then 1 else 0)=(if real=true then 1 else 0) := by
        by_cases hm : real=true <;> simp [hm,carrierIff]
      rw [this]
      omega
    · rw [ch'ne hij,led'ne hij,(others hij).2.1]; exact h.bridgeG i
  · -- src_child
    intro i
    by_cases hij : i=j
    · subst hij; rw [ch'j]; exact fun t ht => h.src_child i (srcSub t ht)
    · rw [ch'ne hij]; exact h.src_child i
  · -- fin_child
    intro i
    by_cases hij : i=j
    · subst hij; rw [ch'j]
      intro t ht
      rcases (finIff t).mp ht with ht | ⟨rfl,hf⟩
      · exact h.fin_child i ht
      · exact hf
    · rw [ch'ne hij]; exact h.fin_child i
  · -- src_loc
    intro t ht
    rcases h.src_loc t ht with ⟨i,hi⟩ | ⟨i,hi⟩ | ⟨hcs,_⟩
    · by_cases hij : i=j
      · subst hij
        rcases srcLoss t hi with h' | rfl
        · exact Or.inl ⟨i,by rw [ch'j]; exact h'⟩
        · exact Or.inr (Or.inl ⟨i,by rw [ceC]; simp⟩)
      · exact Or.inl ⟨i,by rw [ch'ne hij]; exact hi⟩
    · by_cases hij : i=j
      · subst hij
        rw [ceB] at hi
        rcases List.mem_cons.mp hi with rfl | hi
        · exact Or.inr (Or.inr ⟨hsrcIff.mpr ht,CK.symm⟩)
        · exact Or.inr (Or.inl ⟨i,by rw [ceC]; exact List.mem_append_left _ hi⟩)
      · exact Or.inr (Or.inl ⟨i,by rw [(others hij).1]; exact hi⟩)
    · exact absurd hcs (by simp)
  · -- fin_loc
    intro t ht
    rcases h.fin_loc t ht with ⟨i,hi⟩ | ⟨i,hi⟩ | ⟨hcr,hK⟩
    · by_cases hij : i=j
      · subst hij; exact Or.inl ⟨i,by rw [ch'j]; exact (finIff t).mpr (Or.inl hi)⟩
      · exact Or.inl ⟨i,by rw [ch'ne hij]; exact hi⟩
    · by_cases hij : i=j
      · subst hij
        rw [cdB] at hi
        rcases List.mem_cons.mp hi with rfl | hi
        · exact Or.inl ⟨i,by rw [ch'j]; exact (finIff _).mpr (Or.inr ⟨rfl,ht⟩)⟩
        · exact Or.inr (Or.inl ⟨i,by rw [cdC]; exact List.mem_append_left _ hi⟩)
      · exact Or.inr (Or.inl ⟨i,by rw [(others hij).2.1]; exact hi⟩)
    · exact Or.inr (Or.inl ⟨j,by rw [cdC,hK]; simp⟩)
  · -- del_home
    intro i t hti htf
    by_cases hij : i=j
    · subst hij
      rw [cdC] at hti
      rcases List.mem_append.mp hti with hti | hti
      · exact h.del_home i t (by rw [cdB]; exact List.mem_cons_of_mem _ hti) htf
      · have htK : t=B (P.L.hub P.L.K) := List.mem_singleton.mp hti
        rw [htK] at htf ⊢
        exact (carrierReal (carrierIff.mp htf)).2
    · rw [(others hij).2.1] at hti; exact h.del_home i t hti htf
  · -- del_src
    intro i t hti
    by_cases hij : i=j
    · subst hij
      rw [cdC] at hti
      rcases List.mem_append.mp hti with hti | hti
      · exact h.del_src i t (by rw [cdB]; exact List.mem_cons_of_mem _ hti)
      · rw [List.mem_singleton.mp hti]; exact carrierNotSrc
    · rw [(others hij).2.1] at hti; exact h.del_src i t hti
  · -- exp_fin
    intro i t hti
    by_cases hij : i=j
    · subst hij
      rw [ceC] at hti
      rcases List.mem_append.mp hti with hti | hti
      · exact h.exp_fin i t (by rw [ceB]; exact List.mem_cons_of_mem _ hti)
      · rw [List.mem_singleton.mp hti]; exact outFin
    · rw [(others hij).1] at hti; exact h.exp_fin i t hti
  · -- entered
    intro i idx hidx hlen hns
    by_cases hij : i=j
    · subst hij
      rw [led'j,hk'] at hlen
      have lenB : (P.ce B i).length=tl.length+1 := by rw [ceB]; simp
      have lenC : (P.ce C i).length=tl.length+1 := by rw [ceC]; simp
      have getC : ∀ k (hk : k<(P.ce C i).length), (P.ce C i)[k]=(tl++[out])[k]'(by rw [←ceC]; exact hk) :=
        fun k hk => List.getElem_of_eq ceC hk
      have getB : ∀ k (hk : k<tl.length), (P.ce B i)[k+1]'(by rw [lenB]; omega)=tl[k] := by
        intro k hk
        rw [List.getElem_of_eq ceB]
        simp
      rw [ch'j]
      by_cases hlast : idx<tl.length
      · have eqC : (P.ce C i)[idx]=tl[idx] := by rw [getC]; exact List.getElem_append_left hlast
        obtain ⟨sl,rest⟩ := h.entered i (idx+1) (by rw [lenB]; omega)
          (by rw [lenB]; rw [lenC] at hlen; omega) (by rw [getB idx hlast,←eqC]; exact hns)
        refine ⟨slNext (slOut sl),?_⟩
        intro i' hi' hlt
        by_cases hl2 : i'<tl.length
        · have e1 : (P.ce C i)[i']=tl[i'] := by rw [getC]; exact List.getElem_append_left hl2
          rw [e1,←getB i' hl2]
          exact rest (i'+1) (by rw [lenB]; omega) (by omega)
        · have hi'eq : i'=tl.length := by rw [lenC] at hi'; omega
          have e1 : (P.ce C i)[i']=out := by rw [getC]; simp [hi'eq]
          rw [e1]; exact slOut sl
      · have hidx' : idx=tl.length := by rw [lenC] at hidx; omega
        have e1 : (P.ce C i)[idx]=out := by rw [getC]; simp [hidx']
        refine ⟨slNext (e1 ▸ hns),?_⟩
        intro i' hi' hlt
        rw [lenC] at hi'; omega
    · have e := (others hij).1
      rw [led'ne hij] at hlen
      rw [ch'ne hij]
      have hidxB : idx<(P.ce B i).length := e ▸ hidx
      have key : ∀ k (hk : k<(P.ce C i).length), (P.ce C i)[k]=(P.ce B i)[k]'(e ▸ hk) :=
        fun k hk => List.getElem_of_eq e hk
      obtain ⟨sl,rest⟩ := h.entered i idx hidxB (by rw [←e]; exact hlen) (by rw [←key]; exact hns)
      exact ⟨sl,fun i' hi' hlt => by rw [key]; exact rest i' _ hlt⟩
  · -- sumS
    have hs : ∑ i, (led' i).S+(led j).S=∑ i, (led i).S+c'.S := sum_update_map led Ledger.Counter.S j c'
    have h0 := h.sumS
    rw [hS'] at hs
    have : (if src=true then 1 else 0)=(if head∈r .coreSource then 1 else 0) := by
      by_cases hm : head∈r .coreSource <;> simp [hm,hsrcIff]
    rw [this] at hs
    show ∑ i, (led' i).S=_
    omega
  · -- sumG
    have hs : ∑ i, (led' i).G+(led j).G=∑ i, (led i).G+c'.G := sum_update_map led Ledger.Counter.G j c'
    have h0 := h.sumG
    rw [hG'] at hs
    show ∑ i, (led' i).G=_
    omega
  · -- cost
    have hsum := sum_update_add (fun i => (P.Q i).work (ch i)) j ((P.Q j).work next)
    have eq : P.totalWork ch'=∑ i, Function.update (fun i => (P.Q i).work (ch i)) j ((P.Q j).work next) i := by
      unfold totalWork
      apply sum_congr rfl
      intro i _
      by_cases hij : i=j
      · subst hij; simp [ch']
      · simp [ch',Function.update_of_ne hij]
    have tw : P.totalWork ch=∑ i, (P.Q i).work (ch i) := rfl
    rw [eq,tw]
    unfold serviceCost
    omega

end Inner

end StarSpec
end SlidingPuzzle.NestedRouting.Interface
