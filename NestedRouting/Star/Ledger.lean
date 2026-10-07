import MathlibRoots

/-! The scheduling ledger of a star router, as pure arithmetic.

Each spoke counts its source returns `S`, real (goal) inputs `G`, services
`k`, services after retirement `late`, and the largest credit `peak` it has
had, where credit is `S - G`. A spoke is active while `S < pop`. Helper
inputs go to an active spoke of least credit. Under a cap `B` on the total
credit before every service:

* the peaks sum to at most `J + Σ_{t ≤ J} ⌊B/t⌋` (the peak-credit lemma,
  `research/three_level/theory/PEAK_CREDIT_LEMMA.md`), and
* a spoke's services are at most its population, plus its export length,
  plus its peak credit (`k ≤ S + E + late`, `late ≤ peak`).

The dyadic bound `Σ_{t ≤ 2^m} ⌊B/t⌋ ≤ B (m+1)` keeps everything in `ℕ`. -/
namespace SlidingPuzzle.NestedRouting.Ledger
open Finset

structure Counter where
  S : Nat
  G : Nat
  k : Nat
  late : Nat
  peak : Int
  /-- Token services on a retired spoke (draining). -/
  idle : Nat

def Counter.credit (c : Counter) : Int := (c.S : Int)-c.G

def Counter.zero : Counter := ⟨0,0,0,0,0,0⟩

variable {J : Nat}

def active (pop : Fin J → Nat) (st : Fin J → Counter) : Finset (Fin J) :=
  univ.filter (fun j => (st j).S<pop j)

def totalCredit (st : Fin J → Counter) : Int := ∑ j, (st j).credit

/-- `Σ_{a < t ≤ J} (1 + ⌊B/t⌋)`. -/
def tailCharge (B J a : Nat) : Nat := ∑ t ∈ Ioc a J, (1+B/t)

/-- One service on spoke `j`: `real` says the input is a goal, `source`
says the output is a source return. -/
def serve (c : Counter) (pop : Nat) (real source : Bool) : Counter :=
  let S := c.S+(if source then 1 else 0)
  let G := c.G+(if real then 1 else 0)
  ⟨S,G,c.k+1,c.late+(if c.S<pop then 0 else if real then 1 else 0),max c.peak ((S : Int)-G),
    c.idle+(if c.S<pop then 0 else if real then 0 else 1)⟩

/-- The rules a physical service satisfies. -/
structure Allowed (pop E : Fin J → Nat) (st : Fin J → Counter) (j : Fin J)
    (real source : Bool) : Prop where
  source_active : source → (st j).S<pop j
  real_room : real → (st j).G<pop j
  helper_least : real=false → (st j).S<pop j → ∀ i∈active pop st, (st j).credit≤(st i).credit
  early : source=false → (st j).S<pop j → (st j).k<E j

/-- The invariant of a ledger under total-credit cap `B`. -/
structure Good (pop E : Fin J → Nat) (B : Nat) (st : Fin J → Counter) : Prop where
  S_le : ∀ j, (st j).S≤pop j
  G_le : ∀ j, (st j).G≤pop j
  peak_nonneg : ∀ j, 0≤(st j).peak
  credit_le : ∀ j, (st j).credit≤(st j).peak
  active_peak : ∀ j∈active pop st, (st j).peak≤1+((B/(active pop st).card : Nat) : Int)
  retired_sum : ∑ j ∈ univ \ active pop st, (st j).peak≤(tailCharge B J (active pop st).card : Int)
  /-- Retired spokes have distinct ranks above the active count: the active
  count when they retired. -/
  ranks : ∃ τ : Fin J → Nat, ∀ i, ¬(st i).S<pop i → (active pop st).card<τ i ∧ τ i≤J ∧
    (st i).peak≤1+((B/τ i : Nat) : Int) ∧ ∀ i', ¬(st i').S<pop i' → τ i=τ i' → i=i'
  late_zero : ∀ j, (st j).S<pop j → (st j).late=0
  idle_zero : ∀ j, (st j).S<pop j → (st j).idle=0
  late_bound : ∀ j, (st j).S=pop j → ((st j).late : Int)+pop j≤(st j).G+(st j).peak
  services : ∀ j, (st j).k≤(st j).S+E j+(st j).late+(st j).idle

theorem good_zero (pop E : Fin J → Nat) (B : Nat) : Good pop E B (fun _ => Counter.zero) := by
  refine ⟨fun _ => Nat.zero_le _,fun _ => Nat.zero_le _,fun _ => le_rfl,
    fun _ => by simp [Counter.zero,Counter.credit],fun _ _ => by simp only [Counter.zero]; positivity,
    ?_,?_,fun _ _ => rfl,fun _ _ => rfl,?_,fun _ => Nat.zero_le _⟩
  · simp only [Counter.zero,sum_const_zero]
    exact_mod_cast Nat.zero_le _
  · -- the spokes with no population are retired from the start: rank them above the rest
    classical
    set R := univ.filter (fun i : Fin J => ¬(Counter.zero.S<pop i)) with hR
    have hA : active pop (fun _ => Counter.zero)=univ \ R := by
      ext i; simp [active,hR]
    have hc : (active pop (fun _ => Counter.zero)).card+R.card=J := by
      rw [hA,card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin]
      have := card_le_univ R; simp at this; omega
    let e := R.equivFin
    refine ⟨fun i => if hi : i∈R then J-R.card+1+(e ⟨i,hi⟩).val else 0,?_⟩
    intro i hi
    have hiR : i∈R := by simp [hR]; simpa using hi
    simp only [dif_pos hiR]
    have hlt := (e ⟨i,hiR⟩).isLt
    refine ⟨by omega,by omega,by simp only [Counter.zero]; positivity,?_⟩
    intro i' hi' heq
    have hiR' : i'∈R := by simp [hR]; simpa using hi'
    simp only [dif_pos hiR'] at heq
    have : e ⟨i,hiR⟩=e ⟨i',hiR'⟩ := Fin.ext (by omega)
    exact congrArg Subtype.val (e.injective this)
  · intro j hj
    simp only [Counter.zero] at hj ⊢
    omega

/-- Retired spokes have nonnegative credit, so the active credits are capped too. -/
theorem active_credit_le {pop E : Fin J → Nat} {B : Nat} {st : Fin J → Counter}
    (h : Good pop E B st) (cap : totalCredit st≤B) :
    ∑ i ∈ active pop st, (st i).credit≤B := by
  have split := sum_filter_add_sum_filter_not univ (fun i => (st i).S<pop i) (fun i => (st i).credit)
  have retired : 0≤∑ i ∈ univ.filter (fun i => ¬(st i).S<pop i), (st i).credit := by
    apply sum_nonneg
    intro i hi
    have hS : (st i).S=pop i := le_antisymm (h.S_le i) (by simpa using (mem_filter.mp hi).2)
    have hG := h.G_le i
    simp only [Counter.credit]
    omega
  unfold totalCredit at cap
  unfold active
  linarith

/-- A least-credit active spoke has credit at most `B / a`. -/
theorem least_credit_le {pop E : Fin J → Nat} {B : Nat} {st : Fin J → Counter}
    (h : Good pop E B st) (cap : totalCredit st≤B) {j : Fin J} (hj : j∈active pop st)
    (least : ∀ i∈active pop st, (st j).credit≤(st i).credit) :
    (st j).credit≤((B/(active pop st).card : Nat) : Int) := by
  have hpos : 0<(active pop st).card := card_pos.mpr ⟨j,hj⟩
  have hsum : ((active pop st).card : Int)*(st j).credit≤B := by
    have := sum_le_sum least
    simp only [sum_const,nsmul_eq_mul] at this
    exact this.trans (active_credit_le h cap)
  have : (st j).credit≤(B : Int)/((active pop st).card : Int) := by
    rw [Int.le_ediv_iff_mul_le (by exact_mod_cast hpos)]
    linarith
  simpa [Int.natCast_ediv] using this

section Step
variable {pop E : Fin J → Nat} {B : Nat} {st : Fin J → Counter} {j : Fin J} {c' : Counter}

theorem mem_active_update_ne {i : Fin J} (hij : i≠j) :
    i∈active pop (Function.update st j c') ↔ i∈active pop st := by
  simp [active,Function.update_of_ne hij]

theorem active_update_same (same : c'.S<pop j ↔ (st j).S<pop j) :
    active pop (Function.update st j c')=active pop st := by
  ext i
  by_cases hij : i=j
  · subst hij; simp [active,same]
  · exact mem_active_update_ne hij

theorem active_update_retire (was : (st j).S<pop j) (now : ¬c'.S<pop j) :
    active pop (Function.update st j c')=(active pop st).erase j := by
  ext i
  by_cases hij : i=j
  · subst hij; simp [active,now]
  · rw [mem_erase,mem_active_update_ne hij]
    exact ⟨fun h => ⟨hij,h⟩,fun h => h.2⟩

theorem tailCharge_step (B J a : Nat) (ha : 1≤a) (haJ : a≤J) :
    tailCharge B J (a-1)=(1+B/a)+tailCharge B J a := by
  unfold tailCharge
  rw [←sum_Ioc_consecutive _ (Nat.sub_le a 1) haJ]
  have : Ioc (a-1) a={a} := by
    have := Nat.Ioc_succ_singleton (a-1)
    rwa [Nat.sub_add_cancel ha] at this
  rw [this,sum_singleton]

theorem serve_S (c : Counter) (p : Nat) (real source : Bool) :
    (serve c p real source).S=c.S+(if source then 1 else 0) := rfl
theorem serve_G (c : Counter) (p : Nat) (real source : Bool) :
    (serve c p real source).G=c.G+(if real then 1 else 0) := rfl
theorem serve_k (c : Counter) (p : Nat) (real source : Bool) :
    (serve c p real source).k=c.k+1 := rfl
theorem serve_late (c : Counter) (p : Nat) (real source : Bool) :
    (serve c p real source).late=c.late+(if c.S<p then 0 else if real then 1 else 0) := rfl
theorem serve_idle (c : Counter) (p : Nat) (real source : Bool) :
    (serve c p real source).idle=c.idle+(if c.S<p then 0 else if real then 0 else 1) := rfl
theorem serve_peak (c : Counter) (p : Nat) (real source : Bool) :
    (serve c p real source).peak=max c.peak (serve c p real source).credit := rfl
theorem serve_credit (c : Counter) (p : Nat) (real source : Bool) :
    (serve c p real source).credit=c.credit+(if source then 1 else 0)-(if real then 1 else 0) := by
  simp only [Counter.credit,serve_S,serve_G]
  split_ifs <;> push_cast <;> ring

end Step

/-- One allowed service preserves the ledger invariant. -/
theorem Good.step {pop E : Fin J → Nat} {B : Nat} {st : Fin J → Counter}
    (h : Good pop E B st) (cap : totalCredit st≤B) {j : Fin J} {real source : Bool}
    (al : Allowed pop E st j real source) :
    Good pop E B (Function.update st j (serve (st j) (pop j) real source)) := by
  set c' := serve (st j) (pop j) real source with hc'
  set st' := Function.update st j c' with hst'
  have at_j : st' j=c' := by simp [st']
  have at_ne {i : Fin J} (hij : i≠j) : st' i=st i := by simp [st',Function.update_of_ne hij]
  have hS := h.S_le j
  have hG := h.G_le j
  have hcred := h.credit_le j
  have hpk := h.peak_nonneg j
  have cS' : c'.S=(st j).S+(if source then 1 else 0) := serve_S _ _ _ _
  have cG' : c'.G=(st j).G+(if real then 1 else 0) := serve_G _ _ _ _
  have ck' : c'.k=(st j).k+1 := serve_k _ _ _ _
  have cl' : c'.late=(st j).late+(if (st j).S<pop j then 0 else if real then 1 else 0) := serve_late _ _ _ _
  have ci' : c'.idle=(st j).idle+(if (st j).S<pop j then 0 else if real then 0 else 1) := serve_idle _ _ _ _
  have cp' : c'.peak=max (st j).peak c'.credit := serve_peak _ _ _ _
  have cc' : c'.credit=(st j).credit+(if source then 1 else 0)-(if real then 1 else 0) :=
    serve_credit _ _ _ _
  have cS : c'.S≤pop j := by
    rw [cS']
    split_ifs with hs
    · have := al.source_active hs; omega
    · omega
  have hsrcAct : source=true → (st j).S<pop j := fun hs => al.source_active hs
  -- the new peak, when the spoke was active
  have newPeak (was : (st j).S<pop j) :
      c'.peak≤1+((B/(active pop st).card : Nat) : Int) := by
    have hj : j∈active pop st := by simp [active,was]
    have old := h.active_peak j hj
    rw [cp']
    refine max_le old ?_
    rw [cc']
    cases real
    · have least := least_credit_le h cap hj (al.helper_least rfl was)
      push_cast at least old ⊢
      split_ifs <;> first | contradiction | linarith
    · push_cast at old ⊢
      split_ifs <;> first | contradiction | linarith
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    by_cases hij : i=j
    · rw [hij,at_j]; exact cS
    · rw [at_ne hij]; exact h.S_le i
  · intro i
    by_cases hij : i=j
    · rw [hij,at_j,cG']
      split_ifs with hr
      · have := al.real_room hr; omega
      · omega
    · rw [at_ne hij]; exact h.G_le i
  · intro i
    by_cases hij : i=j
    · rw [hij,at_j,cp']; exact le_max_of_le_left hpk
    · rw [at_ne hij]; exact h.peak_nonneg i
  · intro i
    by_cases hij : i=j
    · rw [hij,at_j,cp']; exact le_max_right _ _
    · rw [at_ne hij]; exact h.credit_le i
  · -- active peaks
    intro i hi
    by_cases was : (st j).S<pop j
    · by_cases now : c'.S<pop j
      · have same := active_update_same (st:=st) (j:=j) (c':=c') (pop:=pop) ⟨fun _ => was,fun _ => now⟩
        rw [same] at hi ⊢
        by_cases hij : i=j
        · rw [hij,at_j]; exact newPeak was
        · rw [at_ne hij]; exact h.active_peak i hi
      · have ret := active_update_retire (st:=st) (j:=j) (c':=c') (pop:=pop) was now
        rw [ret] at hi ⊢
        obtain ⟨hij,hi'⟩ := mem_erase.mp hi
        rw [at_ne hij]
        have hjA : j∈active pop st := by simp [active,was]
        have old := h.active_peak i hi'
        rw [card_erase_of_mem hjA]
        have hpos : 1<(active pop st).card := by
          have : ({i,j} : Finset (Fin J))⊆active pop st := by
            intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
          have := card_le_card this
          rw [card_pair hij] at this
          omega
        have := Nat.div_le_div_left (a:=B) (Nat.sub_le (active pop st).card 1) (by omega : 0<(active pop st).card-1)
        have : ((B/(active pop st).card : Nat) : Int)≤((B/((active pop st).card-1) : Nat) : Int) := by
          exact_mod_cast this
        linarith
    · have hsrc : source=false := by
        cases source
        · rfl
        · exact absurd (hsrcAct rfl) was
      have now : ¬c'.S<pop j := by rw [cS',hsrc]; simpa using was
      have same := active_update_same (st:=st) (j:=j) (c':=c') (pop:=pop) ⟨fun h' => absurd h' now,fun h' => absurd h' was⟩
      rw [same] at hi ⊢
      have hij : i≠j := by rintro rfl; simp [active,was] at hi
      rw [at_ne hij]; exact h.active_peak i hi
  · -- retired peaks
    by_cases was : (st j).S<pop j
    · have hjA : j∈active pop st := by simp [active,was]
      by_cases now : c'.S<pop j
      · have same := active_update_same (st:=st) (j:=j) (c':=c') (pop:=pop) ⟨fun _ => was,fun _ => now⟩
        rw [same]
        have : ∑ i ∈ univ \ active pop st, (st' i).peak=∑ i ∈ univ \ active pop st, (st i).peak := by
          apply sum_congr rfl
          intro i hi
          have hij : i≠j := by rintro rfl; exact (mem_sdiff.mp hi).2 hjA
          rw [at_ne hij]
        rw [this]; exact h.retired_sum
      · have ret := active_update_retire (st:=st) (j:=j) (c':=c') (pop:=pop) was now
        rw [ret]
        have hset : univ \ (active pop st).erase j=insert j (univ \ active pop st) := by
          ext i; by_cases hij : i=j <;> simp [hij,hjA]
        have hjn : j∉univ \ active pop st := by simp [hjA]
        rw [hset,sum_insert hjn,at_j]
        have rest : ∑ i ∈ univ \ active pop st, (st' i).peak=∑ i ∈ univ \ active pop st, (st i).peak := by
          apply sum_congr rfl
          intro i hi
          have hij : i≠j := by rintro rfl; exact hjn hi
          rw [at_ne hij]
        rw [rest,card_erase_of_mem hjA]
        have hpos : 1≤(active pop st).card := card_pos.mpr ⟨j,hjA⟩
        have hle : (active pop st).card≤J := by
          simpa using card_le_univ (active pop st)
        rw [tailCharge_step B J _ hpos hle]
        push_cast
        have := newPeak was
        have := h.retired_sum
        push_cast at *
        linarith
    · have hsrc : source=false := by
        cases source
        · rfl
        · exact absurd (hsrcAct rfl) was
      have now : ¬c'.S<pop j := by rw [cS',hsrc]; simpa using was
      have same := active_update_same (st:=st) (j:=j) (c':=c') (pop:=pop) ⟨fun h' => absurd h' now,fun h' => absurd h' was⟩
      rw [same]
      have peakSame : c'.peak=(st j).peak := by
        rw [cp',cc',hsrc]
        apply max_eq_left
        cases real <;> simp only [Bool.false_eq_true,if_false,if_true] <;> linarith
      have : ∑ i ∈ univ \ active pop st, (st' i).peak=∑ i ∈ univ \ active pop st, (st i).peak := by
        apply sum_congr rfl
        intro i _
        by_cases hij : i=j
        · rw [hij,at_j,peakSame]
        · rw [at_ne hij]
      rw [this]; exact h.retired_sum
  · -- ranks
    obtain ⟨τ,hτ⟩ := h.ranks
    have retSame {i : Fin J} (hij : i≠j) : ((st' i).S<pop i ↔ (st i).S<pop i) := by rw [at_ne hij]
    by_cases was : (st j).S<pop j
    · have hjA : j∈active pop st := by simp [active,was]
      by_cases now : c'.S<pop j
      · have same := active_update_same (st:=st) (j:=j) (c':=c') (pop:=pop) ⟨fun _ => was,fun _ => now⟩
        refine ⟨τ,?_⟩
        intro i hi
        have hij : i≠j := by rintro rfl; rw [at_j] at hi; exact hi now
        rw [same,at_ne hij]
        rw [at_ne hij] at hi
        obtain ⟨a1,a2,a3,a4⟩ := hτ i hi
        refine ⟨a1,a2,a3,?_⟩
        intro i' hi' heq
        have hi'j : i'≠j := by rintro rfl; rw [at_j] at hi'; exact hi' now
        rw [at_ne hi'j] at hi'
        exact a4 i' hi' heq
      · have ret := active_update_retire (st:=st) (j:=j) (c':=c') (pop:=pop) was now
        have hcard : ((active pop st).erase j).card=(active pop st).card-1 := card_erase_of_mem hjA
        have hpos : 1≤(active pop st).card := card_pos.mpr ⟨j,hjA⟩
        have hle : (active pop st).card≤J := by simpa using card_le_univ (active pop st)
        refine ⟨Function.update τ j (active pop st).card,?_⟩
        intro i hi
        rw [ret,hcard]
        by_cases hij : i=j
        · subst hij
          simp only [Function.update_self]
          refine ⟨by omega,hle,by rw [at_j]; exact newPeak was,?_⟩
          intro i' hi' heq
          by_contra hne
          have hne' : i'≠i := fun e => hne e.symm
          rw [Function.update_of_ne hne'] at heq
          rw [at_ne hne'] at hi'
          have := (hτ i' hi').1
          omega
        · rw [Function.update_of_ne hij]
          rw [at_ne hij] at hi ⊢
          obtain ⟨a1,a2,a3,a4⟩ := hτ i hi
          refine ⟨by omega,a2,a3,?_⟩
          intro i' hi' heq
          by_cases hi'j : i'=j
          · subst hi'j
            rw [Function.update_self] at heq
            omega
          · rw [Function.update_of_ne hi'j] at heq
            rw [at_ne hi'j] at hi'
            exact a4 i' hi' heq
    · have hsrc : source=false := by
        cases source
        · rfl
        · exact absurd (hsrcAct rfl) was
      have now : ¬c'.S<pop j := by rw [cS',hsrc]; simpa using was
      have same := active_update_same (st:=st) (j:=j) (c':=c') (pop:=pop) ⟨fun h' => absurd h' now,fun h' => absurd h' was⟩
      have peakSame : c'.peak=(st j).peak := by
        rw [cp',cc',hsrc]
        apply max_eq_left
        cases real <;> simp only [Bool.false_eq_true,if_false,if_true] <;> linarith
      have stillRet (i : Fin J) : ((st' i).S<pop i ↔ (st i).S<pop i) := by
        by_cases hij : i=j
        · subst hij; rw [at_j]; exact ⟨fun h' => absurd h' now,fun h' => absurd h' was⟩
        · rw [at_ne hij]
      have peakEq (i : Fin J) : (st' i).peak=(st i).peak := by
        by_cases hij : i=j
        · subst hij; rw [at_j,peakSame]
        · rw [at_ne hij]
      refine ⟨τ,?_⟩
      intro i hi
      rw [same,peakEq i]
      rw [stillRet i] at hi
      obtain ⟨a1,a2,a3,a4⟩ := hτ i hi
      exact ⟨a1,a2,a3,fun i' hi' heq => a4 i' ((stillRet i').not.mp hi') heq⟩
  · intro i hi
    by_cases hij : i=j
    · rw [hij,at_j] at hi ⊢
      have was : (st j).S<pop j := by omega
      rw [cl',if_pos was,h.late_zero j was]
    · rw [at_ne hij] at hi ⊢; exact h.late_zero i hi
  · intro i hi
    by_cases hij : i=j
    · rw [hij,at_j] at hi ⊢
      have was : (st j).S<pop j := by omega
      rw [ci',if_pos was,h.idle_zero j was]
    · rw [at_ne hij] at hi ⊢; exact h.idle_zero i hi
  · intro i hi
    by_cases hij : i=j
    · rw [hij,at_j] at hi ⊢
      by_cases was : (st j).S<pop j
      · rw [cl',if_pos was,h.late_zero j was]
        have h1 := le_max_right (st j).peak c'.credit
        rw [←cp'] at h1
        have h2 : c'.credit=(c'.S : Int)-c'.G := rfl
        rw [hi] at h2
        push_cast
        linarith
      · have hSj : (st j).S=pop j := by omega
        have old := h.late_bound j hSj
        have hsrc : source=false := by
          cases source
          · rfl
          · exact absurd (hsrcAct rfl) was
        rw [cl',cG',cp',if_neg was]
        have := le_max_left (st j).peak c'.credit
        cases real <;> simp only [Bool.false_eq_true,if_false,if_true] <;> push_cast <;> linarith
    · rw [at_ne hij] at hi ⊢; exact h.late_bound i hi
  · intro i
    by_cases hij : i=j
    · rw [hij,at_j,ck',cS',cl',ci']
      have old := h.services j
      cases source
      · simp only [Bool.false_eq_true,if_false]
        by_cases was : (st j).S<pop j
        · have := al.early rfl was
          simp only [if_pos was]; omega
        · simp only [if_neg was]; split_ifs <;> omega
      · simp only [if_true]; split_ifs <;> omega
    · rw [at_ne hij]; exact h.services i

theorem tailCharge_mono {B B' : Nat} (hB : B≤B') (J a : Nat) : tailCharge B J a≤tailCharge B' J a := by
  apply sum_le_sum
  intro t _
  have := Nat.div_le_div_right (c:=t) hB
  omega

/-- A larger total-credit cap keeps the invariant. -/
theorem Good.relax {pop E : Fin J → Nat} {B B' : Nat} {st : Fin J → Counter}
    (h : Good pop E B st) (hB : B≤B') : Good pop E B' st := by
  refine { h with active_peak := ?_, retired_sum := ?_, ranks := ?_ }
  · intro j hj
    have := h.active_peak j hj
    have hd : B/(active pop st).card≤B'/(active pop st).card := Nat.div_le_div_right hB
    have : ((B/(active pop st).card : Nat) : Int)≤((B'/(active pop st).card : Nat) : Int) := by
      exact_mod_cast hd
    linarith
  · have := h.retired_sum
    have hm : (tailCharge B J (active pop st).card : Int)≤tailCharge B' J (active pop st).card := by
      exact_mod_cast tailCharge_mono hB J _
    linarith
  · obtain ⟨τ,hτ⟩ := h.ranks
    refine ⟨τ,fun i hi => ?_⟩
    obtain ⟨a1,a2,a3,a4⟩ := hτ i hi
    refine ⟨a1,a2,?_,a4⟩
    have hd : B/τ i≤B'/τ i := Nat.div_le_div_right hB
    have : ((B/τ i : Nat) : Int)≤((B'/τ i : Nat) : Int) := by exact_mod_cast hd
    linarith

/-- The peak-credit lemma. -/
theorem Good.peak_sum {pop E : Fin J → Nat} {B : Nat} {st : Fin J → Counter}
    (h : Good pop E B st) : ∑ j, (st j).peak≤(tailCharge B J 0 : Int) := by
  have ret := h.retired_sum
  have hact : ∑ j ∈ active pop st, (st j).peak≤((active pop st).card : Int)*
      (1+((B/(active pop st).card : Nat) : Int)) := by
    have := sum_le_sum (s:=active pop st) (fun j hj => h.active_peak j hj)
    simpa [sum_const,nsmul_eq_mul] using this
  have split := sum_sdiff (s₁:=active pop st) (s₂:=univ) (f:=fun j => (st j).peak) (subset_univ _)
  have haJ : (active pop st).card≤J := by simpa using card_le_univ (active pop st)
  generalize (active pop st).card=a at ret hact haJ
  have tail0 : tailCharge B J 0=(∑ t ∈ Ioc 0 a, (1+B/t))+tailCharge B J a := by
    unfold tailCharge
    rw [sum_Ioc_consecutive _ (Nat.zero_le a) haJ]
  have head : a*(1+B/a)≤∑ t ∈ Ioc 0 a, (1+B/t) := by
    have : ∀ t∈Ioc 0 a, 1+B/a≤1+B/t := by
      intro t ht
      have := Nat.div_le_div_left (a:=B) (mem_Ioc.mp ht).2 (mem_Ioc.mp ht).1
      omega
    have := sum_le_sum this
    simpa [sum_const,Nat.card_Ioc] using this
  have head' : ((a*(1+B/a) : Nat) : Int)≤((∑ t ∈ Ioc 0 a, (1+B/t) : Nat) : Int) := by
    exact_mod_cast head
  rw [tail0,←split]
  push_cast at head' hact ret ⊢
  linarith

/-- Dyadic blocks: `Σ_{t ≤ 2^m} ⌊B/t⌋ ≤ B (m+1)`. -/
theorem harmonic_dyadic (B m : Nat) : ∑ t ∈ Ioc 0 (2^m), B/t≤B*(m+1) := by
  induction m with
  | zero =>
    have : Ioc 0 1=({1} : Finset Nat) := by decide
    simp [this]
  | succ m ih =>
    have hle : 2^m≤2^(m+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [←sum_Ioc_consecutive _ (Nat.zero_le _) hle]
    have block : ∑ t ∈ Ioc (2^m) (2^(m+1)), B/t≤B := by
      have each : ∀ t∈Ioc (2^m) (2^(m+1)), B/t≤B/2^m := by
        intro t ht
        exact Nat.div_le_div_left (le_of_lt (mem_Ioc.mp ht).1) (by positivity)
      have := sum_le_sum each
      rw [sum_const,Nat.card_Ioc,smul_eq_mul] at this
      have h2 : 2^(m+1)-2^m=2^m := by rw [pow_succ]; omega
      rw [h2] at this
      exact this.trans (Nat.mul_div_le B (2^m))
    calc _ ≤ B*(m+1)+B := Nat.add_le_add ih block
      _ = B*(m+1+1) := by ring

theorem tailCharge_zero_le (B J p q : Nat) (harm : q*∑ t ∈ Ioc 0 J, B/t≤p*B) :
    q*tailCharge B J 0≤q*J+p*B := by
  unfold tailCharge
  rw [sum_add_distrib]
  simp only [sum_const,Nat.card_Ioc,Nat.sub_zero,smul_eq_mul,mul_one]
  rw [Nat.mul_add]
  omega

/-- The dyadic harmonic bound: `J ≤ 2^m` gives `H_J ≤ m+1`. -/
theorem harm_dyadic {J m : Nat} (hJ : J≤2^m) (B : Nat) : 1*∑ t ∈ Ioc 0 J, B/t≤(m+1)*B := by
  rw [Nat.one_mul,Nat.mul_comm]
  exact (sum_le_sum_of_subset (Ioc_subset_Ioc_right hJ)).trans (harmonic_dyadic B m)

/-- Ceiling division. -/
def cdiv (x q : Nat) : Nat := (x+q-1)/q

theorem le_mul_cdiv {x q : Nat} (hq : 0<q) : x≤q*cdiv x q := by
  unfold cdiv
  have := Nat.div_add_mod (x+q-1) q
  have := Nat.mod_lt (x+q-1) hq
  omega

theorem cdiv_le {x q : Nat} : q*cdiv x q≤x+q-1 := by
  unfold cdiv
  exact Nat.mul_div_le (x+q-1) q

/-- Rescale a fractional bound `q·S ≤ q·J + p·β` by a cost `c`. -/
theorem scale_frac {S J p q β : Nat} (hq : 0<q) (h : q*S≤q*J+p*β) (c : Nat) :
    c*S≤c*J+cdiv (c*p) q*β := by
  have h1 : q*(c*S)≤q*(c*J)+c*p*β := by
    have := Nat.mul_le_mul_left c h
    calc q*(c*S)=c*(q*S) := by ring
      _≤c*(q*J+p*β) := this
      _=q*(c*J)+c*p*β := by ring
  have h2 : c*p*β≤q*cdiv (c*p) q*β := Nat.mul_le_mul_right _ (le_mul_cdiv hq)
  have h3 : q*(c*S)≤q*(c*J+cdiv (c*p) q*β) := by
    calc q*(c*S)≤q*(c*J)+q*cdiv (c*p) q*β := by omega
      _=q*(c*J+cdiv (c*p) q*β) := by ring
  exact Nat.le_of_mul_le_mul_left h3 hq

theorem Good.late_le_peak {pop E : Fin J → Nat} {B : Nat} {st : Fin J → Counter}
    (h : Good pop E B st) (j : Fin J) : ((st j).late : Int)≤(st j).peak := by
  by_cases hj : (st j).S<pop j
  · rw [h.late_zero j hj]; exact_mod_cast h.peak_nonneg j
  · have hS : (st j).S=pop j := le_antisymm (h.S_le j) (by omega)
    have := h.late_bound j hS
    have := h.G_le j
    linarith

/-- Services on a spoke: population, plus export length, plus peak credit,
plus draining services. -/
theorem Good.services_le {pop E : Fin J → Nat} {B : Nat} {st : Fin J → Counter}
    (h : Good pop E B st) (j : Fin J) :
    ((st j).k : Int)≤pop j+E j+(st j).peak+(st j).idle := by
  have := h.services j
  have := h.S_le j
  have := h.late_le_peak j
  linarith


/-- Every spoke has a rank: distinct values in `1..J`, each bounding its peak
by `1 + ⌊B/τ⌋`. Active spokes take the ranks up to the active count. -/
theorem Good.rank_all {pop E : Fin J → Nat} {B : Nat} {st : Fin J → Counter}
    (h : Good pop E B st) : ∃ τ : Fin J → Nat, Function.Injective τ ∧ (∀ i, 1≤τ i ∧ τ i≤J) ∧
      ∀ i, (st i).peak≤1+((B/τ i : Nat) : Int) := by
  classical
  obtain ⟨τ,hτ⟩ := h.ranks
  set A := active pop st with hAdef
  let e := A.equivFin
  have mem {i : Fin J} : i∈A ↔ (st i).S<pop i := by simp [hAdef,active]
  refine ⟨fun i => if hi : i∈A then 1+(e ⟨i,hi⟩).val else τ i,?_,?_,?_⟩
  · intro i i' heq
    simp only at heq
    by_cases hi : i∈A <;> by_cases hi' : i'∈A
    · rw [dif_pos hi,dif_pos hi'] at heq
      have : e ⟨i,hi⟩=e ⟨i',hi'⟩ := Fin.ext (by omega)
      exact congrArg Subtype.val (e.injective this)
    · rw [dif_pos hi,dif_neg hi'] at heq
      have := (hτ i' (mt mem.mpr hi')).1
      have := (e ⟨i,hi⟩).isLt
      omega
    · rw [dif_neg hi,dif_pos hi'] at heq
      have := (hτ i (mt mem.mpr hi)).1
      have := (e ⟨i',hi'⟩).isLt
      omega
    · rw [dif_neg hi,dif_neg hi'] at heq
      exact (hτ i (mt mem.mpr hi)).2.2.2 i' (mt mem.mpr hi') heq
  · intro i
    have hAJ : A.card≤J := by simpa using card_le_univ A
    by_cases hi : i∈A
    · simp only [dif_pos hi]; have := (e ⟨i,hi⟩).isLt; omega
    · simp only [dif_neg hi]; have := hτ i (mt mem.mpr hi); omega
  · intro i
    by_cases hi : i∈A
    · simp only [dif_pos hi]
      have old := h.active_peak i hi
      have hlt := (e ⟨i,hi⟩).isLt
      have hd : B/A.card≤B/(1+(e ⟨i,hi⟩).val) := Nat.div_le_div_left (by omega) (by omega)
      have : ((B/A.card : Nat) : Int)≤((B/(1+(e ⟨i,hi⟩).val) : Nat) : Int) := by exact_mod_cast hd
      rw [←hAdef] at old
      linarith
    · simp only [dif_neg hi]; exact (hτ i (mt mem.mpr hi)).2.2.1

/-- Distinct positive values: `Σ_{t∈S} ⌊B/t⌋ ≤ Σ_{t ≤ |S|} ⌊B/t⌋`. -/
theorem sum_div_distinct (B : Nat) (S : Finset Nat) (hS : ∀ t∈S, 1≤t) :
    ∑ t ∈ S, B/t≤∑ t ∈ Ioc 0 S.card, B/t := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert m S hm ih =>
    have hmS : m∉S := fun hm' => lt_irrefl _ (hm m hm')
    rw [sum_insert hmS,card_insert_of_notMem hmS,sum_Ioc_succ_top (Nat.zero_le _)]
    have ih' := ih (fun t ht => hS t (mem_insert_of_mem ht))
    -- the largest value is at least the count
    have hsub : insert m S⊆Ioc 0 m := by
      intro t ht
      rcases mem_insert.mp ht with rfl | ht
      · exact mem_Ioc.mpr ⟨hS _ (mem_insert_self _ _),le_rfl⟩
      · exact mem_Ioc.mpr ⟨hS t (mem_insert_of_mem ht),le_of_lt (hm t ht)⟩
    have hcard := card_le_card hsub
    rw [card_insert_of_notMem hmS,Nat.card_Ioc] at hcard
    have : B/m≤B/(S.card+1) := Nat.div_le_div_left (by omega) (by omega)
    omega

/-- The layered harmonic charge of weights `ρ`: for each level `v`, the
harmonic sum up to the number of spokes of weight above `v`. -/
def layered (ρ : Fin J → Nat) (B : Nat) : Nat :=
  ∑ v ∈ range (univ.sup ρ), ∑ t ∈ Ioc 0 (univ.filter (fun j => v<ρ j)).card, B/t

/-- The weighted peak-credit lemma: `Σ ρ_j peak_j ≤ Σ ρ_j + layered ρ B`. -/
theorem Good.weighted_peak {pop E : Fin J → Nat} {B : Nat} {st : Fin J → Counter}
    (h : Good pop E B st) (ρ : Fin J → Nat) :
    ∑ j, ρ j*(st j).peak.toNat≤∑ j, ρ j+layered ρ B := by
  classical
  obtain ⟨τ,inj,hr,hp⟩ := h.rank_all
  have each (j : Fin J) : ρ j*(st j).peak.toNat≤ρ j+ρ j*(B/τ j) := by
    have := hp j
    have h0 := h.peak_nonneg j
    have : (st j).peak.toNat≤1+B/τ j := by omega
    calc ρ j*(st j).peak.toNat≤ρ j*(1+B/τ j) := Nat.mul_le_mul_left _ this
      _=_ := by ring
  refine (sum_le_sum (fun j _ => each j)).trans ?_
  rw [sum_add_distrib]
  apply Nat.add_le_add_left
  -- layer cake: `ρ j = #{v < sup ρ : v < ρ j}`
  have layer (j : Fin J) : ρ j*(B/τ j)=∑ v ∈ range (univ.sup ρ), if v<ρ j then B/τ j else 0 := by
    rw [sum_ite,sum_const_zero,Nat.add_zero,sum_const,smul_eq_mul]
    congr 1
    have hle : ρ j≤univ.sup ρ := le_sup (mem_univ j)
    have : (range (univ.sup ρ)).filter (fun v => v<ρ j)=range (ρ j) := by
      ext v; simp only [mem_filter,mem_range]; omega
    rw [this,card_range]
  rw [sum_congr rfl (fun j _ => layer j),sum_comm]
  unfold layered
  apply sum_le_sum
  intro v _
  rw [←sum_filter]
  set F := univ.filter (fun j => v<ρ j)
  rw [←sum_image (f:=fun t => B/t) (fun a _ b _ e => inj e)]
  have hc : (F.image τ).card=F.card := card_image_of_injective _ inj
  rw [←hc]
  exact sum_div_distinct B _ (fun t ht => by
    obtain ⟨j,_,rfl⟩ := mem_image.mp ht; exact (hr j).1)

end SlidingPuzzle.NestedRouting.Ledger
