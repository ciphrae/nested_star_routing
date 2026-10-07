import NestedRouting.Board.Basic
import NestedRouting.Interface.ReservePolicy

/-! Five occurrence roles of the tiles in a paused region: core and reserve
sources, helpers, core and reserve finals. A received reserve final is
distinct from a reusable helper. Every availability statement below is
derived from literal board contents and finite cardinalities. -/
namespace SlidingPuzzle.NestedRouting.TileRoles
open Finset
open SlidingPuzzle.NestedRouting.ReservePolicy
variable {n : Nat}

inductive Role where
  | coreSource | reserveSource | helper | coreFinal | reserveFinal
  deriving DecidableEq

instance : Fintype Role := ⟨{.coreSource,.reserveSource,.helper,.coreFinal,.reserveFinal},
  by intro i; cases i <;> simp⟩

def Roles (n : Nat) := Role → Finset (Tile n)

def contents (p : Roles n) : Finset (Tile n) := univ.biUnion p

structure Inventory (R : Finset (Cell n)) (B : Board n) (p : Roles n) : Prop where
  disjoint : ∀ i j, i≠j → Disjoint (p i) (p j)
  exact : R.image B=contents p

theorem role_present {R : Finset (Cell n)} {B : Board n} {p : Roles n}
    (h : Inventory R B p) (i : Role) : p i ⊆ R.image B := by
  intro x hx
  rw [h.exact]
  exact mem_biUnion.mpr ⟨i,mem_univ _,hx⟩

theorem outside_fresh {R : Finset (Cell n)} {B : Board n} {p : Roles n}
    (h : Inventory R B p) {e : Cell n} (he : e∉R) :
    ∀ i, B e∉p i := by
  intro i hi
  obtain ⟨x,hx,heq⟩ := mem_image.mp (role_present h i hi)
  exact he (B.injective heq ▸ hx)

theorem role_card_sum {R : Finset (Cell n)} {B : Board n} {p : Roles n}
    (h : Inventory R B p) :
    R.card=(p .coreSource).card+(p .reserveSource).card+(p .helper).card+
      (p .coreFinal).card+(p .reserveFinal).card := by
  have hc := congrArg Finset.card h.exact
  rw [card_image_of_injective _ B.injective] at hc
  unfold contents at hc
  rw [card_biUnion (fun i _ j _ hij => h.disjoint i j hij)] at hc
  have enum : (univ : Finset Role)={.coreSource,.reserveSource,.helper,.coreFinal,.reserveFinal} := by decide
  simpa [enum,add_assoc] using hc

/-- The bookkeeping of a paused region with cells `R`: the exact five-role
inventory `p` and the policy counters `c`. -/
structure State (R : Finset (Cell n)) (B : Board n) (M r g : Nat) (p : Roles n) (c : Counts) :
    Prop where
  inventory : Inventory R B p
  size : R.card=M+r+g
  coreSources : (p .coreSource).card+c.ec=M
  reserveSources : (p .reserveSource).card+c.er=r
  coreFinals : (p .coreFinal).card=c.ac
  reserveFinals : (p .reserveFinal).card=c.ar
  valid : c.Valid M r

namespace State
variable {R : Finset (Cell n)} {B : Board n} {M r g : Nat} {p : Roles n} {c : Counts}

theorem helper_mass (st : State R B M r g p c) :
    (p .helper).card+c.ac+c.ar=g+c.ec+c.er := by
  have hs := role_card_sum st.inventory
  have hc := st.coreSources
  have hr := st.reserveSources
  have hf := st.coreFinals
  have hg := st.reserveFinals
  rw [st.size] at hs
  omega

theorem helper_population (st : State R B M r g p c) (hg : 6≤g) :
    6≤(p .helper).card :=
  helpers_available st.valid g _ hg st.helper_mass

theorem source_core (st : State R B M r g p c) :
    (p .coreSource).Nonempty ↔ c.ec<M := by
  rw [←card_pos]
  have hc := st.coreSources
  omega

theorem source_reserve (st : State R B M r g p c) :
    (p .reserveSource).Nonempty ↔ c.er<r := by
  rw [←card_pos]
  have hc := st.reserveSources
  omega

/-- The protected set may include the blank. At least two actual helper
occupants lie outside any four protected cells. No auxiliary classifier is
used to distinguish a helper from a received final. -/
theorem movable_helpers (st : State R B M r g p c) (hg : 6≤g)
    (guarded : Finset (Cell n)) (small : guarded.card≤4) :
    2≤((p .helper) \ guarded.image B).card := by
  have hp := st.helper_population hg
  have hi := card_image_le (s:=guarded) (f:=B)
  have hs := le_card_sdiff (guarded.image B) (p .helper)
  omega

theorem helper_cell (st : State R B M r g p c) (hg : 6≤g)
    (guarded : Finset (Cell n)) (small : guarded.card≤4) :
    ∃ z∈R, z∉guarded ∧ B z∈p .helper := by
  have hpos : 0<((p .helper) \ guarded.image B).card := by
    have h := st.movable_helpers hg guarded small
    omega
  obtain ⟨t,ht⟩ := card_pos.mp hpos
  obtain ⟨hrole,houtside⟩ := mem_sdiff.mp ht
  obtain ⟨z,hz,rfl⟩ := mem_image.mp (role_present st.inventory .helper hrole)
  exact ⟨z,hz,fun hin => houtside (mem_image.mpr ⟨z,hin,rfl⟩),hrole⟩

/-- Literal input freshness supplies the goal-population guard. -/
theorem fresh_core (st : State R B M r g p c) (goals : Finset (Tile n))
    (owned : p .coreFinal ⊆ goals) (capacity : goals.card≤M)
    (e : Cell n) (he : e∉R) (input : B e∈goals) : c.ac<M := by
  have fresh := outside_fresh st.inventory he Role.coreFinal
  have hc := card_le_card (insert_subset input owned)
  rw [card_insert_of_notMem fresh,st.coreFinals] at hc
  omega

theorem fresh_reserve (st : State R B M r g p c) (goals : Finset (Tile n))
    (owned : p .reserveFinal ⊆ goals) (capacity : goals.card≤r)
    (e : Cell n) (he : e∉R) (input : B e∈goals) : c.ar<r := by
  have fresh := outside_fresh st.inventory he Role.reserveFinal
  have hc := card_le_card (insert_subset input owned)
  rw [card_insert_of_notMem fresh,st.reserveFinals] at hc
  omega
end State

/-- All swaps inside the parent preserve its contents. Only the exchange
with e changes its inventory. In particular the parity stores u,v are
allowed, and required, to be inside the parent. -/
theorem exchange_parent_contents (R : Finset (Cell n)) (B C : Board n)
    (e z u v : Cell n) (he : e∉R) (hz : z∈R) (hu : u∈R) (hv : v∈R)
    (hzu : z≠u) (hzv : z≠v)
    (load : C z=B e) (storeU : C u=B v) (storeV : C v=B u)
    (fixed : ∀ x, x≠e → x≠z → x≠u → x≠v → C x=B x) :
    R.image C=insert (B e) ((R.image B).erase (B z)) := by
  apply Subset.antisymm
  · intro t ht
    obtain ⟨x,hx,rfl⟩ := mem_image.mp ht
    by_cases hxz : x=z
    · subst x
      rw [load]
      exact mem_insert_self _ _
    · apply mem_insert_of_mem
      by_cases hxu : x=u
      · subst x
        rw [storeU]
        exact mem_erase.mpr ⟨fun h => hzv (B.injective h).symm,mem_image.mpr ⟨v,hv,rfl⟩⟩
      · by_cases hxv : x=v
        · subst x
          rw [storeV]
          exact mem_erase.mpr ⟨fun h => hzu (B.injective h).symm,mem_image.mpr ⟨u,hu,rfl⟩⟩
        · rw [fixed x (fun h => he (h ▸ hx)) hxz hxu hxv]
          exact mem_erase.mpr ⟨fun h => hxz (B.injective h),mem_image.mpr ⟨x,hx,rfl⟩⟩
  · intro t ht
    rcases mem_insert.mp ht with rfl | ht
    · exact mem_image.mpr ⟨z,hz,load⟩
    · obtain ⟨hnt,ht⟩ := mem_erase.mp ht
      obtain ⟨x,hx,rfl⟩ := mem_image.mp ht
      have hxz : x≠z := fun h => hnt (congrArg B h)
      by_cases hxu : x=u
      · subst x
        exact mem_image.mpr ⟨v,hv,storeV⟩
      · by_cases hxv : x=v
        · subst x
          exact mem_image.mpr ⟨u,hu,storeU⟩
        · exact mem_image.mpr ⟨x,hx,fixed x (fun h => he (h ▸ hx)) hxz hxu hxv⟩

/-- A three-cycle `(e q u)` with `e` outside and `q, u` inside: the contents
change exactly by the input `B e` replacing `B q`. -/
theorem cycle_parent_contents (R : Finset (Cell n)) (B C : Board n)
    (e q u : Cell n) (he : e∉R) (hq : q∈R) (hu : u∈R) (hqu : q≠u)
    (sq : C q=B u) (su : C u=B e) (fixed : ∀ x, x≠e → x≠q → x≠u → C x=B x) :
    R.image C=insert (B e) ((R.image B).erase (B q)) := by
  apply Subset.antisymm
  · intro t ht
    obtain ⟨x,hx,rfl⟩ := mem_image.mp ht
    by_cases hxq : x=q
    · subst x; rw [sq]
      exact mem_insert_of_mem (mem_erase.mpr ⟨fun h => hqu (B.injective h).symm,mem_image.mpr ⟨u,hu,rfl⟩⟩)
    by_cases hxu : x=u
    · subst x; rw [su]; exact mem_insert_self _ _
    rw [fixed x (fun h => he (h ▸ hx)) hxq hxu]
    exact mem_insert_of_mem (mem_erase.mpr ⟨fun h => hxq (B.injective h),mem_image.mpr ⟨x,hx,rfl⟩⟩)
  · intro t ht
    rcases mem_insert.mp ht with rfl | ht
    · exact mem_image.mpr ⟨u,hu,su⟩
    · obtain ⟨hnt,ht⟩ := mem_erase.mp ht
      obtain ⟨x,hx,rfl⟩ := mem_image.mp ht
      have hxq : x≠q := fun h => hnt (congrArg B h)
      by_cases hxu : x=u
      · subst x; exact mem_image.mpr ⟨q,hq,sq⟩
      · exact mem_image.mpr ⟨x,hx,fixed x (fun h => he (h ▸ hx)) hxq hxu⟩

/-- Moving the blank within a parent changes no parent label inventory,
even though its internal cells can be arbitrarily permuted. -/
theorem contents_eq_of_exterior_fixed (R : Finset (Cell n)) (B C : Board n)
    (fixed : ∀ x, x∉R → C x=B x) : R.image C=R.image B := by
  ext t
  simp only [mem_image]
  constructor
  · rintro ⟨x,hx,hxt⟩
    have inside : B.symm t∈R := by
      by_contra outside
      have h := fixed (B.symm t) outside
      rw [B.apply_symm_apply] at h
      have same : B.symm t=x := C.injective (h.trans hxt.symm)
      exact outside (same.symm ▸ hx)
    exact ⟨B.symm t,inside,B.apply_symm_apply _⟩
  · rintro ⟨x,hx,hxt⟩
    have inside : C.symm t∈R := by
      by_contra outside
      have h := fixed (C.symm t) outside
      rw [C.apply_symm_apply] at h
      have same : C.symm t=x := B.injective (h.symm.trans hxt.symm)
      exact outside (same.symm ▸ hx)
    exact ⟨C.symm t,inside,C.apply_symm_apply _⟩

end SlidingPuzzle.NestedRouting.TileRoles
