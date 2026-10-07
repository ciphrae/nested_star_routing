import NestedRouting.Interface.Roles

/-! The eight source-first transitions, selected from the exact role
inventory of a region.
Core and reserve goal freshness supplies their input guards. -/
namespace SlidingPuzzle.NestedRouting.TileRoles
open Finset
open SlidingPuzzle.NestedRouting.ReservePolicy

inductive Arrival where
  | helper | core | reserve
  deriving DecidableEq

inductive Export where
  | core | reserve | helper
  deriving DecidableEq

def Arrival.role : Arrival → Role
  | .helper => .helper
  | .core => .coreFinal
  | .reserve => .reserveFinal

def Export.role : Export → Role
  | .core => .coreSource
  | .reserve => .reserveSource
  | .helper => .helper

def advance (c : Counts) (input : Arrival) (out : Export) : Counts :=
  ⟨c.ec+(if out=.core then 1 else 0),c.er+(if out=.reserve then 1 else 0),
    c.ac+(if input=.core then 1 else 0),c.ar+(if input=.reserve then 1 else 0)⟩

def RequestGuard (M r : Nat) (c : Counts) : Arrival → Prop
  | .helper => c.ec<M ∨ c.er<r
  | .core => c.ac<M
  | .reserve => c.ar<r

def select (M r : Nat) (c : Counts) : Arrival → Export
  | .helper => if c.ec<M then .core else .reserve
  | .core => if c.ec<M then .core else if c.er<r then .reserve else .helper
  | .reserve => if c.er<r then .reserve else if c.ec<M then .core else .helper

/-- Every guarded, selected transition keeps the counters valid. -/
theorem valid_advance {M r : Nat} {c : Counts} (v : c.Valid M r)
    (input : Arrival) (guard : RequestGuard M r c input) :
    (advance c input (select M r c input)).Valid M r := by
  obtain ⟨h1,h2,h3,h4,h5,h6⟩ := v
  cases input <;> simp only [RequestGuard] at guard <;> simp only [select] <;> split_ifs <;>
    simp only [advance,Counts.Valid,reduceCtorEq,if_true,if_false] <;> omega

namespace State
variable {n : Nat} {R : Finset (Cell n)} {B : Board n} {M r g : Nat} {p : Roles n} {c : Counts}

theorem selected_available (st : State R B M r g p c) (hg : 6≤g)
    (input : Arrival) (guard : RequestGuard M r c input) :
    (p (select M r c input).role).Nonempty := by
  cases input with
  | helper =>
    change c.ec<M ∨ c.er<r at guard
    by_cases hc : c.ec<M
    · simpa [select,hc,Export.role] using st.source_core.mpr hc
    · have hr : c.er<r := guard.resolve_left hc
      simpa [select,hc,Export.role] using st.source_reserve.mpr hr
  | core =>
    by_cases hc : c.ec<M
    · simpa [select,hc,Export.role] using st.source_core.mpr hc
    · by_cases hr : c.er<r
      · simpa [select,hc,hr,Export.role] using st.source_reserve.mpr hr
      · have hp : 0<(p .helper).card := by
          have := st.helper_population hg
          omega
        simpa [select,hc,hr,Export.role] using card_pos.mp hp
  | reserve =>
    by_cases hr : c.er<r
    · simpa [select,hr,Export.role] using st.source_reserve.mpr hr
    · by_cases hc : c.ec<M
      · simpa [select,hc,hr,Export.role] using st.source_core.mpr hc
      · have hp : 0<(p .helper).card := by
          have := st.helper_population hg
          omega
        simpa [select,hc,hr,Export.role] using card_pos.mp hp

/-- The selected output is a physical occupant. When it is a global helper,
it can be selected outside the four protected cells. Its membership is in
the helper role, not merely in the inner auxiliary classifier. -/
theorem selected_cell (st : State R B M r g p c) (hg : 6≤g)
    (input : Arrival) (guard : RequestGuard M r c input)
    (guarded : Finset (Cell n)) (small : guarded.card≤4) :
    ∃ z∈R, B z∈p (select M r c input).role ∧
      (select M r c input=.helper → z∉guarded) := by
  by_cases helper : select M r c input=.helper
  · obtain ⟨z,hz,houtside,hrole⟩ := st.helper_cell hg guarded small
    exact ⟨z,hz,by simpa [helper,Export.role] using hrole,fun _ => houtside⟩
  · obtain ⟨t,ht⟩ := st.selected_available hg input guard
    obtain ⟨z,hz,rfl⟩ := mem_image.mp (role_present st.inventory _ ht)
    exact ⟨z,hz,ht,fun h => (helper h).elim⟩

end State
end SlidingPuzzle.NestedRouting.TileRoles
