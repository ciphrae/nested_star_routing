import NestedRouting.Star.Finish

/-! **The middle-node step.** A star router over children that are
regions is itself a region, with budget `baseP + rateP · β`. -/
namespace SlidingPuzzle.NestedRouting.Interface
open Finset TileRoles

variable {n : Nat} [NeZero n] {J : Nat}

namespace StarSpec
variable (P : StarSpec n J)

noncomputable def region : Region n :=
  { P.core P.baseP P.rateP P.Prepared with
    sound := fun hs => hs.sound
    relax := fun hs hβ => hs.relax hβ
    transport := fun hs path same => hs.transport path same
    prepared_local := fun h same => P.prepared_local h same
    init := fun h => P.init h
    substitute := by
      intro _ _ _ _ π hs path sub phys
      exact hs.substitute path sub phys
    request := by
      intro _ _ _ input _ _ hs entry atZ label guard lead
      obtain ⟨rfl,rfl⟩ := entry
      exact P.request hs input atZ label guard lead _ _ _
    finish := by
      intro _ _ _ _ _ hs entry atZ core res
      obtain ⟨rfl,rfl⟩ := entry
      exact P.finish hs atZ core res _ }

end StarSpec
end SlidingPuzzle.NestedRouting.Interface
