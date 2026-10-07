import NestedRouting.Final

/-! Audit of the nested-routing God's-number bound. -/
open SlidingPuzzle SlidingPuzzle.NestedRouting.Central

#check @SlidingPuzzle.NestedRouting.Central.pair_bound
#print axioms SlidingPuzzle.NestedRouting.Central.pair_bound
#print axioms SlidingPuzzle.NestedRouting.Central.canonical

-- The statement, restated with the repository's own definitions.
example : ∀ (n : Nat) [NeZero n], 256≤n → ∀ B T : Board n, Nonempty (Path B T) →
    ∃ path : Path B T, (path.length : ℝ)≤n^3+4161*n^2*Real.log n-12148*n^2 := pair_bound
