import Cauchy.definitions.triangle
import Cauchy.definitions.domain

namespace theorems

open definitions

-- This is the only sorryed lemma in the main result. It follows from the fact that the triangle in
-- convex (which we have shown), however there is insufficient infrastructure in Mathlib to be able to prove this
-- as far as we know

theorem triangle_interior_contained {U : Set ℂ} {T : Triangle}
  (h : TriangularBoundary T ⊆ U) (hU : IsCDomain U) : TriangularSet T ⊆ U := by sorry
