import Cauchy.definitions.triangle
import Cauchy.definitions.domain

namespace theorems

open definitions

theorem triangle_interior_contained {U : Set ℂ} {T : Triangle}
  (h : TriangularBoundary T ⊆ U) (hU : IsCDomain U) : TriangularSet T ⊆ U := by sorry -- unfortunately this is likely too hard!
