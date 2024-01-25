import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Calculus.Dslope
import Mathlib.Data.Complex.Basic
import Cauchy.definitions.triangle
import Cauchy.definitions.path_integrals
import Cauchy.definitions.domain
import Cauchy.helpers.triangle
import Cauchy.lemmas.zero_le_of_gt_zero
import Cauchy.integral_zero._1_triangle_sequence
import Cauchy.integral_zero._4_integral_bound

namespace sorrylemmas

open definitions lemmas helpers.triangle
variable {U : Set ℂ}

theorem cauchy_for_triangles_generalised {T : Triangle} {f : ℂ  → ℂ }
(hU: IsCDomain U) (hT : TriangularBoundary T ⊆ U) (z : ℂ) (hfC : ContinuousOn f U)
(hfD : DifferentiableOn ℂ f (U\{z}) )
: trianglePathIntegral f T = 0 := by sorry
