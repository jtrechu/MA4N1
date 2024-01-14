import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.SpecialFunctions.Log.Base

import Cauchy.definitions.triangle
import Cauchy.definitions.path_integrals
import Cauchy.lemmas.mean_leq_max
import Cauchy.definitions.subtriangle
import Cauchy.lemmas.dist_tri_leq_perimeter
import Cauchy.integral_zero.triangle_sequence

open definitions lemmas
lemma triangle_in_ball (t : Triangle) (z : ℂ) (h: z ∈ TriangularSet t):
TriangularSet t ⊆ Metric.closedBall z (perimeter t) := by
intro x xt
exact (dist_tri_leq_perimeter t z x ⟨h,xt⟩ )

lemma subtriangle_in_ball (t: Triangle) (f : ℂ → ℂ) (z : ℂ) (h: ∀ n, z ∈ TriangularSet ( triangleSequence f t n) ) (p:ℝ):
∃n:ℕ , TriangularSet ( triangleSequence f t n) ⊆  Metric.closedBall z p := by sorry
