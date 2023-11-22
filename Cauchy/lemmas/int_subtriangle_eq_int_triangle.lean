import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Data.Complex.Basic
import Cauchy.definitions.triangle
import Cauchy.definitions.path_integrals
import Cauchy.definitions.domain

open definitions
open definitions_usingPaths
namespace lemmas

--lemma proving: 'We orient the middle triangle by the anti-clockwise direction. Then we have'
-- ∫_∂T^0 f(z) dz = ∑_a,b,c,d  ∫_∂T^0_. f(z) dz
lemma int_subtriangle_eq_int_triangle {U : Set ℂ } {T : Triangle} {f : ℂ  → ℂ }
  (h_UDomain: IsCDomain U) (h_TSubU : TriangularSet T ⊆ U) (h_fAnalytic : AnalyticOn ℂ f U )
  : pathIntegral1 T.a T.a f (path T)
  = pathIntegral1 T.a T.a f (path (subTriangleA T))
  + pathIntegral1 (subTriangleB T).a (subTriangleB T).a f (path (subTriangleB T))
  + pathIntegral1 (subTriangleC T).a (subTriangleC T).a f (path (subTriangleC T))
  + pathIntegral1 (subTriangle T).a (subTriangle T).a f (path (subTriangle T)) := by
  sorry
end lemmas
