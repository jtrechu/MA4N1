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
--open definitions_domain

theorem cauchy_for_triangles {U : Set ℂ } {T : Triangle} {f : ℂ  → ℂ }
(h_UDomain: IsCDomain U) (h_TSubU : TriangularSet T ⊆ U) (h_fAnalytic : DifferentiableOn ℂ f U )
: pathIntegral1 f T.path = 0 := by
sorry
