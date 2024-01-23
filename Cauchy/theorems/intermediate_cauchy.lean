import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Data.Complex.Basic
import Cauchy.definitions.triangle
import Cauchy.definitions.subtriangle
import Cauchy.definitions.path_integrals
import Cauchy.definitions.domain
import Cauchy.helpers.triangle

import Cauchy.lemmas.zero_le_of_gt_zero

open definitions

def TriangleDifference (T : Triangle) (sT : SubTriangle T) :=
  (TriangularSet T) \ (TriangularSet sT) ∪ TriangularBoundary sT

theorem intermediate_cauchy {U : Set ℂ} {T : Triangle} {sT : SubTriangle T} {f : ℂ  → ℂ }
(hU : IsOpen U) (hT : TriangleDifference T sT ⊆ U) (hf : DifferentiableOn ℂ f U )
: trianglePathIntegral f T = trianglePathIntegral f sT := by
  sorry
