import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic

import Cauchy.definitions.path_integrals
import Cauchy.definitions.triangle

import Cauchy.integral_zero._1_triangle_sequence

open definitions

variable {U : Set ℂ} (f : ℂ → ℂ) (T : Triangle) (hU : IsCDomain U)
  (h₁ : DifferentiableOn ℂ f U) (h₂: TriangularBoundary T ⊆ U)

lemma integral_as_deriv (w : ℂ)
  (hw : ∀n, w ∈ TriangularSet (triangleSequence f T hU h₁ h₂ n).triangle) :
  ‖trianglePathIntegral f T‖ = ‖trianglePathIntegral (λz => f z - f w - (z - w)*deriv f w) T‖ := by
  sorry
