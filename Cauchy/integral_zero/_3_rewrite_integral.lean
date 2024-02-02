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
import Cauchy.lemmas.path_integral_linearity

import Cauchy.integral_zero._1_triangle_sequence
import Cauchy.lemmas.triangle_integrals_zero

open definitions lemmas theorems

variable {U : Set ℂ} (f : ℂ → ℂ) (T : Triangle) (hU : IsCDomain U)
  (h₁ : DifferentiableOn ℂ f U) (h₂: TriangularBoundary T ⊆ U)

-- The objective of this file is to show that the path integral won't change by adding a certain
-- polynomial term to it. This is because a polynomial has an antiderivative and so by the
-- fundamental theorem of calculus (also proven) the integral over any closed path is zero.

lemma integral_as_deriv (w : ℂ) :
  ‖trianglePathIntegral f T‖ = ‖trianglePathIntegral (λz => f z - f w - (z - w)*deriv f w) T‖ := by
  apply congrArg
  repeat rewrite [triangleIntegral_subtract hU]
  rewrite [const_integral_zero T hU]
  conv_rhs => {
    arg 2; arg 1; intro z;
    rewrite [sub_mul]; arg 1;
    rewrite [mul_comm];
  }
  rewrite [triangleIntegral_subtract hU]
  rewrite [const_mul_integral_zero T hU]
  rewrite [const_integral_zero T hU]
  ring
  any_goals exact h₂
  any_goals apply DifferentiableOn.const_mul
  any_goals apply differentiableOn_const
  any_goals apply DifferentiableOn.mul_const
  any_goals apply DifferentiableOn.sub_const
  any_goals exact h₁
  all_goals exact differentiableOn_id
