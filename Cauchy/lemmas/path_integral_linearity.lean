import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Cauchy.definitions.path_integrals
import Cauchy.definitions.triangle

import Cauchy.lemmas.triangle_convex
import Cauchy.lemmas.path_integral_integrable
import Cauchy.theorems.triangle_interior

open definitions intervalIntegral MeasureTheory unitInterval lemmas theorems

namespace lemmas

-- Here we show that the Path Integral is additive over the function:
-- ∫_γ f + ∫_γ g = ∫_γ (f + g)

lemma pathIntegral_additive {U : Set ℂ} (f g : ℂ → ℂ) (γ : C1Path)
  (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) (hγ : γ '' I ⊆ U) :
  pathIntegral1' (λz => f z+g z) γ = pathIntegral1' f γ + pathIntegral1' g γ := by
  unfold pathIntegral1' aux
  rw[← intervalIntegral.integral_add]
  apply intervalIntegral.integral_congr
  intro x _
  simp only [Pi.mul_apply, Function.comp_apply, Pi.add_apply]
  rewrite[add_mul]
  aesop
  exact aux_integrable f hf γ hγ
  exact aux_integrable g hg γ hγ

-- We now apply this result to triangleIntegrals (which is just a particular case of pathIntegrals)

lemma triangleIntegral_additive {U : Set ℂ} (hU : IsCDomain U) (T : Triangle) (hT : TriangularBoundary T ⊆ U)
  (f g : ℂ → ℂ) (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) :
  trianglePathIntegral (λz => f z+g z) T = trianglePathIntegral f T + trianglePathIntegral g T := by
  repeat rewrite [trianglePathIntegral_apply]
  repeat rewrite [pathIntegral_additive (U:=U) f g]
  ring
  any_goals exact hf
  any_goals exact hg
  all_goals
    simp only [ge_iff_le, zero_le_one, not_true, gt_iff_lt]
    apply subset_trans
    apply linear_path_contained T
    try any_goals exact T.contains_a
    try any_goals exact T.contains_b
    try any_goals exact T.contains_c
    exact triangle_interior_contained hT hU

--We now show that just like with regular integrals multiplying constants can
--be taken out of the integral for a ∈ ℂ we have ∫ₐ(c⬝f) = c⬝∫ₐf

lemma pathIntegral_scalar (c : ℂ) (f : ℂ → ℂ) (γ : C1Path) :
  pathIntegral1' (λz => c*f z) γ = c * pathIntegral1' f γ := by
  unfold pathIntegral1' aux
  simp only [Pi.mul_apply, Function.comp_apply]
  conv => {
    arg 1; arg 1; intro t;
    rewrite [mul_rotate]
  }
  rewrite [intervalIntegral.integral_mul_const]
  ring

--We now apply this result to triangleIntegrals

lemma triangleIntegral_scalar (T : Triangle) (c : ℂ) (f : ℂ → ℂ) :
  trianglePathIntegral (λz => c*f z) T = c * trianglePathIntegral f T := by
  repeat rewrite [trianglePathIntegral_apply]
  repeat rewrite [pathIntegral_scalar c f]
  ring

-- Here we show that the Path Integral works well with substraction:
-- ∫_γ f - ∫_γ g = ∫_γ (f - g)

lemma pathIntegral_subtract {U : Set ℂ} (f g : ℂ → ℂ) (γ : C1Path)
  (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) (hγ : γ '' I ⊆ U) :
  pathIntegral1' (λz => f z-g z) γ = pathIntegral1' f γ - pathIntegral1' g γ := by
  unfold pathIntegral1' aux
  rw[←intervalIntegral.integral_sub]
  apply intervalIntegral.integral_congr
  intro x _
  simp only [Pi.mul_apply, Function.comp_apply, Pi.sub_apply]
  rewrite[sub_mul]
  aesop
  exact aux_integrable f hf γ hγ
  exact aux_integrable g hg γ hγ

--We now apply this result to triangleIntegrals

lemma triangleIntegral_subtract {U : Set ℂ} (hU : IsCDomain U) (T : Triangle) (hT : TriangularBoundary T ⊆ U)
  (f g : ℂ → ℂ) (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) :
  trianglePathIntegral (λz => f z-g z) T = trianglePathIntegral f T - trianglePathIntegral g T := by
  repeat rewrite [trianglePathIntegral_apply]
  repeat rewrite [pathIntegral_subtract (U:=U) f g]
  ring
  any_goals exact hf
  any_goals exact hg
  all_goals
    simp only [ge_iff_le, zero_le_one, not_true, gt_iff_lt]
    apply subset_trans
    apply linear_path_contained T
    try any_goals exact T.contains_a
    try any_goals exact T.contains_b
    try any_goals exact T.contains_c
    exact triangle_interior_contained hT hU
