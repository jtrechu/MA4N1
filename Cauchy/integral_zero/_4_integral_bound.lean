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
import Cauchy.definitions.linear_path
import Cauchy.lemmas.path_integral_linearity

import Cauchy.integral_zero._1_triangle_sequence
import Cauchy.integral_zero._2_exists_delta_subtriangle
import Cauchy.integral_zero._3_rewrite_integral
import Cauchy.lemmas.triangle_integrals_zero
import Cauchy.lemmas.deriv_epsilon_delta
import Cauchy.lemmas.dist_tri_leq_perimeter
import Cauchy.lemmas.triangle_convex

import Cauchy.theorems.triangle_interior

open definitions lemmas theorems unitInterval

variable {U : Set ℂ} (f : ℂ → ℂ) (T : Triangle) (hU : IsCDomain U)
  (h₁ : DifferentiableOn ℂ f U) (h₂: TriangularBoundary T ⊆ U)

lemma normed_integral_bound : ∀ε>0, ∃n:ℕ,
  ‖trianglePathIntegral f (triangleSequence f T hU h₁ h₂ n).triangle‖ ≤
  ε*(perimeter (triangleSequence f T hU h₁ h₂ n).triangle)^2 := by
  intro e he

  have ⟨w, hw⟩ := triangleSequence_common_point f T hU h₁ h₂
  have ⟨d, hd⟩ := deriv_epsilon_delta (z:=w) (f:=f) ?_ e (by linarith)
  have ⟨n, hn⟩ := exists_subtriangle_delta f T hU h₁ h₂ w hw d (by linarith)
  refine ⟨n, ?_⟩
  rewrite [integral_as_deriv f (triangleSequence f T hU h₁ h₂ n).triangle
           hU h₁ ?_ w,
           trianglePathIntegral_apply]
  unfold pathIntegral1'
  unfold definitions.aux
  apply le_trans
  apply norm_add₃_le
  apply le_trans
  apply add_le_add_three
  any_goals
    simp only [Pi.mul_apply, Function.comp_apply]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    simp at hx
    simp only [norm_mul]
    rewrite [deriv_linear_path]

  swap; -- For side AB
  exact e * (perimeter (triangleSequence f T hU h₁ h₂ n).triangle) *
    ‖(triangleSequence f T hU h₁ h₂ n).triangle.b -
     (triangleSequence f T hU h₁ h₂ n).triangle.a‖
  apply mul_le_mul_of_nonneg_right ?_ ?_
  apply le_trans $ hd.2 ((1 - ↑x) * (triangleSequence f T hU h₁ h₂ n).triangle.a +
                            ↑x    * (triangleSequence f T hU h₁ h₂ n).triangle.b) ?_
  rewrite [mul_le_mul_left]
  apply dist_tri_leq_perimeter
  refine ⟨hw n, ?_⟩
  pick_goal 3;
  apply hn
  any_goals
    apply linear_path_contained (triangleSequence f T hU h₁ h₂ n).triangle
                                (triangleSequence f T hU h₁ h₂ n).triangle.a
                                (triangleSequence f T hU h₁ h₂ n).triangle.b
    exact (triangleSequence f T hU h₁ h₂ n).triangle.contains_a
    exact (triangleSequence f T hU h₁ h₂ n).triangle.contains_b
    apply Set.mem_image_of_mem
    exact Set.mem_Icc_of_Ioc hx
  linarith
  apply norm_nonneg

  swap; -- For side BC
  exact e * (perimeter (triangleSequence f T hU h₁ h₂ n).triangle) *
    ‖(triangleSequence f T hU h₁ h₂ n).triangle.c -
     (triangleSequence f T hU h₁ h₂ n).triangle.b‖
  apply mul_le_mul_of_nonneg_right ?_ ?_
  apply le_trans $ hd.2 ((1 - ↑x) * (triangleSequence f T hU h₁ h₂ n).triangle.b +
                            ↑x    * (triangleSequence f T hU h₁ h₂ n).triangle.c) ?_
  rewrite [mul_le_mul_left]
  apply dist_tri_leq_perimeter
  refine ⟨hw n, ?_⟩
  pick_goal 3;
  apply hn
  any_goals
    apply linear_path_contained (triangleSequence f T hU h₁ h₂ n).triangle
                                (triangleSequence f T hU h₁ h₂ n).triangle.b
                                (triangleSequence f T hU h₁ h₂ n).triangle.c
    exact (triangleSequence f T hU h₁ h₂ n).triangle.contains_b
    exact (triangleSequence f T hU h₁ h₂ n).triangle.contains_c
    apply Set.mem_image_of_mem
    exact Set.mem_Icc_of_Ioc hx
  linarith
  apply norm_nonneg

  swap; -- For side CA
  exact e * (perimeter (triangleSequence f T hU h₁ h₂ n).triangle) *
    ‖(triangleSequence f T hU h₁ h₂ n).triangle.a -
     (triangleSequence f T hU h₁ h₂ n).triangle.c‖
  apply mul_le_mul_of_nonneg_right ?_ ?_
  apply le_trans $ hd.2 ((1 - ↑x) * (triangleSequence f T hU h₁ h₂ n).triangle.c +
                            ↑x    * (triangleSequence f T hU h₁ h₂ n).triangle.a) ?_
  rewrite [mul_le_mul_left]
  apply dist_tri_leq_perimeter
  refine ⟨hw n, ?_⟩
  pick_goal 3;
  apply hn
  any_goals
    apply linear_path_contained (triangleSequence f T hU h₁ h₂ n).triangle
                                (triangleSequence f T hU h₁ h₂ n).triangle.c
                                (triangleSequence f T hU h₁ h₂ n).triangle.a
    exact (triangleSequence f T hU h₁ h₂ n).triangle.contains_c
    exact (triangleSequence f T hU h₁ h₂ n).triangle.contains_a
    apply Set.mem_image_of_mem
    exact Set.mem_Icc_of_Ioc hx
  linarith
  apply norm_nonneg

  . simp only [sub_zero, abs_one, mul_one, Real.rpow_two]
    repeat rewrite [←left_distrib]
    rewrite [sq, ←mul_assoc]
    unfold perimeter
    repeat rewrite [dist_eq_norm]
    rfl

  exact (triangleSequence f T hU h₁ h₂ n).h₂

  apply DifferentiableOn.differentiableAt h₁
  rewrite [mem_nhds_iff]
  refine ⟨U, by rfl, hU.1, ?_⟩
  apply Set.mem_of_subset_of_mem ?_ (hw 0)
  exact triangle_interior_contained (triangleSequence f T hU h₁ h₂ 0).h₂ hU
