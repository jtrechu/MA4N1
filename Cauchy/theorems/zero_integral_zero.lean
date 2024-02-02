import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Data.Complex.Basic
import Cauchy.definitions.triangle
import Cauchy.definitions.path_integrals
import Cauchy.definitions.domain
import Cauchy.definitions.eps_subtriangle
import Cauchy.helpers.triangle
import Cauchy.theorems.integral_restriction
import Cauchy.lemmas.triangle_convex
import Cauchy.theorems.triangle_interior

open definitions lemmas unitInterval theorems

--In this file we'll show that if a function is 0 at all points of the
--Triangular set then the pathIntegral over the triangle is 0

theorem zero_integral_zero {T : Triangle} {f : ℂ  → ℂ}
  (hf : ∀u∈(TriangularSet T), f u = 0) : trianglePathIntegral f T = 0 := by

  rewrite [trianglePathIntegral_apply]
  unfold pathIntegral1' definitions.aux
  simp only [Pi.mul_apply, Function.comp_apply]
  conv_lhs => {
    arg 1; arg 1; rewrite [integral_restriction]; arg 1; intro t; arg 1; intro t;
    simp; rewrite [hf ((1 - ↑↑t) * T.a + ↑↑t * T.b)];
    rfl
    tactic => {
      apply Set.mem_of_subset_of_mem
      apply linear_path_contained T T.a T.b T.contains_a T.contains_b
      apply Set.mem_image_of_mem
      exact t.2
    }
    tactic => norm_num
  }

  conv_lhs => {
    arg 1; arg 2;  rewrite [integral_restriction]; arg 1; intro t; arg 1;
    intro t; simp; rewrite [hf ((1 - ↑↑t) * T.b + ↑↑t * T.c)];
    rfl
    tactic => {
      apply Set.mem_of_subset_of_mem
      apply linear_path_contained T T.b T.c T.contains_b T.contains_c
      apply Set.mem_image_of_mem
      exact t.2
    }
    tactic => norm_num
  }

  conv_lhs => {
    arg 2; rewrite [integral_restriction]; arg 1; intro t; arg 1;
    intro t; simp; rewrite [hf ((1 - ↑↑t) * T.c + ↑↑t * T.a)];
    rfl
    tactic => {
      apply Set.mem_of_subset_of_mem
      apply linear_path_contained T T.c T.a T.contains_c T.contains_a
      apply Set.mem_image_of_mem
      exact t.2
    }
    tactic => norm_num
  }

  simp only [zero_mul]
  have : ∫ (t : ℝ) in (0)..(1), function_extension (fun (_:I) => 0) t =
         ∫ (t : ℝ) in (0)..(1), (λ_ => 0) t := by
    unfold function_extension
    aesop
  simp only [this, intervalIntegral.integral_zero, add_zero]
