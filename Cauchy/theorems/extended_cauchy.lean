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
import Cauchy.lemmas.triangle_linindep_disjoint
import Cauchy.lemmas.eps_subtriangle

import Cauchy.theorems.intermediate_cauchy
import Cauchy.theorems.cauchys_theorem_for_triangles
import Cauchy.theorems.zero_integral_zero

open definitions lemmas theorems unitInterval

-- In this file we prove an extended version of Cauchy's theorem for triangles. Here the condition
-- on differentiability is relaxed, from being differentiable in the Domain, to being differentiable
-- in the domain except for 1 point

theorem extended_cauchy {U : Set ℂ } {T : Triangle} {f : ℂ  → ℂ } {z : ℂ}
  (hz : z ∈ (interior $ TriangularSet T))
  (hU: IsCDomain U) (hT : TriangularBoundary T ⊆ U) (hf : ContinuousOn f U)
  (hf' : DifferentiableOn ℂ f (U \ {z})) : trianglePathIntegral f T = 0 := by

  by_cases ∀u∈(TriangularSet T), f u = 0

  exact zero_integral_zero h

  simp at h
  have ⟨u, hu⟩ := h

  rewrite [←norm_eq_zero]
  apply zero_le_of_gt_zero
  apply norm_nonneg
  intro e he
  have bdd := (Metric.isCompact_iff_isClosed_bounded.1 (
    IsCompact.image_of_continuousOn (triangle_compact (T:=T)) (
      ContinuousOn.mono hf (triangle_interior_contained hT hU)
    )
    )).2

  have ⟨ub, hub⟩ := isBounded_iff_forall_norm_le.1 bdd
  have ubgtz : ub > 0 := by
    refine lt_of_lt_of_le ?_ (hub (f u) ?_)
    rewrite [norm_pos_iff]
    exact hu.2
    apply Set.mem_image_of_mem
    exact hu.1

  have hp : e/ub > 0 := by
    refine div_pos he ubgtz

  have hInt := intermediate_cauchy (T:=T)
    (sT:=eps_subtriangle z hz (e/ub) hp)
    (f:=f) (U:=U\{z})
    ?_ ?_ ?_

  rewrite [hInt]
  rewrite [trianglePathIntegral_apply]
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
  pick_goal 2;
  exact ub * ‖(eps_subtriangle z hz (e/ub) hp).b - (eps_subtriangle z hz (e/ub) hp).a‖
  pick_goal 3;
  exact ub * ‖(eps_subtriangle z hz (e/ub) hp).c - (eps_subtriangle z hz (e/ub) hp).b‖
  pick_goal 4;
  exact ub * ‖(eps_subtriangle z hz (e/ub) hp).a - (eps_subtriangle z hz (e/ub) hp).c‖
  any_goals
    apply mul_le_mul_of_nonneg_right
    apply hub
    apply Set.mem_image_of_mem
    apply Set.mem_of_subset_of_mem
    apply subtriangle_subset' (eps_subtriangle z hz (e/ub) hp)
  apply linear_path_contained (eps_subtriangle z hz (e/ub) hp)
    (eps_subtriangle z hz (e/ub) hp).a (eps_subtriangle z hz (e/ub) hp).b
    (eps_subtriangle z hz (e/ub) hp).contains_a (eps_subtriangle z hz (e/ub) hp).contains_b
  pick_goal 3;
  apply linear_path_contained (eps_subtriangle z hz (e/ub) hp)
    (eps_subtriangle z hz (e/ub) hp).b (eps_subtriangle z hz (e/ub) hp).c
    (eps_subtriangle z hz (e/ub) hp).contains_b (eps_subtriangle z hz (e/ub) hp).contains_c
  pick_goal 5;
  apply linear_path_contained (eps_subtriangle z hz (e/ub) hp)
    (eps_subtriangle z hz (e/ub) hp).c (eps_subtriangle z hz (e/ub) hp).a
    (eps_subtriangle z hz (e/ub) hp).contains_c (eps_subtriangle z hz (e/ub) hp).contains_a
  any_goals
    apply Set.mem_image_of_mem
    exact Set.mem_Icc_of_Ioc hx
  any_goals apply norm_nonneg
  simp only [ sub_zero, abs_one, mul_one]
  repeat rewrite [←mul_add]
  apply le_trans
  apply (mul_le_mul_left ubgtz).2
  apply eps_subtriangle_apply
  rewrite [mul_div_left_comm, div_self, mul_one]
  rfl
  exact ne_of_gt ubgtz
  apply IsOpen.sdiff hU.1
  exact T1Space.t1 z
  unfold TriangleDifference
  apply Set.subset_diff_singleton
  apply Set.union_subset
  rewrite [Set.diff_subset_iff]
  apply Set.subset_union_of_subset_right
  exact triangle_interior_contained hT hU
  apply subset_trans
  apply subset_trans boundary_in_set
  apply subtriangle_subset'
  exact triangle_interior_contained hT hU
  rewrite [Set.mem_union]
  push_neg
  constructor
  rewrite [Set.mem_diff]
  push_neg
  intro _
  apply Set.mem_of_subset_of_mem interior_in_set
  apply eps_subtriange_mem_interior

  have dj := Set.disjoint_right.1 $
    triangle_disjoint_if_linindep (eps_subtriangle z hz (e / ub) hp) ?_
  apply dj
  apply eps_subtriange_mem_interior
  apply eps_subtriangle_linindep
  exact hf'
