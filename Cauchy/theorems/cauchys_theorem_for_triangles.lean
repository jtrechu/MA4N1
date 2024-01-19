import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Data.Complex.Basic
import Cauchy.definitions.triangle
import Cauchy.definitions.path_integrals
import Cauchy.definitions.domain
import Cauchy.helpers.triangle

import Cauchy.lemmas.zero_le_of_gt_zero

import Cauchy.integral_zero._1_triangle_sequence
import Cauchy.integral_zero._4_integral_bound

open definitions lemmas helpers.triangle

theorem cauchy_for_triangles {U : Set ℂ } {T : Triangle} {f : ℂ  → ℂ }
(hU: IsCDomain U) (hT : TriangularBoundary T ⊆ U) (hf : DifferentiableOn ℂ f U )
: trianglePathIntegral f T = 0 := by

  by_cases Trivial T
  exact trivial_integral_zero h

  rewrite [←norm_eq_zero]
  apply zero_le_of_gt_zero
  apply norm_nonneg
  intro e he
  have ⟨n, hn⟩ := normed_integral_bound f T hU hf hT (e/(perimeter T)^2) ?_
  have bT := triangleSequence_apply f T hU hf hT n
  rewrite [triangleSequence_perim f T hU hf hT n] at hn
  have ineq := le_trans bT hn
  simp only [Real.rpow_nat_cast, Real.rpow_two, div_pow] at ineq
  rewrite [pow_right_comm] at ineq
  ring_nf at ineq
  rewrite [mul_le_mul_right, inv_pow, mul_rotate, mul_inv_cancel, one_mul] at ineq
  exact ineq
  swap;

  apply pow_pos
  norm_num
  swap;

  apply div_pos he
  rewrite [Real.rpow_two, lt_iff_le_and_ne]
  constructor
  apply sq_nonneg
  symm

  all_goals
  simp only [ne_eq, zero_lt_two, pow_eq_zero_iff]
  exact (not_iff_not.2 (perim_zero_iff_trivial T)).2 h
