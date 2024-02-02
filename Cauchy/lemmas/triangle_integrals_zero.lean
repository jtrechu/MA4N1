import Cauchy.definitions.triangle
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic
import Cauchy.lemmas.triangle_inequality
import Cauchy.lemmas.complex_real_norm_equiv
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Data.Set.Intervals.UnorderedInterval
import Mathlib.MeasureTheory.Integral.SetIntegral
import Cauchy.helpers.piecewise_paths
import Cauchy.lemmas.complex_ftc
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Data.Set.Intervals.UnorderedInterval
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Topology.UnitInterval
import Cauchy.definitions.path
import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Init.Set

import Cauchy.lemmas.triangle_convex
import Cauchy.theorems.triangle_interior

open definitions helpers unitInterval lemmas theorems

-- In this file we'll show, by applying the complex FTC, that some basic functions have
-- a zero integral over the triangle

variable {U : Set ℂ} (T : Triangle) (hU : IsCDomain U) (h₂: TriangularBoundary T ⊆ U)

-- We firstly show that a constant has integral 0 over the triangle

lemma const_integral_zero (c : ℂ) : trianglePathIntegral (λ_ => c) T = 0 := by
  rewrite [trianglePathIntegral_apply]
  repeat rewrite [complex_ftc' (F:=λz => c*z) (U:=U)]
  simp
  any_goals
    simp only [ge_iff_le, zero_le_one, not_true, gt_iff_lt]
    apply subset_trans
    apply linear_path_contained T
    try any_goals exact T.contains_a
    try any_goals exact T.contains_b
    try any_goals exact T.contains_c
    exact triangle_interior_contained h₂ hU
  any_goals
    rewrite [Function.funext_iff]
    intro a
    rewrite [deriv_const_mul, deriv_id'']
    simp only [mul_one]
  any_goals
    exact differentiableOn_const c
  any_goals exact hU.1
  any_goals
    apply DifferentiableOn.const_mul
    exact differentiableOn_id
  any_goals exact differentiableAt_id

-- We now show that a constant times the identity has integral 0 over the triangle

lemma const_mul_integral_zero (c : ℂ) : trianglePathIntegral (λz => c*z) T = 0 := by
  rewrite [trianglePathIntegral_apply]
  repeat rewrite [complex_ftc' (F:=λz => c*(1/2)*(z*z)) (U:=U)]
  simp
  any_goals
    simp only [ge_iff_le, zero_le_one, not_true, gt_iff_lt]
    apply subset_trans
    apply linear_path_contained T
    try any_goals exact T.contains_a
    try any_goals exact T.contains_b
    try any_goals exact T.contains_c
    exact triangle_interior_contained h₂ hU
  any_goals
    rewrite [Function.funext_iff]
    intro a
    rewrite [deriv_const_mul, deriv_mul, deriv_id'']
    ring
  any_goals
    apply DifferentiableOn.const_mul
    exact differentiableOn_id
  any_goals exact hU.1
  any_goals
    apply DifferentiableOn.const_mul
    apply DifferentiableOn.mul
    any_goals exact differentiableOn_id
  any_goals
    apply DifferentiableAt.mul
  any_goals exact differentiableAt_id
