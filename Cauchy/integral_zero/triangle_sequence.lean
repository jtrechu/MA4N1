import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.UnitInterval

import Cauchy.definitions.triangle
import Cauchy.definitions.path_integrals
import Cauchy.definitions.domain
import Cauchy.lemmas.mean_leq_max
import Cauchy.definitions.subtriangle
import Cauchy.lemmas.perim_subtriangle_is_half_triangle
import Cauchy.lemmas.subtriangle_subset
import Cauchy.lemmas.integral_on_triangle
import Cauchy.theorems.triangle_compact
import Cauchy.theorems.triangle_interior

open definitions lemmas Classical theorems

variable {U : Set ℂ} (f : ℂ → ℂ) (T : Triangle) (hU : IsCDomain U)
  (h₁ : DifferentiableOn ℂ f U) (h₂: TriangularBoundary T ⊆ U)

def subtriangle_mean_inequality := abs_ge_sum_4
  (trianglePathIntegral f (subTriangleA T)) (trianglePathIntegral f (subTriangleB T))
  (trianglePathIntegral f (subTriangleC T)) (trianglePathIntegral f (subTriangleD T))
  (by symm; apply triangleIntegral' f T h₁ h₂)

noncomputable def selectSubtriangle : SubTriangle T :=
       (Or.by_cases (subtriangle_mean_inequality f T h₁ h₂) (λ_=>subTriangleA T)
  λh => Or.by_cases                  h                      (λ_=>subTriangleB T)
  λh => Or.by_cases                  h                      (λ_=>subTriangleC T)
                                                             λ_=>subTriangleD T)

structure SequenceItem where
  triangle : Triangle
  h₂ : TriangularBoundary triangle ⊆ U

noncomputable def triangleSequence (n : ℕ) : SequenceItem (U:=U) := by
  match n with
  | 0 => exact ⟨T, h₂⟩
  | x + 1 =>
    have ⟨T, ph₂⟩ := triangleSequence x
    refine ⟨SubTriangle.toTriangle $ selectSubtriangle f T h₁ ph₂, ?_⟩
    apply subset_trans boundary_in_set
    apply subset_trans
    apply subtriangle_subset'
    exact triangle_interior_contained ph₂ hU

lemma triangleSequence_apply (n : ℕ) :
   ‖trianglePathIntegral f (triangleSequence f T hU h₁ h₂ n).triangle‖ ≥ ‖trianglePathIntegral f T‖/(4^n) := by
  induction n with
  | zero =>
    unfold triangleSequence
    simp
  | succ n ih =>
    unfold triangleSequence selectSubtriangle
    have id := subtriangle_mean_inequality f (triangleSequence f T hU h₁ h₂ n).triangle
     h₁ (triangleSequence f T hU h₁ h₂ n).h₂
    simp only []
    repeat
      rewrite [Or.by_cases]
      split_ifs with h
      rewrite [ge_iff_le, div_le_iff] at h
      have i := le_trans ih h
      rewrite [←div_le_iff] at i
      rewrite [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
        Real.rpow_add_one, ge_iff_le, div_mul_eq_div_div]
      exact i
      any_goals linarith
      rewrite [or_iff_not_imp_left] at id
      have id := id h
    rewrite [ge_iff_le, div_le_iff] at id
    have i := le_trans ih id
    rewrite [←div_le_iff] at i
    rewrite [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
      Real.rpow_add_one, ge_iff_le, div_mul_eq_div_div]
    exact i
    any_goals linarith

lemma aux (a:ℝ) (n:ℝ) (h: n≥0): (a/2 ^ ↑n) / 2 = a/2^(↑n+1) := by
  field_simp
  rw[mul_comm]
  have h: (2:ℝ)^(1:ℝ) = (2:ℝ) := by simp
  nth_rewrite 2 [←h]
  rw[←Real.rpow_add']
  rw[add_comm]
  simp
  norm_num
  linarith

lemma triangleSequence_perim (n : ℕ) :
  perimeter (triangleSequence f T hU h₁ h₂ n).triangle = perimeter T / 2^n := by
  induction n with
  | zero =>
    unfold triangleSequence
    simp
  | succ n ih =>
    unfold triangleSequence selectSubtriangle
    simp only []
    repeat'
      rewrite [Or.by_cases]
      split_ifs
    all_goals
      try rewrite [perim_subtriangleA_is_half_triangle]
      try rewrite [perim_subtriangleB_is_half_triangle]
      try rewrite [perim_subtriangleC_is_half_triangle]
      try rewrite [perim_subtriangleD_is_half_triangle]
      rw[ih, Nat.succ_eq_add_one ]
      rw[aux (perimeter T)]
      aesop
      exact (Nat.cast_nonneg n)

lemma triangleSequence_common_point :
  ∃z, ∀n, z ∈ (TriangularSet $ (triangleSequence f T hU h₁ h₂ n).triangle) := by
  rewrite [←Set.nonempty_iInter]
  apply IsCompact.nonempty_iInter_of_sequence_nonempty_compact_closed
  . intro i
    conv_lhs => unfold triangleSequence
    simp only [Nat.add_eq, Nat.add_zero]
    apply subtriangle_subset'
  . intro i
    exact (triangleSequence f T hU h₁ h₂ i).triangle.Nonempty
  . exact triangle_compact
  . intro i
    exact IsCompact.isClosed triangle_compact
