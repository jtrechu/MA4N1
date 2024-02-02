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

--This file deals with the creation of the sequence of triangles used in the proof.
-- Given a Triangle Tₙ we want Tₙ₊₁ which we define to be the triangle with the biggest norm of
-- the path integral out of the 4 subtriangles of Tₙ


variable {U : Set ℂ} (f : ℂ → ℂ) (T : Triangle) (hU : IsCDomain U)
  (h₁ : DifferentiableOn ℂ f U) (h₂: TriangularBoundary T ⊆ U)

-- The point of using this sequence is that we can apply the fact that a+b+c+d ≤ 4max(a,b,c,d).
-- Which is the following inequality:

def subtriangle_mean_inequality := abs_ge_sum_4
  (trianglePathIntegral f (subTriangleA T)) (trianglePathIntegral f (subTriangleB T))
  (trianglePathIntegral f (subTriangleC T)) (trianglePathIntegral f (subTriangleD T))
  (by symm; apply triangleIntegral' f T h₁ h₂)

-- The following definition picks a triangle out of the four subtriangles
-- it'll pick one for which it holds that the patch integral is
-- bigger than 1/4 of the path integral in the triangle

noncomputable def selectSubtriangle : SubTriangle T :=
       (Or.by_cases (subtriangle_mean_inequality f T h₁ h₂) (λ_=>subTriangleA T)
  λh => Or.by_cases                  h                      (λ_=>subTriangleB T)
  λh => Or.by_cases                  h                      (λ_=>subTriangleC T)
                                                             λ_=>subTriangleD T)

-- Now that we can repeat this process as much as we want, we define
-- the sequence in which the (n+1)th term is the result of applying
-- selectSubtriangle to the nth term

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

--Now we apply the norm in our sequence to get that the integral over the n-th triangle is bigger
--than 4⁻ⁿ times the integral over the original triangle:

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

--We now do something similar but with the perimeter, showing that the perimeter of the nth triangle
--of the sequence is 2⁻ⁿ times the perimeter of the original triangle, first we prove a trivial
-- result needed for the proof

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

--Lastly we show that given the sequence of triangles there is a point z that is common to all the
--triangles of the sequence, this is ∃z ∈ ⋂ᵢⁿ(Tᵢ) ∀n

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
