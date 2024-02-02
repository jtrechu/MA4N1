import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor


import Cauchy.definitions.triangle
import Cauchy.definitions.path_integrals
import Cauchy.lemmas.mean_leq_max
import Cauchy.definitions.subtriangle
import Cauchy.lemmas.dist_tri_leq_perimeter
import Cauchy.integral_zero.triangle_sequence
import Cauchy.helpers.triangle

open definitions lemmas helpers.triangle

-- This was the first attempt at showing we can get a triangle as small as we want it to be.

-- It was done by giving an specific radius for the ball that contained the triangle

lemma triangle_in_ball (t : Triangle) (z : ℂ) (h: z ∈ TriangularSet t):
TriangularSet t ⊆ Metric.closedBall z (perimeter t) := by
intro x xt
exact (dist_tri_leq_perimeter t z x ⟨h,xt⟩ )

theorem power_monotone_of_nonneg (a b : ℝ) (c : ℝ) (h₁ : a ≤ b) (h₂ : 0 ≤ c) :
  c^a ≤ c^b := by
  sorry
lemma perimeterPositive (t:Triangle) (h : nonTrivial t) : 0 < perimeter t := by
unfold perimeter
have j : t.b ≠ t.a := by
  unfold nonTrivial at h
  unfold Trivial at h
  simp_all only [ne_eq]
  apply Aesop.BuiltinRules.not_intro
  intro a
  simp_all only [sub_self, mul_zero, add_zero, exists_const, true_or, not_true]
rw[←dist_pos]  at j
have k : dist t.b t.a ≤ dist t.b t.a + dist t.c t.b + dist t.a t.c := by
  have k₁ : 0≤ dist t.c t.b := by exact dist_nonneg
  have k₂ : 0≤ dist t.a t.c := by exact dist_nonneg
  linarith
linarith

lemma subtriangle_in_ball (t: Triangle) (ht: nonTrivial t) (f : ℂ → ℂ) (z : ℂ) (hn: ∀ n, z ∈ TriangularSet ( triangleSequence f t n) ) (p:ℝ) (hp : 0 < p):
∃n:ℕ , TriangularSet ( triangleSequence f t n) ⊆  Metric.closedBall z p := by
use   ⌈Real.logb 2 (perimeter t/p)⌉₊
intro a b
have key : perimeter ( triangleSequence f t  ⌈Real.logb 2 (perimeter t/p)⌉₊) ≤ p := by
  rw[triangleSequence_perim]
  have triv : 0≤(2:ℝ) :=by norm_num
  have h:  Real.logb 2 (perimeter t/p) ≤  ⌈Real.logb 2 (perimeter t/p)⌉₊ := by exact Nat.le_ceil ( Real.logb 2 (perimeter t/p))
  have h1: 2 ^ Real.logb 2 (perimeter t / p) ≤ 2 ^ ⌈Real.logb 2 (perimeter t / p)⌉₊ := by
   exact power_monotone_of_nonneg (Real.logb 2 (perimeter t / p)) (↑⌈Real.logb 2 (perimeter t / p)⌉₊) 2 h triv
  have h3:  perimeter t / 2 ^ ↑⌈Real.logb 2 (perimeter t / p)⌉₊ ≤ perimeter t /  2 ^ Real.logb 2 (perimeter t / p) := by
    sorry

  have h4: (2:ℝ)  ^ Real.logb 2 (perimeter t / p) = perimeter t /p := by
      rw[Real.rpow_logb]
      norm_num
      norm_num
      ring_nf
      have h5 : 0 < p⁻¹:= by
        rw[←(inv_pos)] at hp
        exact hp
      have h5 : 0 < perimeter t := by exact (perimeterPositive t ht)
      nlinarith
  rw[h4] at h3
  have h7: perimeter t / (perimeter t / p) = p := by
    ring_nf
    rw[mul_comm]
    ring_nf
    have h9: perimeter t ≠ 0 := by
      have h10: 0 < perimeter t := by exact (perimeterPositive t ht)
      apply ne_of_gt at h10
      exact h10
    have h8 : (perimeter t)⁻¹ * perimeter t = 1 := by
      exact (inv_mul_cancel h9 )
    aesop
  rw[h7] at h3
  exact h3


have h11 : z ∈ TriangularSet (triangleSequence f t  ⌈Real.logb 2 (perimeter t/p)⌉₊) := by exact hn ⌈Real.logb 2 (perimeter t/p)⌉₊

have h12 :  dist a z ≤ perimeter (triangleSequence f t ⌈Real.logb 2 (perimeter t / p)⌉₊) := by
    exact (dist_tri_leq_perimeter (triangleSequence f t  ⌈Real.logb 2 (perimeter t/p)⌉₊) z a ⟨h11,b⟩ )
have h12 : dist a z ≤ p := by exact (LE.le.trans h12 key)
exact h12
