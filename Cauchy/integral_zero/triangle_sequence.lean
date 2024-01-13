import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.UnitInterval

import Cauchy.definitions.triangle
import Cauchy.definitions.path_integrals
import Cauchy.lemmas.mean_leq_max
import Cauchy.definitions.subtriangle

open definitions lemmas Classical

def subtriangle_mean_inequality (f : ℂ → ℂ) (T : Triangle) := abs_ge_sum_4
  (trianglePathIntegral f (subTriangleA T)) (trianglePathIntegral f (subTriangleB T))
  (trianglePathIntegral f (subTriangleC T)) (trianglePathIntegral f (subTriangleD T))
  (sum:=trianglePathIntegral f T) (by sorry)

noncomputable def selectSubtriangle (f : ℂ → ℂ) (T : Triangle) : SubTriangle T :=
       (Or.by_cases (subtriangle_mean_inequality f T) (λ_=>subTriangleA T)
  λh => Or.by_cases               h                   (λ_=>subTriangleB T)
  λh => Or.by_cases               h                   (λ_=>subTriangleC T)
                                                       λ_=>subTriangleD T)

noncomputable def triangleSequence (f : ℂ → ℂ) (T : Triangle) (n : ℕ) : Triangle := by
  match n with
  | 0 => exact T
  | x + 1 => exact SubTriangle.toTriangle $ selectSubtriangle f (triangleSequence f T x)

lemma triangleSequence_apply {f : ℂ → ℂ} {T : Triangle} (n : ℕ) :
   ‖trianglePathIntegral f (triangleSequence f T n)‖ ≥ ‖trianglePathIntegral f T‖/(4^n) := by
  induction n with
  | zero =>
    unfold triangleSequence
    simp
  | succ n ih =>
    unfold triangleSequence selectSubtriangle
    have id := subtriangle_mean_inequality f (triangleSequence f T n)
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
