import Mathlib.Data.Complex.Basic
import Mathlib.Tactic


namespace lemmas

-- In this file we prove the classic theorem know as the triangle inequality

lemma triangle_inequality {a b : ℂ} : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := by
  have triangle := Complex.instNormedFieldComplex.dist_triangle a 0 (-b)
  repeat rewrite [Complex.dist_eq] at triangle
  simp at triangle
  exact triangle
