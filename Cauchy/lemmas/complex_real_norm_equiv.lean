import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Field.Defs

--Very useful theorem to make Lean behave and not complain
lemma complex_real_norm_equiv (a b : ℝ) : @norm ℂ Complex.instNormedFieldComplex.toNorm (b - a) = ‖b - a‖ := by
    rewrite [Complex.norm_eq_abs, Complex.abs_def]
    simp
    rewrite [Complex.normSq_apply]
    simp
    rw [Real.sqrt_mul_self_eq_abs]
