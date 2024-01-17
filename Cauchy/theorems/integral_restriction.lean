import Mathlib.MeasureTheory.Integral.IntervalIntegral

open unitInterval MeasureTheory

namespace theorems

noncomputable def function_extension {a b : ℝ} (f : Set.Icc a b → ℂ) (x : ℝ) : ℂ :=
  by by_cases x ∈ Set.Icc a b; exact f (⟨x, h⟩); exact 0;

theorem integral_restriction {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℂ) : ∫ x in (a)..(b), f x ∂volume =
  ∫ x in (a)..(b), function_extension (Set.restrict (Set.Icc a b) f) x ∂volume := by
  apply intervalIntegral.integral_congr
  unfold function_extension Set.EqOn
  aesop
