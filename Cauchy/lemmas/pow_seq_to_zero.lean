-- Average of four numbers

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Cauchy.lemmas.triangle_inequality
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace lemmas

open lemmas

--We will show certain limits that will be useful for the inequalities with triangles

--We show something equivalent to the fact that lim(n→-∞) (a⬝xⁿ) for x>1

lemma pow_zseq_to_zero (a x : ℝ) (hx : x > 1) : ∀ε > 0, ∃(n:ℤ), n ≤ 0 ∧ a*x^n < ε := by
  intro e he
  by_cases a <= 0
  refine ⟨0, ?_⟩
  simp only [Int.cast_zero, Real.rpow_zero, mul_one, true_and]
  linarith
  simp only [not_le] at h
  have hl := tendsto_rpow_atTop_of_base_gt_one x hx
  rewrite [Metric.tendsto_nhds] at hl
  have hh := hl (e/a) (div_pos he h)
  simp at hh
  have ⟨n', hn'⟩ := hh
  have f := Real.exists_floor n'
  have ⟨n, hn⟩ := f
  have lb := hn' (min n 0) ?_
  rewrite [lt_div_iff' h, abs_of_pos] at lb
  refine ⟨min n 0, Int.min_le_right n 0, ?_⟩
  simp only [Int.cast_min, Int.cast_zero]
  exact lb
  apply Real.rpow_pos_of_pos
  linarith
  aesop

--We now show the same but with x in the denominator and positive exponent, which is equivalent

lemma pow_seq_to_zero (a x : ℝ) (hx : x > 1) : ∀ε > 0, ∃n:ℕ, a/x^(n:ℝ) < ε := by
  intro e he
  have h : ∀ε > 0, ∃(n:ℤ), n ≤ 0 ∧ a*x^n < ε := pow_zseq_to_zero a x hx
  have hh := h e he
  have ⟨n', hn'⟩ := hh
  have ⟨n, hn⟩ := Int.exists_eq_neg_ofNat hn'.1
  refine ⟨n, ?_⟩
  rewrite [div_eq_mul_inv, ←Real.rpow_neg]
  convert hn'.2
  aesop
  linarith

end lemmas
