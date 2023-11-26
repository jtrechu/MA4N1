import Mathlib.Tactic

namespace helpers.inequalities

lemma gt_nonneg_sum_prod_3 (a A b B c C : ℝ) (ha : a ≥ 0) (hA : A ≥ 0)
  (hb : b ≥ 0) (hB : B ≥ 0) (hc : c ≥ 0) (hC : C ≥ 0) : a*A + b*B + c*C ≥ 0 := by
    repeat apply add_nonneg
    all_goals apply mul_nonneg
    all_goals assumption
