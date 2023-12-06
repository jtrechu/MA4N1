import Mathlib.Tactic
import Mathlib.Topology.UnitInterval

open unitInterval

namespace helpers.inequalities

lemma gt_nonneg_sum_prod_3 (a A b B c C : ℝ) (ha : a ≥ 0) (hA : A ≥ 0)
  (hb : b ≥ 0) (hB : B ≥ 0) (hc : c ≥ 0) (hC : C ≥ 0) : a*A + b*B + c*C ≥ 0 := by
    repeat apply add_nonneg
    all_goals apply mul_nonneg
    all_goals assumption

lemma cover_lb_lt {a b c d : ℝ} (h : Set.Icc b c ⊆ Set.Ioo a d) (hh : b ≤ c) : a < b := by
  rewrite [Set.Ioo, Set.subset_def] at h
  have h := h b
  rewrite [Set.left_mem_Icc] at h
  have ⟨h, _⟩ := h hh
  exact h

lemma cover_ub_gt {a b c d : ℝ} (h : Set.Icc b c ⊆ Set.Ioo a d) (hh : b ≤ c) : c < d := by
  rewrite [Set.Ioo, Set.subset_def] at h
  have h := h c
  rewrite [Set.right_mem_Icc] at h
  have ⟨_, h⟩ := h hh
  exact h

lemma unit_mul_mem_cover {a b : ℝ} (x : I) (y : Set.Ioo a b) (h : I ⊆ Set.Ioo a b) :
  x*(y:ℝ) ∈ Set.Ioo a b := by
  unfold Set.Ioo at *
  simp only [Set.coe_setOf] at y
  have ⟨y, defy⟩ := y
  rewrite [Set.mem_def, Set.setOf_app_iff]
  simp only
  have lb := cover_lb_lt h (by linarith)
  have ub := cover_ub_gt h (by linarith)
  by_cases y ≥ (0 : ℝ)
  . constructor
    exact lt_of_lt_of_le lb (mul_nonneg unitInterval.nonneg' h)
    exact lt_of_le_of_lt (mul_le_of_le_one_left h unitInterval.le_one') defy.2
  . simp only [ge_iff_le, not_le] at h
    constructor
    refine lt_of_lt_of_le defy.1 (le_mul_of_le_one_left ?_ unitInterval.le_one')
    apply le_of_lt; exact h;
    apply lt_of_le_of_lt (mul_nonpos_of_nonneg_of_nonpos ?_ ?_)
    . apply lt_trans (by linarith) ub
    . exact unitInterval.nonneg'
    . apply le_of_lt; exact h;

lemma union_bound_bound (a b c d x : ℝ)
  (hbc : c < b) (hbd : b ≤ d) (hac : a < c):
    a < x ∧ x < b ∨ c ≤ x ∧ x ≤ d ↔ a < x ∧ x ≤ d := by
    rewrite [iff_def]
    constructor
    . intro ineq
      cases ineq with
      | inl h =>
        have ⟨ax, xb⟩ := h
        constructor; exact ax; linarith
      | inr h =>
        have ⟨cx, xd⟩ := h
        constructor; linarith; exact xd
    . intro ineq
      have ⟨ax, xd⟩ := ineq
      by_cases x < b
      exact Or.inl ⟨ax, h⟩
      simp only [not_lt] at h
      refine Or.inr (by constructor; all_goals linarith)

lemma union_bound_bound' (a b c d x : ℝ)
  (hbc : c < b) (hbd : b < d) (hac : a < c):
    a < x ∧ x ≤ b ∨ c < x ∧ x < d ↔ a < x ∧ x < d := by
    rewrite [iff_def]
    constructor
    . intro ineq
      cases ineq with
      | inl h =>
        have ⟨ax, xb⟩ := h
        constructor; exact ax; linarith
      | inr h =>
        have ⟨cx, xd⟩ := h
        constructor; linarith; exact xd
    . intro ineq
      have ⟨ax, xd⟩ := ineq
      by_cases x ≤ b
      exact Or.inl ⟨ax, h⟩
      simp only [not_lt] at h
      refine Or.inr (by constructor; all_goals linarith)
