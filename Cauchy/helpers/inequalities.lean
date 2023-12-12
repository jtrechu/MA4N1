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

lemma bounded_transform_mem_cover {a b : ℝ} (scale : I) (hs : scale ≠ 0) (x : Set.Ioo a b)
  (h : I ⊆ Set.Ioo a b) (offset : ℝ) (ho : 0 ≤ offset) (hub : offset ≤ b * (1 - scale)) :
  scale * (x:ℝ) + offset ∈ Set.Ioo a b := by
  unfold Set.Ioo at *
  simp only [Set.coe_setOf] at x
  have ⟨x, defx⟩ := x
  rewrite [Set.mem_def, Set.setOf_app_iff]
  simp only
  have lb := cover_lb_lt h (by linarith)
  have slb : scale > 0 := by exact Ne.lt_of_le' hs nonneg'
  by_cases x ≥ (0 : ℝ)
  . constructor
    apply lt_of_lt_of_le (b:=scale * x)
    . exact lt_of_lt_of_le lb (mul_nonneg nonneg' h)
    . exact le_add_of_nonneg_right ho
    calc scale * x + offset
      _ < scale * b + offset          := by simp; exact mul_lt_mul_of_pos_left defx.2 slb
      _ ≤ scale * b + b * (1 - scale) := by linarith
      _ = b                           := by ring
  . simp only [ge_iff_le, not_le] at h
    constructor
    . calc scale * x + offset
      _ ≥ scale * x := by linarith
      _ ≥ x         := by exact le_mul_of_le_one_left (le_of_lt h) le_one'
      _ > a         := by exact defx.1
    . calc scale * x + offset
      _ < scale * b + offset          := by simp; exact mul_lt_mul_of_pos_left defx.2 slb
      _ ≤ scale * b + b * (1 - scale) := by linarith
      _ = b                           := by ring

lemma unit_transform_mem_cover {a b : ℝ} (scale : I) (hs : scale ≠ 0)
  (x : Set.Ioo a b) (h : I ⊆ Set.Ioo a b) (offset : I) (hub : offset ≤ (1:ℝ) - scale) :
  scale * (x:ℝ) + offset ∈ Set.Ioo a b := by
  have ub := cover_ub_gt h (by norm_num)
  refine bounded_transform_mem_cover scale hs x h offset nonneg' ?_
  apply le_trans hub
  apply le_mul_of_one_le_left
  exact (Set.Icc.one_sub_nonneg scale)
  exact le_of_lt ub

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
