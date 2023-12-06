import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Topology.MetricSpace.PseudoMetric
import Cauchy.helpers.inequalities

open unitInterval Metric helpers.inequalities

namespace definitions

structure UnitIntervalCover where
  set : Set ℝ
  h : IsOpen set ∧ I ⊆ set

instance : Coe UnitIntervalCover (Set ℝ) where
  coe := UnitIntervalCover.set

def UnitIntervalCover.interval_bounds (uic : UnitIntervalCover) : ∃ interval : Set ℝ, ∃ a b : ℝ,
  I ⊆ Set.Ioo a b ∧ Set.Ioo a b ⊆ uic.set ∧ interval = Set.Ioo a b := by
  have ⟨set, o, ss⟩ := uic
  simp only [ge_iff_le, zero_le_one, not_true, gt_iff_lt, not_lt]
  rewrite [Metric.isOpen_iff] at o
  have ⟨el, gtzl, lball⟩ := o 0 (by apply Set.mem_of_subset_of_mem ss; exact unitInterval.zero_mem)
  have ⟨er, gtzr, rball⟩ := o 1 (by apply Set.mem_of_subset_of_mem ss; exact unitInterval.one_mem)
  have union_int : ball 0 (min el 1) ∪ I ∪ ball 1 (min er 1) = Set.Ioo (-min el 1) (min er 1 + 1) := by
    rewrite [Metric.ball, Metric.ball, Set.Ioo, unitInterval, Set.Icc]
    simp only [Real.dist_eq, abs_lt, add_zero, sub_zero]
    rewrite [Set.union_def]
    simp only [Set.mem_union, Set.mem_setOf_eq]
    conv_lhs => {
      intro a
      arg 1;
      intro a;
      rw [sub_lt_iff_lt_add, lt_sub_iff_add_lt]
      rewrite [union_bound_bound, union_bound_bound']
      rfl
      any_goals tactic => simp; try assumption
      tactic => exact Or.inr (by assumption)
    }
  have lbss := lball; have rbss := rball
  rewrite [Set.subset_def, Metric.ball] at lball rball
  repeat rewrite [Metric.ball] at union_int
  simp only [Set.mem_setOf_eq] at rball
  simp only [dist_zero_right, ge_iff_le, zero_le_one, not_true,
    gt_iff_lt, not_lt] at lball rball
  rewrite [←Set.subset_def] at lball
  refine ⟨Set.Ioo (-min el 1) (min er 1+1), (-min el 1), (min er 1+1), ?_⟩
  rw [←union_int]
  repeat' constructor
  . apply Set.subset_union_of_subset_left
    exact Set.subset_union_right (ball 0 (min el 1)) I
  . apply subset_trans (b:=ball 0 el ∪ I ∪ ball 1 er)
    . repeat apply Set.union_subset_union
      any_goals exact Metric.ball_subset (by simp)
      rfl
    . apply Set.union_subset; apply Set.union_subset
      exacts [lbss, ss, rbss]

def UnitIntervalCover.interval (uic : UnitIntervalCover) : Set ℝ :=
  uic.interval_bounds.choose

def UnitIntervalCover.interval_apply (uic : UnitIntervalCover) :
  ∃ a b : ℝ, uic.interval = Set.Ioo a b ∧ I ⊆ Set.Ioo a b ∧ Set.Ioo a b ⊆ uic.set := by
  have ⟨a, b, gti, lts, ex⟩ := Exists.choose_spec uic.interval_bounds
  refine ⟨a, b, ?_, gti, lts⟩
  unfold interval
  rw [ex]
