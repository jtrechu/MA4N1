import Mathlib.Tactic

noncomputable def test (index : ℕ ) : ℝ := by
  match index with
  | 0 => exact 1
  | n + 1 => exact (test n) / 2

lemma test2 : test 4 = (1/16) := by
  repeat unfold test
  ring

open Classical

lemma test3 (p q r s : Prop) (h : p ∨ q ∨ r ∨ s) : ℕ := by
  apply Or.by_cases h
  exact λp => 1
  exact λq => 1
