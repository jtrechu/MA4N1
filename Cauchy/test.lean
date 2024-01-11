import Mathlib.Tactic

noncomputable def test (index : ℕ ) : ℝ := by
  match index with
  | 0 => exact 1
  | n + 1 => exact (test n) / 2

lemma test2 : test 4 = (1/16) := by
  repeat unfold test
  ring
