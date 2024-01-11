-- Average of four numbers

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Cauchy.lemmas.triangle_inequality

namespace lemmas

open lemmas

lemma abs_ge_sum_4 (a b c d sum : ℂ) : a+b+c+d = sum → ‖a‖ ≥ ‖sum‖/4 ∨ ‖b‖ ≥ ‖sum‖/4
  ∨ ‖c‖ ≥ ‖sum‖/4 ∨ ‖d‖ ≥ ‖sum‖/4:= by
  contrapose
  repeat rewrite [not_or]
  repeat rewrite [←lt_iff_not_ge]
  intro i s
  apply_fun norm at s
  have t : ‖a+b+c+d‖ ≤ ‖a‖+‖b‖+‖c‖+‖d‖ := by
    repeat apply le_trans (by apply triangle_inequality); rw [add_le_add_iff_right]
  linarith

lemma mean_leq_max (a b c d : ℝ) : a+b+c+d ≤ 4*max a (max b (max c d)) := by
have h1 : a ≤ max a (max b (max c d)) := by apply le_max_left
have h2 : b ≤ max a (max b (max c d)) :=
  by
    rw[max_left_comm]
    apply le_max_left
have h3: c ≤ max a (max b (max c d)) :=
  by
    rw[max_left_comm b c, max_left_comm]
    apply le_max_left
have h4: d ≤ max a (max b (max c d)):=
  by
    rw[max_comm c d, max_left_comm b d, max_left_comm]
    apply le_max_left
linarith

end lemmas
