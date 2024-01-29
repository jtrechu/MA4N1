import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Cauchy.definitions.triangle
import Cauchy.helpers.triangle

open definitions
open helpers.triangle

namespace lemmas

lemma continuous_add_components : Continuous AddComponents := by
  unfold AddComponents
  repeat apply Continuous.add
  . exact continuous_fst
  . apply Continuous.comp
    . exact continuous_fst
    . exact continuous_snd
  . apply Continuous.comp
    repeat' exact continuous_snd


lemma continuous_triangle_point {T : Triangle} : Continuous $ TrianglePoint T := by
  unfold TrianglePoint
  repeat apply Continuous.add
  any_goals apply Continuous.mul
  any_goals exact continuous_const
  all_goals apply Continuous.comp'
  any_goals exact Complex.continuous_ofReal
  exact continuous_fst
  any_goals apply Continuous.comp
  any_goals exact continuous_snd
  any_goals exact continuous_fst
