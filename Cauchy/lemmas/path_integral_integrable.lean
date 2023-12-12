import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic

import Cauchy.definitions.path
import Cauchy.definitions.path_integrals
import Cauchy.definitions.domain

open definitions MeasureTheory unitInterval

namespace lemmas

lemma aux_integrable {U : Set ℂ} (f : ℂ → ℂ) (h : DifferentiableOn ℂ f U)
  (γ : C1Path) (hγ : γ '' I ⊆ U):
  IntervalIntegrable (aux f γ) volume 0 1 := by
  unfold aux
  apply IntervalIntegrable.mul_continuousOn
  . apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.comp
    any_goals rewrite [Set.uIcc_of_le zero_le_one]
    exact DifferentiableOn.continuousOn h
    exact γ.continuousOnI
    rw [Set.mapsTo']; exact hγ
  . rewrite [Set.uIcc_of_le zero_le_one]
    exact γ.continuousDerivOnI
