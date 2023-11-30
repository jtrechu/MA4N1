import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Finset.Basic

namespace definitions

open unitInterval Finset

structure C1Path extends C(ℝ, ℂ) where
  differentiable_toFun : DifferentiableOn ℝ toFun I

-- copied from Mathlib Path
instance C1Path.continuousMapClass : ContinuousMapClass C1Path ℝ ℂ where
  coe := fun γ ↦ ⇑γ.toContinuousMap
  coe_injective' := fun γ₁ γ₂ h => by
    simp only [FunLike.coe_fn_eq] at h
    cases γ₁; cases γ₂; congr
  map_continuous := fun γ => by continuity

structure PiecewisePath where
  count : ℕ
  paths : range count → C1Path
