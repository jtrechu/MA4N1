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
  continuous_deriv_toFun : ContinuousOn (deriv toFun) I

-- copied from Mathlib Path
instance C1Path.continuousMapClass : ContinuousMapClass C1Path ℝ ℂ where
  coe := fun γ ↦ ⇑γ.toContinuousMap
  coe_injective' := fun γ₁ γ₂ h => by
    simp only [FunLike.coe_fn_eq] at h
    cases γ₁; cases γ₂; congr
  map_continuous := fun γ => by continuity

structure PiecewisePath where
  count : ℕ
  paths : Fin count → C1Path

instance : Coe C1Path PiecewisePath where
  coe := λ p => {count := 1, paths := λ 0 => p}

def constructPiecewisePath (array : Array C1Path) : PiecewisePath :=
  PiecewisePath.mk array.size λ i => array[i]

def PiecewisePath.extend (path1 path2 : PiecewisePath) : PiecewisePath :=
  {
    count := path2.count + path1.count
    paths := λ i => by
      by_cases i < path1.count
      . exact path1.paths $ Fin.castLT i h
      . simp only [not_lt] at h
        exact path2.paths $ Fin.subNat path1.count i h
  }
