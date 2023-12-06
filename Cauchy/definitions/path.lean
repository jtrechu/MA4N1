import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.ContinuousOn

import Cauchy.definitions.unit_interval_cover
import Cauchy.helpers.inequalities

namespace definitions

open unitInterval Finset DifferentiableOn definitions helpers

structure C1Path extends C(ℝ, ℂ) where
  open_cover : UnitIntervalCover
  differentiable_toFun : DifferentiableOn ℝ toFun open_cover
  continuous_deriv_toFun : ContinuousOn (deriv toFun) open_cover

-- copied from Mathlib Path (No longer true!)
-- instance C1Path.continuousMapClass : ContinuousMapClass C1Path ℝ ℂ where
--   coe := fun γ ↦ ⇑γ.toContinuousMap
--   coe_injective' := fun γ₁ γ₂ h => by
--     simp only [FunLike.coe_fn_eq] at h
--     cases γ₁; cases γ₂; congr
--   map_continuous := fun γ => by continuity


instance : CoeFun (C1Path) fun _ => ℝ → ℂ :=
  ⟨fun p => p.toFun⟩

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

def C1Path.scale (path : C1Path) (scale : I) : C1Path := {

    toFun := λ x => path.toFun $ scale * x

    open_cover := {
      set := path.open_cover.interval
      h := by
        have ⟨a, b, cdef, gti, _⟩ := path.open_cover.interval_apply
        rw [cdef]
        exact ⟨isOpen_Ioo, gti⟩
    }

    differentiable_toFun := by
      have ⟨a, b, cdef, gti, lts⟩ := path.open_cover.interval_apply
      simp; apply DifferentiableOn.comp;
      . exact path.differentiable_toFun
      . apply DifferentiableOn.const_mul; exact differentiableOn_id
      . rw [Set.mapsTo', Set.image, Set.subset_def]
        intro x h; have ⟨ox, oxi, defx⟩ := h
        apply Set.mem_of_subset_of_mem lts
        rw [←defx]
        rw [cdef] at oxi
        exact inequalities.unit_mul_mem_cover scale ⟨ox, oxi⟩ gti


    continuous_deriv_toFun := by
      have ⟨a, b, cdef, gti, lts⟩ := path.open_cover.interval_apply
      simp only [ContinuousMap.toFun_eq_coe]
      rewrite [cdef, continuousOn_iff_continuous_restrict]
      conv => {
        arg 1; intro y;
        apply deriv.scomp
        tactic => {
          apply DifferentiableOn.differentiableAt path.differentiable_toFun
          rewrite [mem_nhds_iff]
          refine ⟨Set.Ioo a b, lts, isOpen_Ioo, ?_⟩
          exact inequalities.unit_mul_mem_cover scale y gti
        }
        tactic => {
          apply Differentiable.differentiableAt;
          apply Differentiable.const_mul;
          exact differentiable_id'
          }
      }
      conv in _ • _ => {
          arg 1;
          rw [deriv_const_mul_field]
      }
      simp only [deriv_id'', mul_one, Complex.real_smul]
      apply Continuous.mul
      exact continuous_const
      rewrite [←Function.comp_def]
      apply ContinuousOn.comp_continuous (s:=Set.Ioo a b)
      . exact ContinuousOn.mono path.continuous_deriv_toFun lts
      . apply Continuous.mul
        exact continuous_const
        exact continuous_subtype_val
      . intro x
        exact inequalities.unit_mul_mem_cover scale x gti
  }

def C1Path.split (path : C1Path) (split : I) : PiecewisePath :=
  constructPiecewisePath #[
    path.scale split,
    path.scale (by
      refine ⟨1-(split:ℝ), ?_⟩
      rw [←mem_iff_one_sub_mem]
      exact Subtype.mem split)
  ]
