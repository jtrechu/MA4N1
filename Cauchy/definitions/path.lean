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
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.ContinuousOn

import Cauchy.definitions.unit_interval_cover
import Cauchy.helpers.inequalities

namespace definitions

open unitInterval Finset DifferentiableOn definitions helpers

-- After dealing with different structures, we ended up creating a new structure, C1Path, with convenient properties for the future proofs

structure C1Path where
  toFun : ℝ → ℂ
  open_cover : UnitIntervalCover
  differentiable_toFun : DifferentiableOn ℝ toFun open_cover
  continuous_deriv_toFun : ContinuousOn (deriv toFun) open_cover

instance : CoeFun (C1Path) fun _ => ℝ → ℂ :=
  ⟨fun p => p.toFun⟩

structure PiecewisePath (count : ℕ) where
  paths : Fin count → C1Path

instance : Coe C1Path (PiecewisePath 1) where
  coe := λ p => {paths := λ 0 => p}

def PiecewisePath.extend {n m : ℕ} (p : PiecewisePath n) (q : PiecewisePath m) : PiecewisePath (n + m) :=
  {
    paths := λ i => by
      by_cases i < n
      . exact p.paths $ Fin.castLT i h
      . simp only [not_lt] at h
        refine q.paths $ Fin.subNat n ⟨i, ?_⟩ h
        rewrite [add_comm m n]; exact Fin.prop i
  }

-- These properties are extremely useful 
lemma C1Path.differentiableOnI (path : C1Path) : DifferentiableOn ℝ path I := by
  have ⟨a, _, gti, lts⟩ := path.open_cover.interval_apply
  apply DifferentiableOn.mono path.differentiable_toFun
  exact subset_trans gti lts

lemma C1Path.continuousOnI (path : C1Path) : ContinuousOn path I := by
  exact DifferentiableOn.continuousOn path.differentiableOnI

lemma C1Path.continuousDerivOnI (path : C1Path) : ContinuousOn (deriv path) I := by
  have ⟨a, _, gti, lts⟩ := path.open_cover.interval_apply
  apply ContinuousOn.mono path.continuous_deriv_toFun
  exact subset_trans gti lts

def C1Path.transform (path : C1Path) (scale : I) (offset : I) (ho : offset ≤ (1:ℝ) - scale)
  (hs : scale ≠ 0) : C1Path := {

    toFun := λ x => path.toFun $ scale * x + offset

    open_cover := {
      set := path.open_cover.interval
      h := by
        have ⟨a, cdef, gti, _⟩ := path.open_cover.interval_apply
        rw [cdef]
        exact ⟨isOpen_Ioo, gti⟩
    }

    differentiable_toFun := by
      have ⟨a, cdef, gti, lts⟩ := path.open_cover.interval_apply
      simp; apply DifferentiableOn.comp
      exact path.differentiable_toFun
      apply DifferentiableOn.add_const
      apply DifferentiableOn.const_mul; exact differentiableOn_id
      rw [Set.mapsTo', Set.image, Set.subset_def]
      intro x h; have ⟨ox, oxi, defx⟩ := h
      apply Set.mem_of_subset_of_mem lts
      rw [←defx]
      rw [cdef] at oxi
      exact inequalities.unit_transform_mem_cover scale hs ⟨ox, oxi⟩ gti offset ho

    continuous_deriv_toFun := by
      have ⟨a, cdef, gti, lts⟩ := path.open_cover.interval_apply
      simp only [ContinuousMap.toFun_eq_coe]
      rewrite [cdef, continuousOn_iff_continuous_restrict]
      conv => {
        arg 1; intro y
        apply deriv.scomp
        tactic => {
          apply DifferentiableOn.differentiableAt path.differentiable_toFun
          rewrite [mem_nhds_iff]
          refine ⟨Set.Ioo (-a) (a+1), lts, isOpen_Ioo, ?_⟩
          exact inequalities.unit_transform_mem_cover scale hs y gti offset ho
        }
        tactic => {
          apply Differentiable.differentiableAt
          apply Differentiable.add
          apply Differentiable.const_mul
          exact differentiable_id'
          apply differentiable_const
          }
      }
      conv in _ • _ => {
          arg 1;
          rw [deriv_add_const, deriv_const_mul_field]
          simp only [deriv_id'', mul_one, Complex.real_smul]
      }
      apply Continuous.mul
      exact continuous_const
      rewrite [←Function.comp_def]
      apply ContinuousOn.comp_continuous (s:=Set.Ioo (-a) (a+1))
      exact ContinuousOn.mono path.continuous_deriv_toFun lts
      any_goals continuity
      intro x
      exact inequalities.unit_transform_mem_cover scale hs x gti offset ho
  }

def C1Path.reverse (path : C1Path) : C1Path := {
  toFun := λ x => path.toFun (1 - x)

  open_cover := {
      set := path.open_cover.interval
      h := by
        have ⟨a, cdef, gti, _⟩ := path.open_cover.interval_apply
        rw [cdef]
        exact ⟨isOpen_Ioo, gti⟩
    }

  differentiable_toFun := by
      have ⟨a, cdef, gti, lts⟩ := path.open_cover.interval_apply
      simp; apply DifferentiableOn.comp
      exact path.differentiable_toFun
      apply DifferentiableOn.const_add
      apply DifferentiableOn.neg; exact differentiableOn_id
      rw [Set.mapsTo', Set.image, Set.subset_def]
      intro x h; have ⟨ox, oxi, defx⟩ := h
      apply Set.mem_of_subset_of_mem lts
      rw [←defx]
      rw [cdef] at oxi
      simp only [Set.mem_Ioo] at oxi
      simp only [Set.mem_Ioo]
      constructor
      all_goals linarith

  continuous_deriv_toFun := by
      have ⟨a, cdef, gti, lts⟩ := path.open_cover.interval_apply
      simp only [ContinuousMap.toFun_eq_coe]
      rewrite [cdef, continuousOn_iff_continuous_restrict]
      conv => {
        arg 1; intro y
        apply deriv.scomp
        tactic => {
          apply DifferentiableOn.differentiableAt path.differentiable_toFun
          rewrite [mem_nhds_iff]
          refine ⟨Set.Ioo (-a) (a+1), lts, isOpen_Ioo, ?_⟩
          exact inequalities.reverse_mem_cover y
        }
        tactic => {
          apply Differentiable.differentiableAt
          apply Differentiable.add
          apply differentiable_const
          apply Differentiable.neg
          exact differentiable_id'
          }
      }
      conv in _ • _ => {
          arg 1;
          rw [deriv_const_sub]
          simp only [deriv_id'', mul_one, Complex.real_smul]
      }
      apply Continuous.mul
      exact continuous_const
      rewrite [←Function.comp_def]
      apply ContinuousOn.comp_continuous (s:=Set.Ioo (-a) (a+1))
      exact ContinuousOn.mono path.continuous_deriv_toFun lts
      any_goals continuity
      intro x
      exact inequalities.reverse_mem_cover x
}

def C1Path.split (path : C1Path) (split : Set.Ioo (0:ℝ) 1) : PiecewisePath 2 := {
  paths := λ i => (by
    by_cases i = 0
    exact (path.transform ⟨split, le_of_lt split.2.1, le_of_lt split.2.2⟩ 0
    (by simp; exact le_of_lt split.2.2) (ne_of_gt split.2.1))
    exact (path.transform ⟨1 - split, le_of_lt (Set.Ioo.one_sub_mem split.2).1, le_of_lt (Set.Ioo.one_sub_mem split.2).2⟩
    ⟨split, le_of_lt split.2.1, le_of_lt split.2.2⟩ (by simp) (ne_of_gt (Set.Ioo.one_sub_mem split.2).1))
  )
}
