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
import Mathlib.Analysis.Complex.RealDeriv

import Cauchy.definitions.path

namespace definitions

open definitions unitInterval

theorem Complex.differentiable_coe : Differentiable ℝ (λ x => ↑x : ℝ → ℂ) := by
  rewrite [Differentiable]
  intro x
  apply HasFDerivAt.differentiableAt
  apply HasDerivAt.ofReal_comp
  rewrite [hasDerivAt_deriv_iff]
  exact differentiableAt_id'

theorem Complex.deriv_coe (x : ℝ) : deriv (λ x => ↑x : ℝ → ℂ) x = 1 := by
  apply HasDerivAt.deriv
  apply HasDerivAt.ofReal_comp
  exact hasDerivAt_id' x


def linearPath (a b : ℂ) : C1Path := {
  toFun := λ t => (1 - t)*a + t*b
  open_cover := {
    set := Set.univ
    h := ⟨isOpen_univ, Set.subset_univ I⟩
  }
  differentiable_toFun := by
    apply DifferentiableOn.add
    apply DifferentiableOn.mul_const
    rewrite [differentiableOn_const_sub_iff]
    exact Differentiable.differentiableOn Complex.differentiable_coe
    apply DifferentiableOn.mul_const
    exact Differentiable.differentiableOn Complex.differentiable_coe
  continuous_deriv_toFun := by
    conv => {
      arg 1; intro x
      rewrite [deriv_add, deriv_mul_const, deriv_mul_const, deriv_const_sub, Complex.deriv_coe]
      exact rfl
      any_goals apply DifferentiableAt.mul_const
      any_goals apply DifferentiableAt.const_sub
      all_goals exact Differentiable.differentiableAt Complex.differentiable_coe
    }
    exact continuousOn_const
}
