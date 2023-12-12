import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Analysis.Calculus.Deriv.Comp
import Std.Data.Fin.Lemmas

import Cauchy.definitions.path
import Cauchy.definitions.path_integrals

open definitions Fin

namespace helpers

lemma PiecewisePath.path_integral_empty (p : PiecewisePath 0) {f : ℂ → ℂ} : pathIntegral1 f p = 0 := by
  rfl

lemma PiecewisePath.path_integral_one (p : PiecewisePath 1) {f : ℂ → ℂ} :
  pathIntegral1 f p = pathIntegral1' f (p.paths 0) := by
  unfold pathIntegral1
  rewrite [Fin.sum_univ_one]
  rfl

lemma PiecewisePath.path_integral_two (p : PiecewisePath 2) {f : ℂ → ℂ} :
  pathIntegral1 f p = pathIntegral1' f (p.paths 0) + pathIntegral1' f (p.paths 1) := by
  unfold pathIntegral1
  rewrite [Fin.sum_univ_two]
  rfl

lemma PiecewisePath.path_integral_three (p : PiecewisePath 3) {f : ℂ → ℂ} :
  pathIntegral1 f p = pathIntegral1' f (p.paths 0) + pathIntegral1' f (p.paths 1) +
    pathIntegral1' f (p.paths 2) := by
  unfold pathIntegral1
  rewrite [Fin.sum_univ_three]
  rfl
