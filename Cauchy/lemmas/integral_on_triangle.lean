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
import Mathlib.Order.RelClasses

import Cauchy.definitions.path_integrals
import Cauchy.definitions.path
import Cauchy.lemmas.path_equalities
import Cauchy.definitions.triangle
import Cauchy.helpers.piecewise_paths
import Cauchy.definitions.subtriangle
import Cauchy.theorems.linear_path_equivalence
import Cauchy.definitions.linear_path
import Cauchy.helpers.triangle_integral_helper


open trianglehelper definitions helpers theorems intervalIntegral unitInterval

lemma triangleIntegral {U : Set ℂ} (f : ℂ → ℂ) (t : Triangle)  (h₁ : DifferentiableOn ℂ f U) (h₂: TriangularBoundary t ⊆ U) :
  pathIntegral1 f t.path = pathIntegral1 f (subTriangleA t).path + pathIntegral1 f (subTriangleB t).path + pathIntegral1 f (subTriangleC t).path +pathIntegral1 f (subTriangleD t).path := by
  repeat rewrite[PiecewisePath.path_integral_three]
  rw[helper1,helper2,helper3,helper4,helper5,helper6,helper7,helper8,helper9,helper10,helper11,helper12,helper13,helper14,helper15]
  rw[helper16,helper17,helper18]
  rw[(helper19 f t h₁ h₂),(helper20 f t h₁ h₂),(helper21 f t h₁ h₂)]
  ring

lemma triangleIntegral' {U : Set ℂ} (f : ℂ → ℂ) (t : Triangle)  (h₁ : DifferentiableOn ℂ f U) (h₂: TriangularBoundary t ⊆ U) :
trianglePathIntegral f t = trianglePathIntegral f (subTriangleA t) + trianglePathIntegral f (subTriangleB t) + trianglePathIntegral f (subTriangleC t) +trianglePathIntegral f (subTriangleD t)  := by
unfold trianglePathIntegral
apply triangleIntegral
aesop
exact h₂
