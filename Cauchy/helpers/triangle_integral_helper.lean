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
import Mathlib.Tactic

open definitions helpers theorems intervalIntegral unitInterval

namespace trianglehelper

-- This file deals with some trivial, but a bit tidious, results that will be helpful when splitting the triangle into
-- its 4 subtriangles when applying the integral

-- Here we show that the three sides of the triangle are contained in the triangular Boundary of T,

lemma sideABInTriangle (t: Triangle) : (LinearPath.mk t.a t.b)''I ⊆ (TriangularBoundary t) := by
intro y
rw[Set.mem_image]
aesop
unfold TriangularBoundary
use (1 - ↑w),↑w,0
simp_all only [ge_iff_le, sub_nonneg, le_refl, add_zero, sub_add_cancel, mul_zero, zero_mul, Complex.ofReal_sub,
    Complex.ofReal_one, Complex.ofReal_zero, and_self]

lemma sideBCInTriangle (t: Triangle) : (LinearPath.mk t.b t.c)''I ⊆ (TriangularBoundary t) := by
intro y
rw[Set.mem_image]
aesop
unfold TriangularBoundary
use 0,(1 - ↑w),↑w
simp_all only [le_refl, ge_iff_le, sub_nonneg, zero_add, sub_add_cancel, zero_mul, Complex.ofReal_zero,
    Complex.ofReal_sub, Complex.ofReal_one, and_self]

lemma sideCAInTriangle (t: Triangle) : (LinearPath.mk t.c t.a)''I ⊆ (TriangularBoundary t) := by
intro y
rw[Set.mem_image]
aesop
unfold TriangularBoundary
use ↑w,0,(1 - ↑w)
ring_nf
aesop
ring

--The following results deal with splitting and organizing the sides of the triangles so that they are as we
--need them to be for the proof in file integral_on_triangle.lean

-- here we substitute the i-th C1-path in the triangle with the i-th side of the triangle as a linear path
lemma helper1 (f : ℂ → ℂ) (t : Triangle) :
pathIntegral1' f (PiecewisePath.paths (Triangle.path t) 0) = pathIntegral1' f (LinearPath.mk t.a t.b) := by
simp_all only
apply Eq.refl

lemma helper2 (f : ℂ → ℂ) (t : Triangle) :
pathIntegral1' f (PiecewisePath.paths (Triangle.path t) 1) = pathIntegral1' f (LinearPath.mk t.b t.c) := by
simp_all only
apply Eq.refl

lemma helper3 (f : ℂ → ℂ) (t : Triangle) :
pathIntegral1' f (PiecewisePath.paths (Triangle.path t) 2) = pathIntegral1' f (LinearPath.mk t.c t.a) := by
simp_all only
apply Eq.refl

-- here we do the same but for the 4 subtriangles

lemma helper4 (f : ℂ → ℂ) (t :Triangle) : pathIntegral1' f (PiecewisePath.paths (Triangle.path (subTriangleA t).toTriangle) 0) =  pathIntegral1' f (LinearPath.mk t.a (t.a*(1/2)+t.b*(1/2))) := by
unfold subTriangleA
unfold constructSubTriangle
unfold SubTriangle.toTriangle
aesop

lemma helper5 (f : ℂ → ℂ) (t :Triangle) : pathIntegral1' f (PiecewisePath.paths (Triangle.path (subTriangleA t).toTriangle) 1) =  pathIntegral1' f (LinearPath.mk (t.a*(1/2)+t.b*(1/2)) (t.a*(1/2)+t.c*(1/2))) := by
unfold subTriangleA
unfold constructSubTriangle
unfold SubTriangle.toTriangle
aesop

lemma helper6 (f : ℂ → ℂ) (t :Triangle) : pathIntegral1' f (PiecewisePath.paths (Triangle.path (subTriangleA t).toTriangle) 2) =  pathIntegral1' f (LinearPath.mk (t.a*(1/2)+t.c*(1/2)) t.a) := by
unfold subTriangleA
unfold constructSubTriangle
unfold SubTriangle.toTriangle
aesop

lemma helper7 (f : ℂ → ℂ) (t :Triangle) : pathIntegral1' f (PiecewisePath.paths (Triangle.path (subTriangleB t).toTriangle) 0) =  pathIntegral1' f (LinearPath.mk (t.a*(1/2)+t.b*(1/2)) t.b) := by
unfold subTriangleB
unfold constructSubTriangle
unfold SubTriangle.toTriangle
aesop

lemma helper8 (f : ℂ → ℂ) (t :Triangle) : pathIntegral1' f (PiecewisePath.paths (Triangle.path (subTriangleB t).toTriangle) 1) =  pathIntegral1' f (LinearPath.mk t.b (t.b*(1/2)+t.c*(1/2))) := by
unfold subTriangleB
unfold constructSubTriangle
unfold SubTriangle.toTriangle
aesop

lemma helper9 (f : ℂ → ℂ) (t :Triangle) : pathIntegral1' f (PiecewisePath.paths (Triangle.path (subTriangleB t).toTriangle) 2) =  pathIntegral1' f (LinearPath.mk (t.b*(1/2)+t.c*(1/2)) (t.a*(1/2)+t.b*(1/2))) := by
unfold subTriangleB
unfold constructSubTriangle
unfold SubTriangle.toTriangle
aesop

lemma helper10 (f : ℂ → ℂ) (t :Triangle) : pathIntegral1' f (PiecewisePath.paths (Triangle.path (subTriangleC t).toTriangle) 0) =  pathIntegral1' f (LinearPath.mk (t.a*(1/2)+t.c*(1/2)) (t.b*(1/2)+t.c*(1/2))) := by
unfold subTriangleC
unfold constructSubTriangle
unfold SubTriangle.toTriangle
aesop

lemma helper11 (f : ℂ → ℂ) (t :Triangle) : pathIntegral1' f (PiecewisePath.paths (Triangle.path (subTriangleC t).toTriangle) 1) =  pathIntegral1' f (LinearPath.mk (t.b*(1/2)+t.c*(1/2)) t.c) := by
unfold subTriangleC
unfold constructSubTriangle
unfold SubTriangle.toTriangle
aesop

lemma helper12 (f : ℂ → ℂ) (t :Triangle) : pathIntegral1' f (PiecewisePath.paths (Triangle.path (subTriangleC t).toTriangle) 2) =  pathIntegral1' f (LinearPath.mk t.c (t.a*(1/2)+t.c*(1/2))) := by
unfold subTriangleC
unfold constructSubTriangle
unfold SubTriangle.toTriangle
aesop

lemma helper13 (f : ℂ → ℂ) (t :Triangle) : pathIntegral1' f (PiecewisePath.paths (Triangle.path (subTriangleD t).toTriangle) 0) =  pathIntegral1' f (LinearPath.mk (t.a*(1/2)+t.b*(1/2)) (t.b*(1/2)+t.c*(1/2))) := by
unfold subTriangleD
unfold constructSubTriangle
unfold SubTriangle.toTriangle
aesop

lemma helper14 (f : ℂ → ℂ) (t :Triangle) : pathIntegral1' f (PiecewisePath.paths (Triangle.path (subTriangleD t).toTriangle) 1) =  pathIntegral1' f (LinearPath.mk (t.b*(1/2)+t.c*(1/2)) (t.a*(1/2)+t.c*(1/2))) := by
unfold subTriangleD
unfold constructSubTriangle
unfold SubTriangle.toTriangle
aesop

lemma helper15 (f : ℂ → ℂ) (t :Triangle) : pathIntegral1' f (PiecewisePath.paths (Triangle.path (subTriangleD t).toTriangle) 2) =  pathIntegral1' f (LinearPath.mk (t.a*(1/2)+t.c*(1/2)) (t.a*(1/2)+t.b*(1/2))) := by
unfold subTriangleD
unfold constructSubTriangle
unfold SubTriangle.toTriangle
aesop

-- now we reverse the linear paths that we need reversed, so that we have the negative signs
-- in front of the integral instead of the inverse path

lemma helper16 (f: ℂ → ℂ) (t: Triangle) : pathIntegral1' f (LinearPath.mk (t.a*(1/2)+t.c*(1/2)) (t.a*(1/2)+t.b*(1/2))) = - pathIntegral1' f (LinearPath.mk (t.a*(1/2)+t.b*(1/2)) (t.a*(1/2)+t.c*(1/2))) :=by
rw[←reverse_pathIntegral_neg]
unfold pathIntegral1'
unfold aux
rw[linear_path_reverse { head := t.a * (1 / 2) + t.b * (1 / 2), tail := t.a * (1 / 2) + t.c * (1 / 2) }]

lemma helper17 (f: ℂ → ℂ) (t: Triangle) : pathIntegral1' f (LinearPath.mk (t.b*(1/2)+t.c*(1/2)) (t.a*(1/2)+t.c*(1/2))) = - pathIntegral1' f (LinearPath.mk (t.a*(1/2)+t.c*(1/2)) (t.b*(1/2)+t.c*(1/2))) :=by
rw[←reverse_pathIntegral_neg]
unfold pathIntegral1'
unfold aux
rw[linear_path_reverse]

lemma helper18 (f: ℂ → ℂ) (t: Triangle) : pathIntegral1' f (LinearPath.mk (t.a*(1/2)+t.b*(1/2)) (t.b*(1/2)+t.c*(1/2))) = - pathIntegral1' f (LinearPath.mk (t.b*(1/2)+t.c*(1/2)) (t.a*(1/2)+t.b*(1/2))) :=by
rw[←reverse_pathIntegral_neg]
unfold pathIntegral1'
unfold aux
rw[linear_path_reverse]

-- here we'll show that the path integral over a segment is the same as the integral
-- over the first half of the segment plus the integral over the second half
-- We do this with the three sides of our main triangle:


lemma helper19 {U : Set ℂ}(f: ℂ → ℂ) (t: Triangle) (h₁ : DifferentiableOn ℂ f U) (h₂: TriangularBoundary t ⊆ U) :
pathIntegral1' f (LinearPath.mk t.a t.b) = pathIntegral1' f (LinearPath.mk t.a (t.a*(1/2)+t.b*(1/2))) + pathIntegral1' f (LinearPath.mk (t.a*(1/2)+t.b*(1/2)) t.b) :=by
rw[split_equality (split := ⟨1/2,by norm_num ⟩)]
rw[PiecewisePath.path_integral_two]
unfold C1Path.split
unfold C1Path.transform
unfold pathIntegral1'
unfold aux
aesop
have j₁  (x : ℂ) :  (1 - 2⁻¹ * x) * t.a + 2⁻¹ * x * t.b = (1 - x) * t.a + x * (t.a * 2⁻¹ + t.b * 2⁻¹) := by
  ring
have j₂ :∀ p ∈ (Set.uIcc (0:ℝ) 1) , f ((1 - 2⁻¹ * ↑p) * t.a + 2⁻¹ * ↑p * t.b) * (deriv (fun x => (1 - 2⁻¹ * ↑x) * t.a + 2⁻¹ * ↑x * t.b) p) =  f ((1 - ↑p) * t.a + ↑p * (t.a * 2⁻¹ + t.b * 2⁻¹)) *(deriv (fun x => (1 - ↑x) * t.a + ↑x * (t.a * 2⁻¹ + t.b * 2⁻¹)) p):= by
  intro p
  rw[j₁ ↑p]
  aesop
have j : (∫ (t_1 : ℝ) in (0)..(1), f ((1 - 2⁻¹ * ↑t_1) * t.a + 2⁻¹ * ↑t_1 * t.b) * deriv (fun x => (1 - 2⁻¹ * ↑x) * t.a + 2⁻¹ * ↑x * t.b) t_1) = (∫ (t_1 : ℝ) in (0)..(1),
      f ((1 - ↑t_1) * t.a + ↑t_1 * (t.a * 2⁻¹ + t.b * 2⁻¹)) *
        deriv (fun t_2 => (1 - ↑t_2) * t.a + ↑t_2 * (t.a * 2⁻¹ + t.b * 2⁻¹)) t_1) := by
        rw[integral_congr j₂]
rw[j]
have g₁ (x:ℂ) : (1 - ((1 - 2⁻¹) * x + 2⁻¹)) * t.a + ((1 - 2⁻¹) * x + 2⁻¹) * t.b = (1 - x) * (t.a * 2⁻¹ + t.b * 2⁻¹) + x * t.b := by
  ring
have g₂ : ∀ p ∈ (Set.uIcc (0:ℝ) 1), f ((1 - ((1 - 2⁻¹) * ↑p + 2⁻¹)) * t.a + ((1 - 2⁻¹) * ↑p + 2⁻¹) * t.b) *(deriv (fun x => (1 - ((1 - 2⁻¹) * ↑x + 2⁻¹)) * t.a + ((1 - 2⁻¹) * ↑x + 2⁻¹) * t.b) p) = f ((1 - ↑p) * (t.a * 2⁻¹ + t.b * 2⁻¹) + ↑p * t.b) * (deriv (fun t_2 => (1 - ↑t_2) * (t.a * 2⁻¹ + t.b * 2⁻¹) + ↑t_2 * t.b) p) := by
  intro p
  rw[g₁ ↑p]
  aesop

have g : ( ∫ (t_1 : ℝ) in (0)..(1), f ((1 - ((1 - 2⁻¹) * ↑t_1 + 2⁻¹)) * t.a + ((1 - 2⁻¹) * ↑t_1 + 2⁻¹) * t.b) * deriv (fun x => (1 - ((1 - 2⁻¹) * ↑x + 2⁻¹)) * t.a + ((1 - 2⁻¹) * ↑x + 2⁻¹) * t.b) t_1) = (∫ (t_1 : ℝ) in (0)..(1), f ((1 - ↑t_1) * (t.a * 2⁻¹ + t.b * 2⁻¹) + ↑t_1 * t.b) * deriv (fun t_2 => (1 - ↑t_2) * (t.a * 2⁻¹ + t.b * 2⁻¹) + ↑t_2 * t.b) t_1) := by
  rw[integral_congr g₂]
rw[g]
exact h₁
have cont :  (LinearPath.mk t.a t.b) '' I ⊆ TriangularBoundary t := by exact (sideABInTriangle t)
have cont2 :  (LinearPath.mk t.a t.b) '' I ⊆ U := by
  exact (subset_trans cont h₂)
exact cont2



lemma helper20 {U: Set ℂ}(f: ℂ → ℂ) (t: Triangle) (h₁ : DifferentiableOn ℂ f U) (h₂: TriangularBoundary t ⊆ U) :
pathIntegral1' f (LinearPath.mk t.b t.c) = pathIntegral1' f (LinearPath.mk t.b (t.b*(1/2)+t.c*(1/2))) + pathIntegral1' f (LinearPath.mk (t.b*(1/2)+t.c*(1/2)) t.c) :=by
rw[split_equality (split := ⟨1/2,by norm_num ⟩)]
rw[PiecewisePath.path_integral_two]
unfold C1Path.split
unfold C1Path.transform
unfold pathIntegral1'
unfold aux
aesop
have g₁ (x:ℂ): (1 - 2⁻¹ * x) * t.b + 2⁻¹ * x * t.c = (1 - x) * t.b + x * (t.b * 2⁻¹ + t.c * 2⁻¹) := by
  ring
have g₂: ∀ p ∈ (Set.uIcc (0:ℝ) 1), f ((1 - 2⁻¹ * ↑p) * t.b + 2⁻¹ * ↑p * t.c) * deriv (fun x => (1 - 2⁻¹ * ↑x) * t.b + 2⁻¹ * ↑x * t.c) p  = f ((1 - ↑p) * t.b + ↑p * (t.b * 2⁻¹ + t.c * 2⁻¹)) * deriv (fun t_2 => (1 - ↑t_2) * t.b + ↑t_2 * (t.b * 2⁻¹ + t.c * 2⁻¹)) p := by
   intro p
   rw[g₁ ↑p]
   aesop
have g: (∫ (t_1 : ℝ) in (0)..(1),f ((1 - 2⁻¹ * ↑t_1) * t.b + 2⁻¹ * ↑t_1 * t.c) * deriv (fun x => (1 - 2⁻¹ * ↑x) * t.b + 2⁻¹ * ↑x * t.c) t_1) = (∫ (t_1 : ℝ) in (0)..(1),f ((1 - ↑t_1) * t.b + ↑t_1 * (t.b * 2⁻¹ + t.c * 2⁻¹)) * deriv (fun t_2 => (1 - ↑t_2) * t.b + ↑t_2 * (t.b * 2⁻¹ + t.c * 2⁻¹)) t_1) := by
  rw[integral_congr g₂]
rw[g]
have j₁ (x:ℂ): (1 - ((1 - 2⁻¹) * x + 2⁻¹)) * t.b + ((1 - 2⁻¹) * x + 2⁻¹) * t.c = (1 - x) * (t.b * 2⁻¹ + t.c * 2⁻¹) + x * t.c := by
  ring
have j₂: ∀ p ∈ (Set.uIcc (0:ℝ) 1), f ((1 - ((1 - 2⁻¹) * ↑p + 2⁻¹)) * t.b + ((1 - 2⁻¹) * ↑p + 2⁻¹) * t.c) * deriv (fun x => (1 - ((1 - 2⁻¹) * ↑x + 2⁻¹)) * t.b + ((1 - 2⁻¹) * ↑x + 2⁻¹) * t.c) p = f ((1 - ↑p) * (t.b * 2⁻¹ + t.c * 2⁻¹) + ↑p * t.c) * deriv (fun t_2 => (1 - ↑t_2) * (t.b * 2⁻¹ + t.c * 2⁻¹) + ↑t_2 * t.c) p := by
  intro p
  rw[j₁ ↑p]
  aesop
have j: ∫ (t_1 : ℝ) in (0)..(1),f ((1 - ((1 - 2⁻¹) * ↑t_1 + 2⁻¹)) * t.b + ((1 - 2⁻¹) * ↑t_1 + 2⁻¹) * t.c) * deriv (fun x => (1 - ((1 - 2⁻¹) * ↑x + 2⁻¹)) * t.b + ((1 - 2⁻¹) * ↑x + 2⁻¹) * t.c) t_1 = ∫ (t_1 : ℝ) in (0)..(1),f ((1 - ↑t_1) * (t.b * 2⁻¹ + t.c * 2⁻¹) + ↑t_1 * t.c) *deriv (fun t_2 => (1 - ↑t_2) * (t.b * 2⁻¹ + t.c * 2⁻¹) + ↑t_2 * t.c) t_1 := by
  rw[integral_congr j₂]
rw[j]
exact h₁
have cont :  (LinearPath.mk t.b t.c) '' I ⊆ TriangularBoundary t := by exact (sideBCInTriangle t)
have cont2 :  (LinearPath.mk t.b t.c) '' I ⊆ U := by
  exact (subset_trans cont h₂)
exact cont2

lemma helper21 {U: Set ℂ}(f: ℂ → ℂ) (t: Triangle) (h₁ : DifferentiableOn ℂ f U) (h₂: TriangularBoundary t ⊆ U):
pathIntegral1' f (LinearPath.mk t.c t.a) = pathIntegral1' f (LinearPath.mk t.c (t.a*(1/2)+t.c*(1/2))) + pathIntegral1' f (LinearPath.mk (t.a*(1/2)+t.c*(1/2)) t.a) :=by
rw[split_equality (split := ⟨1/2,by norm_num ⟩)]
rw[PiecewisePath.path_integral_two]
unfold C1Path.split
unfold C1Path.transform
unfold pathIntegral1'
unfold aux
aesop
have g₁ (x:ℂ): (1 - 2⁻¹ * x) * t.c + 2⁻¹ * x * t.a = (1 - x) * t.c + x * (t.a * 2⁻¹ + t.c * 2⁻¹) := by
  ring
have g₂: ∀ p ∈ (Set.uIcc (0:ℝ) 1), f ((1 - 2⁻¹ * ↑p) * t.c + 2⁻¹ * ↑p * t.a) * deriv (fun x => (1 - 2⁻¹ * ↑x) * t.c + 2⁻¹ * ↑x * t.a) p = f ((1 - ↑p) * t.c + ↑p * (t.a * 2⁻¹ + t.c * 2⁻¹)) * deriv (fun t_2 => (1 - ↑t_2) * t.c + ↑t_2 * (t.a * 2⁻¹ + t.c * 2⁻¹)) p := by
  intro p
  rw[g₁ ↑p]
  aesop
have g : (∫ (t_1 : ℝ) in (0)..(1), f ((1 - 2⁻¹ * ↑t_1) * t.c + 2⁻¹ * ↑t_1 * t.a) * deriv (fun x => (1 - 2⁻¹ * ↑x) * t.c + 2⁻¹ * ↑x * t.a) t_1) = (∫ (t_1 : ℝ) in (0)..(1),f ((1 - ↑t_1) * t.c + ↑t_1 * (t.a * 2⁻¹ + t.c * 2⁻¹)) *deriv (fun t_2 => (1 - ↑t_2) * t.c + ↑t_2 * (t.a * 2⁻¹ + t.c * 2⁻¹)) t_1) := by
  rw[integral_congr g₂]
rw[g]
have j₁ (x:ℂ) : (1 - ((1 - 2⁻¹) * x + 2⁻¹)) * t.c + ((1 - 2⁻¹) * x + 2⁻¹) * t.a = (1 - x) * (t.a * 2⁻¹ + t.c * 2⁻¹) + x * t.a := by
  ring
have j₂:∀ p ∈ (Set.uIcc (0:ℝ) 1), f ((1 - ((1 - 2⁻¹) * ↑p + 2⁻¹)) * t.c + ((1 - 2⁻¹) * ↑p + 2⁻¹) * t.a) *deriv (fun x => (1 - ((1 - 2⁻¹) * ↑x + 2⁻¹)) * t.c + ((1 - 2⁻¹) * ↑x + 2⁻¹) * t.a) p = f ((1 - ↑p) * (t.a * 2⁻¹ + t.c * 2⁻¹) + ↑p * t.a) *deriv (fun t_2 => (1 - ↑t_2) * (t.a * 2⁻¹ + t.c * 2⁻¹) + ↑t_2 * t.a) p := by
  intro p
  rw[j₁ ↑p]
  aesop
have j: ∫ (t_1 : ℝ) in (0)..(1),f ((1 - ((1 - 2⁻¹) * ↑t_1 + 2⁻¹)) * t.c + ((1 - 2⁻¹) * ↑t_1 + 2⁻¹) * t.a) *deriv (fun x => (1 - ((1 - 2⁻¹) * ↑x + 2⁻¹)) * t.c + ((1 - 2⁻¹) * ↑x + 2⁻¹) * t.a) t_1 =  ∫ (t_1 : ℝ) in (0)..(1),f ((1 - ↑t_1) * (t.a * 2⁻¹ + t.c * 2⁻¹) + ↑t_1 * t.a) *deriv (fun t_2 => (1 - ↑t_2) * (t.a * 2⁻¹ + t.c * 2⁻¹) + ↑t_2 * t.a) t_1 := by
  rw[integral_congr j₂]
rw[j]
exact h₁
have cont :  (LinearPath.mk t.c t.a) '' I ⊆ TriangularBoundary t := by exact (sideCAInTriangle t)
have cont2 :  (LinearPath.mk t.c t.a) '' I ⊆ U := by
  exact (subset_trans cont h₂)
exact cont2
