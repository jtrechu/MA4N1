import Cauchy.definitions.triangle
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic
import Cauchy.lemmas.triangle_inequality
import Cauchy.lemmas.complex_real_norm_equiv
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Data.Set.Intervals.UnorderedInterval
import Mathlib.MeasureTheory.Integral.SetIntegral
import Cauchy.helpers.piecewise_paths
import Cauchy.lemmas.complex_ftc
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Data.Set.Intervals.UnorderedInterval
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Topology.UnitInterval
import Cauchy.definitions.path
import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Init.Set


open definitions
open helpers
open Set
open lemmas
open Nat Real MeasureTheory Set Filter Function intervalIntegral Interval

lemma holoOnTriangle {U : Set ℂ} (t : Triangle) (h_cont : TriangularSet t ⊆ U) :
  pathIntegral1 (deriv (fun x => x)) t.path = 0 := by
  rw[PiecewisePath.path_integral_three]
  rw[complex_ftc1]
  rw[complex_ftc1]
  rw[complex_ftc1]
  have h1 : C1Path.toFun (PiecewisePath.paths (Triangle.path t) 0) 1 = t.b := by
    unfold Triangle.path
    aesop
  have h2 : C1Path.toFun (PiecewisePath.paths (Triangle.path t) 0) 0 = t.a := by
    unfold Triangle.path
    aesop
  have h3 : C1Path.toFun (PiecewisePath.paths (Triangle.path t) 1) 1 = t.c := by
    unfold Triangle.path
    aesop
  have h4 : C1Path.toFun (PiecewisePath.paths (Triangle.path t) 1) 0 = t.b := by
    unfold Triangle.path
    aesop
  have h5 : C1Path.toFun (PiecewisePath.paths (Triangle.path t) 2) 1 = t.a := by
    unfold Triangle.path
    aesop
  have h6 : C1Path.toFun (PiecewisePath.paths (Triangle.path t) 2) 0 = t.c := by
    unfold Triangle.path
    aesop
  rw[h1,h2,h3,h4,h5,h6]
  ring
  have triv1 : [[0,1]] = unitInterval := by aesop
  have a : ContinuousOn (PiecewisePath.paths (Triangle.path t) 2).toFun (Set.uIcc 0 1) := by
    rw[triv1]
    exact (C1Path.continuousOnI (PiecewisePath.paths (Triangle.path t) 2))
  have b : ContinuousOn (PiecewisePath.paths (Triangle.path t) 1).toFun (Set.uIcc 0 1) := by
    rw[triv1]
    exact (C1Path.continuousOnI (PiecewisePath.paths (Triangle.path t) 1))
  have c : ContinuousOn (PiecewisePath.paths (Triangle.path t) 0).toFun (Set.uIcc 0 1) := by
    rw[triv1]
    exact (C1Path.continuousOnI (PiecewisePath.paths (Triangle.path t) 0))
  have h7 : ContinuousOn (deriv ((fun x => x))) (Set.uIcc 0 (1:ℝ)) := by
    rw[deriv_id'']
    exact (continuousOn_const)
  
  have i1 : ContinuousOn (deriv ((fun x => x)) ∘ (PiecewisePath.paths (Triangle.path t) 2).toFun) (Set.uIcc 0 (1:ℝ)) := by
    sorry -- this is used for IntervalIntegrable
  have i2 : ContinuousOn (deriv ((fun x => x)) ∘ (PiecewisePath.paths (Triangle.path t) 1).toFun) (Set.uIcc 0 (1:ℝ)) := by
    sorry
  have i3 : ContinuousOn (deriv ((fun x => x)) ∘ (PiecewisePath.paths (Triangle.path t) 0).toFun) (Set.uIcc 0 (1:ℝ)) := by
    sorry    
  have g1 : IntervalIntegrable (PiecewisePath.paths (Triangle.path t) 2).toFun volume 0 1 := by
    exact (ContinuousOn.intervalIntegrable a)
  have g2 : IntervalIntegrable (PiecewisePath.paths (Triangle.path t) 1).toFun volume 0 1 := by
    exact (ContinuousOn.intervalIntegrable b)
  have g3 : IntervalIntegrable (PiecewisePath.paths (Triangle.path t) 0).toFun volume 0 1 := by
    exact (ContinuousOn.intervalIntegrable c)
  have w : IntervalIntegrable (deriv (fun x => x)) volume 0 1 := by
    exact (ContinuousOn.intervalIntegrable h7)
  have aux1 : ∀ x ∈ [[0, (1:ℝ)]], DifferentiableAt ℝ (deriv (fun x => x)) x := by
    rw[deriv_id'']
    sorry -- exact (differentiableAt_const (1:ℝ))
  have aux2 : ∀ x ∈ [[0, 1]], DifferentiableAt ℝ (fun x => x) x := by
-- how to fix the instance
    --exact (differentiableAt_id')
    sorry
  have h9 : ∀ x ∈ [[0, 1]], DifferentiableAt ℝ (PiecewisePath.paths (Triangle.path t) 2).toFun x := by
    have j1 : DifferentiableOn ℝ (PiecewisePath.paths (Triangle.path t) 2).toFun [[0,1]] := by
            rw[triv1]
            exact(C1Path.differentiableOnI (PiecewisePath.paths (Triangle.path t) 2))
    
    unfold DifferentiableOn at j1 -- how to pass from within to at
    sorry
  
  have h10 : ∀ x ∈ [[0, 1]], DifferentiableAt ℝ ((fun x => x) ∘ (PiecewisePath.paths (Triangle.path t) 2).toFun) x := by
    exact (DifferentiableAt.comp aux2 h9)

  have h11 : IntervalIntegrable (deriv ((fun x => x)) ∘ (PiecewisePath.paths (Triangle.path t) 2).toFun) volume 0 1 := by
    exact (ContinuousOn.intervalIntegrable i1)
    
  have h12 : ∀ x ∈ [[0, 1]], DifferentiableAt ℝ (PiecewisePath.paths (Triangle.path t) 1).toFun x := by
    have j1 : DifferentiableOn ℝ (PiecewisePath.paths (Triangle.path t) 1).toFun [[0,1]] := by
            rw[triv1]
            exact(C1Path.differentiableOnI (PiecewisePath.paths (Triangle.path t) 1))
    
    unfold DifferentiableOn at j1
    sorry
  
  have h13 : ∀ x ∈ [[0, 1]], DifferentiableAt ℝ ((fun x => x) ∘ (PiecewisePath.paths (Triangle.path t) 1).toFun) x := by
    sorry
  have h14 : IntervalIntegrable (deriv ((fun x => x)) ∘ (PiecewisePath.paths (Triangle.path t) 1).toFun) volume 0 1 := by
        exact (ContinuousOn.intervalIntegrable i2)

  have h15 : ∀ x ∈ [[0, 1]], DifferentiableAt ℝ (PiecewisePath.paths (Triangle.path t) 0).toFun x := by
    have j1 : DifferentiableOn ℝ (PiecewisePath.paths (Triangle.path t) 0).toFun [[0,1]] := by
            rw[triv1]
            exact(C1Path.differentiableOnI (PiecewisePath.paths (Triangle.path t) 0))
    
    unfold DifferentiableOn at j1
    sorry
  
  have h16 : ∀ x ∈ [[0, 1]], DifferentiableAt ℝ ((fun x => x) ∘ (PiecewisePath.paths (Triangle.path t) 0).toFun) x := by
    sorry
  have h17 : IntervalIntegrable (deriv ((fun x => x)) ∘ (PiecewisePath.paths (Triangle.path t) 0).toFun) volume 0 1 := by
        exact (ContinuousOn.intervalIntegrable i3)
  repeat sorry
