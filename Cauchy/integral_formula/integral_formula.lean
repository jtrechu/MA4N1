import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv

import Cauchy.definitions.path_integrals
import Cauchy.definitions.triangle

import Cauchy.integral_zero._1_triangle_sequence

open definitions

theorem Cauchy_integral_formula {U : Set ℂ } {f : ℂ  → ℂ } {z : ℂ}
(h_UDomain: IsCDomain U) (h_TSubU : TriangularBoundary T ⊆ U) (h_fAnalytic : DifferentiableOn ℂ f (U \ {z} ))
(ht : ∃ t : Triangle, TriangularBoundary t ⊆ U):
∀ w ∈ TriangularSet t , (2*π*Complex.I)*(f z) = pathIntegral1 (fun w => (f w)/(w-z)) t.path := by sorry
