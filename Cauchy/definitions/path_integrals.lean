import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Cauchy.definitions.path
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic

open Set
open Nat Real MeasureTheory Set Filter Function intervalIntegral Interval
open unitInterval Finset BigOperators
open definitions

namespace definitions

noncomputable def aux (f : ℂ → ℂ) (γ : C1Path) : ℝ  → ℂ :=
 f ∘ γ * deriv γ

noncomputable def pathIntegral1 (f : ℂ → ℂ) (γ : PiecewisePath) : ℂ :=
  ∑ i, ∫t in (0)..(1), (aux f (γ.paths i)) t ∂volume

noncomputable def length (γ : C1Path) : ℝ :=
∫ t in (0)..(1), Complex.abs (deriv γ t) ∂volume

end definitions
