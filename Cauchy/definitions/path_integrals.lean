import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Cauchy.definitions.path

open Set
open Nat Real MeasureTheory Set Filter Function intervalIntegral Interval
open unitInterval
open definitions

namespace definitions

noncomputable def aux (f : ℂ → ℂ) (γ : C1Path) : ℝ  → ℂ :=
 f ∘ γ * deriv γ

noncomputable def pathIntegral1 (f : ℂ → ℂ) (γ : C1Path) : ℂ :=
∫t in (0)..(1), (aux f γ) t ∂volume

noncomputable def length (γ : C1Path) : ℝ :=
∫ t in (0)..(1), Complex.abs (deriv γ t) ∂volume

end definitions
