import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Field.Basic

open Set
open Nat Real MeasureTheory Set Filter Function intervalIntegral Interval
open unitInterval

namespace definitions

noncomputable def aux {x y : ℂ } (f : ℂ → ℂ) (γ : Path x y) : ℝ  → ℂ :=
 (Function.comp f (Path.extend γ)) * (deriv (Path.extend γ))

noncomputable def pathIntegral1 {x y : ℂ } (f : ℂ → ℂ) (γ : Path x y) : ℂ :=
∫t in (0)..(1), (aux f γ)  t ∂volume

noncomputable def length {x y : ℂ } (γ : Path x y) : ℝ :=
∫ t in (0)..(1), Complex.abs ((deriv (Path.extend γ)) t) ∂volume

end definitions
