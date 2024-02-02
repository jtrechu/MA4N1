import Mathlib.Data.Complex.Basic
import Cauchy.lemmas.complex_real_norm_equiv
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Data.Set.Intervals.UnorderedInterval
import Mathlib.MeasureTheory.Integral.SetIntegral
import Cauchy.definitions.domain

-- I thought it could be useful for the proof of the main theorem 

open definitions

noncomputable def holo (f : ℂ  → ℂ) (U : Set ℂ) (z0 : U) (hu : IsCDomain U) : Prop := 
                  ∀ ε > 0, ∀ w ∈ U, ∃ δ > 0, ‖w - z0‖ ≤ δ → ‖f w - f z0 - (w-z0)*(deriv f z0)‖ < ε
