import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Cauchy.definitions.path_integrals

open definitions intervalIntegral MeasureTheory

namespace lemmas.path_integrals

--- Here we show that the Path Integral is additive over the function:
--- ∫_γ f + ∫_γ g = ∫_γ (f + g)

lemma pathIntegral_function_additivity {x y : ℂ } (f g : ℂ → ℂ) (γ : Path x y)
(haux₁: IntervalIntegrable (aux f γ) volume 0 1)
(haux₂: IntervalIntegrable (aux g γ) volume 0 1) :
(pathIntegral1 f γ) + (pathIntegral1 g γ) = (pathIntegral1 (f+g) γ) := by
  unfold pathIntegral1
  rw[← intervalIntegral.integral_add]
  unfold aux
  have : ∀ x ∈ (Set.uIcc 0 1), (f ∘ Path.extend γ * deriv (Path.extend γ)) x + (g ∘ Path.extend γ * deriv (Path.extend γ)) x = ((f + g) ∘ Path.extend γ * deriv (Path.extend γ)) x := by
    intro x
    simp
    rw[add_mul]
    aesop
  rw[integral_congr this]
  · exact haux₁
  · exact haux₂

lemma pathIntegral_function_additivity1 (f g : ℂ → ℂ) (γ : C1Path)
(haux₁: IntervalIntegrable (aux f γ) volume 0 1)
(haux₂: IntervalIntegrable (aux g γ) volume 0 1) :
(pathIntegral1' f γ) + (pathIntegral1' g γ) = (pathIntegral1' (f+g) γ) := by
  unfold pathIntegral1'
  rw[← intervalIntegral.integral_add]
  unfold aux
  have : ∀ x ∈ (Set.uIcc 0 1), (f ∘ γ * deriv γ) x + (g ∘  γ * deriv γ) x = ((f + g) ∘ γ * deriv γ) x := by
    intro x
    simp
    rw[add_mul]
    aesop
  rw[integral_congr this]
  · exact haux₁
  · exact haux₂
