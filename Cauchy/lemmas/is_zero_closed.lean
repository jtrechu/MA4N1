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
import Cauchy.definitions.triangle
import Cauchy.definitions.path_integrals
import Cauchy.lemmas.complex_ftc

theorem is_zero_closed (z w : ℂ) (f : ℂ → ℂ) (γ : Path z w)
      (hf_deriv : ∀ x ∈ (Set.uIcc 0 1), DifferentiableAt ℝ (f ∘ (Path.extend γ)) x)
      (hγ_deriv : ∀ x ∈ (Set.uIcc 0 1), DifferentiableAt ℝ (Path.extend γ) x)
      (h_int : IntervalIntegrable (deriv (f ∘ (Path.extend γ))) volume 0 1)
      (hγ_closed : z = w) :
      pathIntegral1 z w (deriv f) γ = 0 := by
      rw[complex_ftc2]
      simp
      rw[hγ_closed]
      simp
      aesop
      aesop
      aesop

-- The second definition doesn't use the Complex FTC. I just add it in case it can be useful

theorem is_zero_closed2 (z w : ℂ) (f : ℂ → ℂ) (γ : Path z w)
      (hf_deriv : ∀ x ∈ (Set.uIcc 0 1), DifferentiableAt ℝ (f ∘ (Path.extend γ)) x)
      (hγ_deriv : ∀ x ∈ (Set.uIcc 0 1), DifferentiableAt ℝ (Path.extend γ) x)
      (h_int : IntervalIntegrable (deriv (f ∘ (Path.extend γ))) volume 0 1)
      (hγ_closed : z = w) :
      pathIntegral1 z w (deriv f) γ = 0 := by
    unfold pathIntegral1
    unfold aux
    have : ∀ y ∈ (Set.uIcc 0 1),(deriv f ∘ Path.extend γ * deriv (Path.extend γ)) y = deriv (f ∘ (Path.extend γ)) y := by
      intro y hy
      rw [deriv.comp]
      simp
      · exact aux2 (hf_deriv y hy)
      · exact hγ_deriv y hy
    simp
    have : ∀ t ∈ (Set.uIcc 0 1), deriv f (Path.extend γ t) * deriv (Path.extend γ) t = deriv f (Path.extend γ t) • deriv (Path.extend γ) t := by
      aesop
    rw [integral_congr this]
    have : ∀ t ∈ (Set.uIcc 0 1), deriv f (Path.extend γ t) • deriv (Path.extend γ) t = deriv (f ∘ (Path.extend γ)) t := by
      aesop
    rw [integral_congr this]
    rw [integral_deriv_eq_sub hf_deriv h_int]
    simp
    rw [hγ_closed]
    simp
