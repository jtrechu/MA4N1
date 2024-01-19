import Cauchy.definitions.triangle
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic
import Cauchy.lemmas.triangle_inequality
import Cauchy.lemmas.complex_real_norm_equiv
import Cauchy.lemmas.path_integral_integrable
import Cauchy.theorems.integral_restriction
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

-- Maybe there are more imports than what we actually need for this lemma, but it doesn't matter
-- I'll have another look at it and remove all the unnecesary imports

open definitions lemmas theorems

open Set
open Nat Real MeasureTheory Set Filter Function intervalIntegral Interval unitInterval

lemma aux3 {f : ℂ → ℂ} {γ : C1Path}
   (hf : DifferentiableAt ℝ (f ∘ γ) x) :
    DifferentiableAt ℂ f (γ x) := by
  sorry

lemma complex_ftc1 {f : ℂ → ℂ} (γ : C1Path)
    (hf_deriv : ∀ x ∈ (Set.uIcc 0 1), DifferentiableAt ℝ (f ∘ γ) x)
    (hγ_deriv : ∀ x ∈ (Set.uIcc 0 1), DifferentiableAt ℝ γ x)
    (h_int : IntervalIntegrable (deriv (f ∘ γ)) volume 0 1) :
    pathIntegral1' (deriv f) γ = f (γ 1) - f (γ 0) := by
  have : ∀ y ∈ (Set.uIcc 0 1), deriv f (γ y) * deriv γ y = deriv (f ∘ γ) y := by
    intro y hy
    rw [deriv.comp]
    · exact aux3 (hf_deriv y hy)
    · exact hγ_deriv y hy
  unfold pathIntegral1'
  unfold aux
  simp
  rw [integral_congr this, integral_deriv_eq_sub hf_deriv h_int]
  trivial

lemma complex_ftc' {f : ℂ → ℂ} {F : ℂ → ℂ} {U : Set ℂ} {γ : C1Path} (hU : IsOpen U) (hγ : γ '' I ⊆ U)
  (hf : DifferentiableOn ℂ f U) (hF : DifferentiableOn ℂ F U) (hfs : deriv F = f) :
  pathIntegral1' f γ = F (γ 1) - F (γ 0) := by
  have diff_F (x : I) : DifferentiableAt ℂ F (C1Path.toFun γ ↑x) := by
    apply DifferentiableOn.differentiableAt hF
    rewrite[mem_nhds_iff]
    refine ⟨U, by rfl, hU, ?_⟩
    aesop
  have diff_g (x : I) : DifferentiableAt ℝ γ.toFun ↑x := by
    apply DifferentiableOn.differentiableAt γ.differentiable_toFun
    rewrite [mem_nhds_iff]
    refine ⟨γ.open_cover, by rfl, γ.open_cover.h.1, ?_⟩
    apply Set.mem_of_subset_of_mem
    exact γ.open_cover.h.2
    aesop
  unfold pathIntegral1' aux
  rewrite [integral_restriction]
  conv_lhs => {
    arg 1; intro t; arg 1; intro t; simp;
    tactic => {
      conv_lhs => {
        rewrite [←hfs, ←deriv.comp]
        rfl
        exact diff_F t
        exact diff_g t
      }
    }
  }
  have : ∫ (t : ℝ) in (0)..(1), function_extension (fun (t : I) => deriv (F ∘ γ.toFun) ↑t) t =
         ∫ (t : ℝ) in (0)..(1), deriv (F ∘ γ.toFun) t := by
    apply intervalIntegral.integral_congr
    unfold function_extension Set.EqOn
    aesop
  rewrite [this, integral_deriv_eq_sub]

  aesop
  . intro x hx
    simp at hx
    apply DifferentiableAt.comp
    exact DifferentiableAt.restrictScalars ℝ $ diff_F ⟨x, hx⟩
    exact diff_g ⟨x, hx⟩
  . apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    rewrite [continuousOn_iff_continuous_restrict]
    conv => {
      arg 1; intro x; simp;
      apply deriv.comp
      exact diff_F x
      exact diff_g x
    }
    apply Continuous.mul
    rewrite [hfs]
    apply ContinuousOn.comp_continuous
    exact DifferentiableOn.continuousOn hf
    have c := DifferentiableOn.continuousOn γ.differentiable_toFun
    have d := ContinuousOn.mono c γ.open_cover.h.2
    rewrite [continuousOn_iff_continuous_restrict] at d
    conv at d => {
      arg 1; intro x;
      rewrite [Set.restrict_apply]
    }
    exact d
    aesop
    have d := ContinuousOn.mono γ.continuous_deriv_toFun γ.open_cover.h.2
    rewrite [continuousOn_iff_continuous_restrict] at d
    conv at d => {
      arg 1; intro x;
      rewrite [Set.restrict_apply]
    }
    exact d
  exact zero_le_one

lemma aux2 {z w : ℂ} {f : ℂ → ℂ} {γ : Path z w} (hf : DifferentiableAt ℝ (f ∘ (Path.extend γ)) x) :
           DifferentiableAt ℂ f ((Path.extend γ) x) := by
  sorry

--lemma complex_ftc2 (z w : ℂ) (f : ℂ → ℂ) (γ : Path z w)
--     (hf_deriv : ∀ x ∈ (Set.uIcc 0 1), DifferentiableAt ℝ (f ∘ (Path.extend γ)) x)
--     (hγ_deriv : ∀ x ∈ (Set.uIcc 0 1), DifferentiableAt ℝ (Path.extend γ) x)
--     (h_int : IntervalIntegrable (deriv (f ∘ (Path.extend γ))) volume 0 1) :
--     pathIntegral1' (deriv f) γ = (f ∘ (Path.extend γ)) 1 - (f ∘ (Path.extend γ)) 0 := by
--     unfold pathIntegral1
--     unfold aux
--     have : ∀ y ∈ (Set.uIcc 0 1),(deriv f ∘ Path.extend γ * deriv (Path.extend γ)) y = deriv (f ∘ (Path.extend γ)) y := by
--       intro y hy
--       rw [deriv.comp]
--       simp
--       · exact aux2 (hf_deriv y hy)
--       · exact hγ_deriv y hy
--     rw [integral_congr this, integral_deriv_eq_sub hf_deriv h_int]
