import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Cauchy.old_files.path_integrals
import Cauchy.old_files.path_integrals
import Cauchy.old_files.dpath_integrals

open oldDefinitions intervalIntegral MeasureTheory unitInterval helpers

-- Here we show that the Path Integral is additive over the path:
-- ∫_γ f +∫_α f  = ∫_(γ⬝α) f :
-- This was done for the Path Library, before the C1Paths were created
lemma pathIntegral_path_additivity {x y z : ℂ} (f : ℂ → ℂ) (γ : Path x y) (α : Path y z)
  (haux₁: IntervalIntegrable (aux f γ) volume 0 1)
  (haux₂: IntervalIntegrable (aux f α) volume 0 1):
  (pathIntegral1 f γ) + (pathIntegral1 f α) = (pathIntegral1 f (Path.trans γ α)) := by
  unfold pathIntegral1
  have r : ∫ (t : ℝ) in (0)..(1/2), aux f (Path.trans γ α) t  = ∫ (t : ℝ) in (0)..(1) , 1/2 * aux f (Path.trans γ α) (t*(1/2)) := by
    have r₁ : ∫ (t : ℝ) in (0*(1/2))..(1*(1/2)), aux f (Path.trans γ α) t  = ∫ (t : ℝ) in (0)..(1) , 1/2 * aux f (Path.trans γ α) (t*(1/2)) := by
      rw[intervalIntegral.integral_const_mul]
      rw[← intervalIntegral.smul_integral_comp_mul_right]
      aesop
    have r₂ : ∫ (t : ℝ) in (0)..(1/2), aux f (Path.trans γ α) t  = ∫ (t : ℝ) in (0*(1/2))..(1*(1/2)), aux f (Path.trans γ α) t:= by simp
    rw[r₂,r₁]
  have s : ∀ t ∈ I ,  (Path.extend (Path.trans γ α)) (t*(1/2)) = Path.extend γ t:= by
    intro t ht
    have h12 : t*(1/2) ∈ I := by exact unitInterval.mul_mem ht u
    rw[Path.extend_extends (Path.trans γ α) h12]
    rw[Path.extend_extends γ ht]
    apply trans_helper1
  have s : ∀ t ∈ I,  1/2 * deriv (Path.extend (Path.trans γ α)) (t * (1/2)) =  deriv (Path.extend γ) t := by
    intro t ht
    simp
    sorry
  have: ∀ t ∈  (Set.uIcc 0 1),  (f∘Path.extend (Path.trans γ α)) (t*(1/2))*(1/2 * deriv (Path.extend (Path.trans γ α)) (t * 1/2)) = (f ∘ Path.extend γ) (t) *(deriv (Path.extend γ) t) := by
    aesop
  have u : ∫(t:ℝ) in (0)..(1),  (f ∘ Path.extend (Path.trans γ α)) (t*(1/2))*(1/2 * deriv (Path.extend (Path.trans γ α)) (t * 1/2)) ∂volume  =  ∫ (t : ℝ) in (0)..(1), (f ∘ Path.extend γ) (t) *(deriv (Path.extend γ) t) ∂volume := by
    rw[integral_congr this]
  have first_half : ∫(t:ℝ) in (0)..(1), 1/2 * aux f (Path.trans γ α) (t*(1/2)) = ∫ (t : ℝ) in (0)..(1), aux f γ t := by
    unfold aux
    have: ∫ (t : ℝ) in (0)..(1), (f ∘ Path.extend γ * deriv (Path.extend γ)) t = ∫ (t : ℝ) in (0)..(1), (f ∘ Path.extend γ) (t) *(deriv (Path.extend γ) t) ∂volume := by
      simp
    rw[this,←u]
    have: ∀ t ∈ (Set.uIcc 0 1), 1 / 2 * (f ∘ Path.extend (Path.trans γ α) * deriv (Path.extend (Path.trans γ α))) (t * (1 / 2)) =  (f ∘ Path.extend (Path.trans γ α)) (t * (1 / 2)) * (1 / 2 * deriv (Path.extend (Path.trans γ α)) (t * 1 / 2)) := by
      intro t ht
      simp
      ring_nf
    rw[integral_congr this]

  have l : ∫ (t : ℝ) in (1/2)..(1), aux f (Path.trans γ α) t  = ∫ (t : ℝ) in (0)..(1) , 1/2 * aux f (Path.trans γ α) (1/2*t + 1/2) := by
    have l₁ : ∫ (t : ℝ) in ((1/2)*0 + (1/2))..((1/2)*1+ (1/2)), aux f (Path.trans γ α) t  = ∫ (t : ℝ) in (0)..(1) , 1/2 * aux f (Path.trans γ α) ((1/2)*t+1/2) := by
      rw[intervalIntegral.integral_const_mul]
      rw[←intervalIntegral.smul_integral_comp_mul_add]
      simp
    have l₂ : ∫ (t : ℝ) in (1/2)..(1), aux f (Path.trans γ α) t  = ∫ (t : ℝ) in ((1/2)*0 + (1/2))..((1/2)*1+ (1/2)), aux f (Path.trans γ α) t := by ring_nf
    rw[l₂,l₁]

  have v : ∀ t ∈ I ,  (Path.extend (Path.trans γ α)) (1/2*t+1/2) = Path.extend α t:= by
    intro t ht
    have h22 : 1/2*t+1/2 ∈ I := by
      have ⟨a,b⟩ := ht
      have h₁ : 1/2*t + 1/2 ≤ 1 := by linarith
      have h₂ : 0 ≤ 1/2*t +1/2 := by linarith
      norm_num
      exact ⟨h₂,h₁⟩
    rw[Path.extend_extends (Path.trans γ α) h22]
    rw[Path.extend_extends α ht]
    apply trans_helper2

  have w : ∀ t ∈ I,  1/2 * deriv (Path.extend (Path.trans γ α)) (1/2*t+1/2) =  deriv (Path.extend α) t := by
    intro t ht
    simp
    sorry
  have: ∀ t ∈  (Set.uIcc 0 1),  (f∘Path.extend (Path.trans γ α)) (1/2*t+1/2)*(1/2 * deriv (Path.extend (Path.trans γ α)) (1/2*t+1/2)) = (f ∘ Path.extend α) (t) *(deriv (Path.extend α) t) := by
    aesop
  have o : ∫(t:ℝ) in (0)..(1),  (f∘Path.extend (Path.trans γ α)) (1/2*t+1/2)*(1/2 * deriv (Path.extend (Path.trans γ α)) (1/2*t+1/2)) ∂volume  =  ∫ (t : ℝ) in (0)..(1), (f ∘ Path.extend α) (t) *(deriv (Path.extend α) t) ∂volume := by
    rw[integral_congr this]
  have second_half : ∫(t:ℝ) in (0)..(1), 1/2 * aux f (Path.trans γ α) (1/2*t+1/2) = ∫ (t : ℝ) in (0)..(1), aux f α t := by
    unfold aux
    have: ∫ (t : ℝ) in (0)..(1), (f ∘ Path.extend α * deriv (Path.extend α )) t = ∫ (t : ℝ) in (0)..(1), (f ∘ Path.extend α) (t) *(deriv (Path.extend α) t) ∂volume := by
      simp
    rw[this,←o]
    have: ∀ t ∈ (Set.uIcc 0 1), 1 / 2 * (f ∘ Path.extend (Path.trans γ α) * deriv (Path.extend (Path.trans γ α))) (1/2*t+1/2) =  (f ∘ Path.extend (Path.trans γ α)) (1/2*t+1/2) * (1 / 2 * deriv (Path.extend (Path.trans γ α)) (1/2*t+1/2)) := by
      intro t ht
      simp
      ring_nf
    rw[integral_congr this]
  have q : ∫ (t:ℝ) in (0)..(1), aux f (Path.trans γ α) t ∂volume = ∫ (t:ℝ) in (0)..(1/2), aux f (Path.trans γ α) t ∂volume + ∫ (t:ℝ) in (1/2)..(1), aux f (Path.trans γ α) t ∂volume := by
    sorry
  rw[q,r,l,first_half,second_half]
