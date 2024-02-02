import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Cauchy.old_files.path_integrals
import Cauchy.old_files.path_integrals

open definitions intervalIntegral MeasureTheory unitInterval helpers

--This file proved that going through a path in opposite direction only affected
-- the path integral by changing the sign. (For the Path library not C1Paths)

lemma pathIntegral_antisymmetric {x y : ℂ } (f: ℂ → ℂ) (γ : Path x y) :
(pathIntegral1 f (Path.symm γ)) = -(pathIntegral1 f γ) := by
unfold pathIntegral1
have a : ∀ t ∈ I, f (Path.extend (Path.symm γ) t) = f (Path.extend γ (1 - t)) := by
  intro t ht
  have h : 1-t ∈ I := by aesop
  rw[Path.extend_extends (Path.symm γ) ht]
  rw[Path.extend_extends γ h]
  rw[symm_helper]
have b : ∫ (t : ℝ) in (0)..(1), aux f γ t  ∂volume  = ∫ (t : ℝ) in (0)..(1), aux f γ (1+(-1*t)) ∂volume := by
  rw[intervalIntegral.integral_comp_add_mul]
  ring_nf
  rw[intervalIntegral.integral_symm]
  aesop
  norm_num
have c : ∫ (t : ℝ) in (0)..(1), aux f γ t  ∂volume  = ∫ (t : ℝ) in (0)..(1), aux f γ (1-t) ∂volume := by
  rw[b]
  ring_nf
rw[c]
unfold aux
have d : ∀ t ∈ (Set.uIcc 0 1), deriv (Path.extend (Path.symm γ)) t = - deriv (Path.extend γ) (1 - t) := by sorry
simp
have: ∀ t ∈ (Set.uIcc 0 1), f (Path.extend (Path.symm γ) t) * deriv (Path.extend (Path.symm γ)) t = - (f (Path.extend γ (1 - t)) * deriv (Path.extend γ) (1 - t)) := by
  intro t ht
  rw[a]
  rw[d]
  ring
  exact ht
  aesop
rw[←intervalIntegral.integral_neg]
rw[integral_congr this]
