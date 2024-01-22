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
import Mathlib.Topology.ContinuousOn

import Cauchy.definitions.path_integrals
import Cauchy.definitions.triangle

import Cauchy.integral_zero._1_triangle_sequence

open definitions

namespace fun_g


variable {U : Set ℂ}


noncomputable def g_aux (f : ℂ → ℂ) (z :ℂ) : ℂ → ℂ := fun w => if w == z then deriv f z else (f w - f z)/(w-z)



lemma denom_is_differentiable  {z : ℂ} : DifferentiableOn ℂ (fun w => w-z) (U\{z}) := by
have hconst : DifferentiableOn ℂ (fun _ => -z) (U\{z}) := by exact differentiableOn_const (-z)
have hid : DifferentiableOn ℂ (fun w => w) (U\{z}) := by exact differentiableOn_id
apply DifferentiableOn.add hid hconst

lemma denom_is_continuous {z : ℂ} : ContinuousOn (fun w => w-z) (U\{z}) := by
apply (DifferentiableOn.continuousOn (denom_is_differentiable))

lemma hnot0 (z:ℂ): ∀ w ∈ (U\{z}), (fun w => w-z) w ≠ 0 := by
  intro x hx
  aesop
  rw[←ne_eq x z] at right
  have h1 : z = x := by calc _ = z + (x -z) := by rw[a]
                                                  ring
                              _ = x := by ring
  aesop_subst h1
  simp_all only [ne_eq, not_true]

lemma differentiable_g {U: Set ℂ}(f : ℂ → ℂ) (z : ℂ) (hf : DifferentiableOn ℂ f U) : DifferentiableOn ℂ (g_aux f z) (U\{z}):= by
have h1: ∀ x ∈ (U\{z}), g_aux f z x =  (f x - f z)/(x-z)  := by
  intro x hx
  unfold g_aux
  aesop
apply (differentiableOn_congr h1).2
have : U\{z} ⊆ U := by simp_all only [Set.mem_diff, Set.mem_singleton_iff, ne_eq, and_imp,
                           Set.diff_singleton_subset_iff, Set.subset_insert]
have : DifferentiableOn ℂ f (U\{z}) := by exact (DifferentiableOn.mono  hf this)
have : DifferentiableOn ℂ (fun w => f w - f z) (U\{z}) := by
  have trivial :  DifferentiableOn ℂ (fun _ =>- f z) (U\{z}) := by exact (differentiableOn_const (-f z))
  apply DifferentiableOn.add this trivial
apply (DifferentiableOn.div this denom_is_differentiable (hnot0 z))

lemma g_cont_notz {U: Set ℂ}(f : ℂ → ℂ) (z : ℂ) (hf : DifferentiableOn ℂ f U) :  ContinuousOn (g_aux f z) (U\{z}) :=
by apply (DifferentiableOn.continuousOn (differentiable_g f z hf))

lemma fcont (f:ℂ→ℂ) (hf : DifferentiableOn ℂ f U) : ContinuousOn f U := by apply (DifferentiableOn.continuousOn (hf))

lemma U_Punctured_Open (hU : IsCDomain U) : IsOpen (U\{z}) := by
have hU : IsOpen U := by
  unfold IsCDomain at hU
  exact hU.1
have hz : IsOpen {z}ᶜ  := by exact isOpen_compl_singleton
apply IsOpen.inter hU hz



lemma continuous_g (hU : IsCDomain U) (f : ℂ → ℂ) (z : ℂ) (hz: z ∈ U) (hf : DifferentiableOn ℂ f U) : ContinuousOn (g_aux f z) U  := by
unfold ContinuousOn
intro x xU
by_cases (x ∈ U\{z})
have a:=(g_cont_notz f z hf)
rw[ IsOpen.continuousOn_iff (U_Punctured_Open hU)] at a
apply ContinuousAt.continuousWithinAt
apply a
exact h
have hx : x = z := by simp_all only [not_true, Set.mem_diff, Set.mem_singleton_iff, true_and, not_not]
rw[Metric.continuousWithinAt_iff]
have hg : g_aux f z x = deriv f z:= by
  rw[hx]
  unfold g_aux
  simp
rw[hg]
rw[hx]
unfold g_aux
have hDif:  DifferentiableAt ℂ f z  := by
  apply DifferentiableOn.differentiableAt hf
  apply IsOpen.mem_nhds
  unfold IsCDomain at hU
  exact hU.1
  exact hz
apply DifferentiableAt.hasDerivAt at hDif
rw[HasDerivAt.deriv hDif]
rw[hasDerivAt_iff_isLittleO] at hDif
sorry
