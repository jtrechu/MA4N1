import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Cauchy.definitions.path_integrals



open unitInterval Set

--- First we show a few basic results about Path.trans to make it
--- easier to work with it afterwards

namespace helpers

lemma u : 1/2 ∈ I := by norm_num

lemma trans_helper1 {x y z : ℂ} (γ : Path x y) (α : Path y z) (t: ℝ) (h: t ∈ I ):
Path.trans γ α ⟨t*(1/2), by exact unitInterval.mul_mem h u⟩  = γ ⟨ t, by exact h⟩ := by
have h₁ : 1/2*t ≤ 1/2 := by
  simp at h
  have ⟨_, b⟩ := h
  linarith
rw[Path.trans_apply]
split_ifs
· simp
  ring_nf
·  exfalso
   aesop

lemma basic (t : ℝ) (h: t ∈ I): 1/2*t + 1/2 ∈ I := by
have ⟨a,b⟩ := h
have h₁ : 1/2*t + 1/2 ≤ 1 := by linarith
have h₂ : 0 ≤ 1/2*t +1/2 := by linarith
norm_num
exact ⟨h₂,h₁⟩

lemma trans_helper2 {x y z : ℂ} (γ : Path x y) (α : Path y z) (t: ℝ) (ht: t ∈ I ):
Path.trans γ α ⟨1/2*t+1/2 , by exact basic t ht⟩  = α ⟨ t, by exact ht⟩ := by
have h₁ : 1/2*t + 1/2 ≥ 1/2 := by
  simp at ht
  linarith
rw[Path.trans_apply]
split_ifs
aesop
·cases eq_or_lt_of_le h with
| inl h =>
    simp at h
    ring_nf
    rename_i h_1
    aesop_subst h
    simp_all only [le_refl, add_zero, Icc.mk_one, Path.target, Icc.mk_zero, Path.source]
| inr h =>
    exfalso
    aesop
    have basic: 0 < (2:ℝ)  := by norm_num
    have h3 : 2⁻¹*t*2 < 0*2:= by exact  mul_lt_mul_of_pos_right h basic
    ring_nf at h3
    rw[← not_le] at h3
    simp_all only
. ring_nf

lemma symm_helper {x y : ℂ} (γ : Path x y) (t: ℝ) (ht: t ∈ I ):
Path.symm γ ⟨t, by exact ht⟩ = γ ⟨ 1-t, by aesop⟩ := by
rw[Path.symm_apply]
aesop

lemma path_extend_product_rule {x y z : ℂ} (γ : Path x y) (α : Path y z) :
  ∀ t ∈ I,  1/2 * deriv (Path.extend (Path.trans γ α)) (t * (1/2)) =  deriv (Path.extend γ) t := by
  intro t tI
  have t := deriv.comp (h := Path.extend (Path.trans γ α)) (h₂ := λ t₁ =>  (1/2) * t₁)
  have composition : 1/2 * deriv (Path.extend (Path.trans γ α)) (t * (1/2)) = deriv ((λ t₁ => Path.extend (Path.trans γ α) t₁) ∘ λ t₁ =>  (1/2) * t₁) t := by

    rewrite [ ]
  rewrite [←deriv.comp]
  sorry
