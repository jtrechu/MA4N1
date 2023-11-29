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

noncomputable def aux (x y : ℂ ) (f : ℂ → ℂ) (γ : Path x y) : ℝ  → ℂ :=
 (Function.comp f (Path.extend γ)) * (deriv (Path.extend γ))

noncomputable def pathIntegral1 (x y : ℂ ) (f : ℂ → ℂ) (γ : Path x y) : ℂ :=  
∫t in (0)..(1), (aux x y f γ)  t ∂volume

noncomputable def length (x y : ℂ ) (γ : Path x y) : ℝ :=
∫ t in (0)..(1), Complex.abs ((deriv (Path.extend γ)) t) ∂volume

end definitions


namespace basic_properties
open definitions

--- Here we show that the Path Integral is additive over the function: 
--- ∫_γ f + ∫_γ g = ∫_γ (f + g)

lemma pathIntegral_function_additivity (x y : ℂ ) (f g : ℂ → ℂ) (γ : Path x y) 
(haux₁: IntervalIntegrable (aux x y f γ) volume 0 1) 
(haux₂: IntervalIntegrable (aux x y g γ) volume 0 1): 
(pathIntegral1 x y f γ) + (pathIntegral1 x y g γ) = (pathIntegral1 x y (f+g) γ) := by 
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

--- Here we show that the Path Integral is additive over the path: 
--- ∫_γ f +∫_α f  = ∫_(γ⬝α) f :

--- First we show a few basic results about Path.trans to make it 
--- easier to work with it afterwards 

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

--- Now we prove the actual result

lemma pathIntegral_path_additivity {x y z : ℂ} (f : ℂ → ℂ) (γ : Path x y) (α : Path y z)
  (haux₁: IntervalIntegrable (aux x y f γ) volume 0 1)
  (haux₂: IntervalIntegrable (aux y z f α) volume 0 1):
  (pathIntegral1 x y f γ) + (pathIntegral1 y z f α) = (pathIntegral1 x z f (Path.trans γ α)) := by 
  unfold pathIntegral1 
  have r : ∫ (t : ℝ) in (0)..(1/2), aux x z f (Path.trans γ α) t  = ∫ (t : ℝ) in (0)..(1) , 1/2 * aux x z f (Path.trans γ α) (t*(1/2)) := by
    have r₁ : ∫ (t : ℝ) in (0*(1/2))..(1*(1/2)), aux x z f (Path.trans γ α) t  = ∫ (t : ℝ) in (0)..(1) , 1/2 * aux x z f (Path.trans γ α) (t*(1/2)) := by 
      rw[intervalIntegral.integral_const_mul]
      rw[← intervalIntegral.smul_integral_comp_mul_right]
      aesop
    have r₂ : ∫ (t : ℝ) in (0)..(1/2), aux x z f (Path.trans γ α) t  = ∫ (t : ℝ) in (0*(1/2))..(1*(1/2)), aux x z f (Path.trans γ α) t:= by simp
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
  have first_half : ∫(t:ℝ) in (0)..(1), 1/2 * aux x z f (Path.trans γ α) (t*(1/2)) = ∫ (t : ℝ) in (0)..(1), aux x y f γ t := by
    unfold aux
    have: ∫ (t : ℝ) in (0)..(1), (f ∘ Path.extend γ * deriv (Path.extend γ)) t = ∫ (t : ℝ) in (0)..(1), (f ∘ Path.extend γ) (t) *(deriv (Path.extend γ) t) ∂volume := by
      simp
    rw[this,←u]
    have: ∀ t ∈ (Set.uIcc 0 1), 1 / 2 * (f ∘ Path.extend (Path.trans γ α) * deriv (Path.extend (Path.trans γ α))) (t * (1 / 2)) =  (f ∘ Path.extend (Path.trans γ α)) (t * (1 / 2)) * (1 / 2 * deriv (Path.extend (Path.trans γ α)) (t * 1 / 2)) := by
      intro t ht
      simp
      ring_nf
    rw[integral_congr this]
  
  have l : ∫ (t : ℝ) in (1/2)..(1), aux x z f (Path.trans γ α) t  = ∫ (t : ℝ) in (0)..(1) , 1/2 * aux x z f (Path.trans γ α) (1/2*t + 1/2) := by
    have l₁ : ∫ (t : ℝ) in ((1/2)*0 + (1/2))..((1/2)*1+ (1/2)), aux x z f (Path.trans γ α) t  = ∫ (t : ℝ) in (0)..(1) , 1/2 * aux x z f (Path.trans γ α) ((1/2)*t+1/2) := by 
      rw[intervalIntegral.integral_const_mul]
      rw[←intervalIntegral.smul_integral_comp_mul_add]
      simp
    have l₂ : ∫ (t : ℝ) in (1/2)..(1), aux x z f (Path.trans γ α) t  = ∫ (t : ℝ) in ((1/2)*0 + (1/2))..((1/2)*1+ (1/2)), aux x z f (Path.trans γ α) t := by ring_nf
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
  have second_half : ∫(t:ℝ) in (0)..(1), 1/2 * aux x z f (Path.trans γ α) (1/2*t+1/2) = ∫ (t : ℝ) in (0)..(1), aux y z f α t := by
    unfold aux
    have: ∫ (t : ℝ) in (0)..(1), (f ∘ Path.extend α * deriv (Path.extend α )) t = ∫ (t : ℝ) in (0)..(1), (f ∘ Path.extend α) (t) *(deriv (Path.extend α) t) ∂volume := by
      simp
    rw[this,←o]
    have: ∀ t ∈ (Set.uIcc 0 1), 1 / 2 * (f ∘ Path.extend (Path.trans γ α) * deriv (Path.extend (Path.trans γ α))) (1/2*t+1/2) =  (f ∘ Path.extend (Path.trans γ α)) (1/2*t+1/2) * (1 / 2 * deriv (Path.extend (Path.trans γ α)) (1/2*t+1/2)) := by
      intro t ht
      simp
      ring_nf
    rw[integral_congr this]
  have q : ∫ (t:ℝ) in (0)..(1), aux x z f (Path.trans γ α) t ∂volume = ∫ (t:ℝ) in (0)..(1/2), aux x z f (Path.trans γ α) t ∂volume + ∫ (t:ℝ) in (1/2)..(1), aux x z f (Path.trans γ α) t ∂volume := by
    sorry
  rw[q,r,l,first_half,second_half]



--- We'll now show that doing an integral over the symmetric path is 
--- equivalent to changing the sign of the integral:

--- Like before we first show a basic result of Path.trans to make it 
--- easier to work with it

lemma symm_helper {x y : ℂ} (γ : Path x y) (t: ℝ) (ht: t ∈ I ):
Path.symm γ ⟨t, by exact ht⟩ = γ ⟨ 1-t, by aesop⟩ := by
rw[Path.symm_apply]
aesop

--- Now we prove the actual result

lemma pathIntSymm {x y : ℂ } (f: ℂ → ℂ) (γ : Path x y) :
(pathIntegral1 y x f (Path.symm γ)) = -(pathIntegral1 x y f γ) := by 
unfold pathIntegral1
have a : ∀ t ∈ I, f (Path.extend (Path.symm γ) t) = f (Path.extend γ (1 - t)) := by
  intro t ht
  have h : 1-t ∈ I := by aesop
  rw[Path.extend_extends (Path.symm γ) ht]
  rw[Path.extend_extends γ h]
  rw[symm_helper]
have b : ∫ (t : ℝ) in (0)..(1), aux x y f γ t  ∂volume  = ∫ (t : ℝ) in (0)..(1), aux x y f γ (1+(-1*t)) ∂volume := by
  rw[intervalIntegral.integral_comp_add_mul]
  ring_nf
  rw[intervalIntegral.integral_symm]
  aesop
  norm_num
have c : ∫ (t : ℝ) in (0)..(1), aux x y f γ t  ∂volume  = ∫ (t : ℝ) in (0)..(1), aux x y f γ (1-t) ∂volume := by
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

end basic_properties
