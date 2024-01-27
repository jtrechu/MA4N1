import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Cauchy.definitions.triangle
import Cauchy.definitions.subtriangle
import Cauchy.definitions.path_integrals
import Cauchy.definitions.domain
import Cauchy.helpers.triangle
import Cauchy.lemmas.zero_le_of_gt_zero


open definitions unitInterval

namespace definitions

lemma helperCircleR : Differentiable ℝ (fun (θ:ℝ) => ↑θ * Complex.I*2*Real.pi) := by
    apply Differentiable.mul
    apply Differentiable.mul
    apply Differentiable.mul
    exact Complex.differentiable_coe
    any_goals apply differentiable_const


lemma auxCircle (c:ℂ) (R:ℝ) :  Differentiable ℝ (fun θ:ℝ => c + ↑R * Complex.exp (↑θ * Complex.I*2*Real.pi)) := by
apply Differentiable.add
exact differentiable_const c
apply Differentiable.mul
exact differentiable_const (↑R:ℂ)
have h2 : Differentiable ℝ (fun (θ:ℝ) =>  Complex.exp (↑θ * Complex.I*2*Real.pi)):= by
    apply (Differentiable.cexp helperCircleR)
exact h2


noncomputable def funct1 : ℝ → ℂ := fun x => x * Complex.I * 2 * Real.pi
noncomputable def funct2 : ℝ → ℂ := fun x => x * Complex.I

lemma auxCircle' (x:ℝ) (c:ℂ) (R:ℝ) : deriv (fun θ:ℝ => c + ↑R * Complex.exp (↑θ * Complex.I*2*Real.pi)) x = (fun (θ:ℝ) =>(Complex.I*2*Real.pi)* (↑R:ℂ) * Complex.exp (↑θ * Complex.I*2*Real.pi)) x:= by
have h1 : (fun θ:ℝ => Complex.exp (↑θ * Complex.I*2*Real.pi)) = (Complex.exp ∘ funct1) := by
  unfold funct1
  aesop
simp_all only [differentiableAt_const, deriv_const_add', deriv_const_mul_field']
rw[deriv.comp]
rw[Complex.deriv_exp]
have h2: deriv funct1 x = Complex.I*2*Real.pi := by
  unfold funct1
  repeat rw[deriv_mul_const]
  rw[Complex.deriv_coe]
  ring_nf
  norm_num
  apply Complex.differentiable_coe
  apply Differentiable.mul
  apply Complex.differentiable_coe
  exact differentiable_const Complex.I
  repeat apply Differentiable.mul
  apply Complex.differentiable_coe
  any_goals apply differentiable_const
rw[h2]
unfold funct1
ring
unfold funct1
apply  Differentiable.differentiableAt
exact Complex.differentiable_exp
unfold funct1
repeat apply DifferentiableAt.mul
apply  Differentiable.differentiableAt
exact Complex.differentiable_coe
any_goals apply differentiableAt_const


lemma auxCircle''' (x:ℝ) : deriv (fun x => Complex.exp (↑x * Complex.I)) x = Complex.I * Complex.exp (x*Complex.I) := by
have h1 : (fun θ:ℝ => Complex.exp (θ * Complex.I)) = (Complex.exp ∘ funct2) := by
  unfold funct2
  aesop
simp_all only [differentiableAt_const, deriv_const_add', deriv_const_mul_field']
rw[deriv.comp]
rw[Complex.deriv_exp]
have h2: deriv funct2 x = Complex.I := by
  unfold funct2
  repeat rw[deriv_mul_const]
  ring_nf
  norm_num
  rw[Complex.deriv_coe x]
  ring
  apply Differentiable.differentiableAt
  exact Complex.differentiable_coe
rw[h2]
unfold funct2
ring
unfold funct2
apply  Differentiable.differentiableAt
exact Complex.differentiable_exp
unfold funct2
repeat apply DifferentiableAt.mul
apply  Differentiable.differentiableAt
any_goals apply differentiableAt_const
exact Complex.differentiable_coe

lemma auxCircle''  (R:ℝ) : Continuous  (fun (θ:ℝ) =>(Complex.I*2*Real.pi)* (↑R:ℂ) * Complex.exp (↑θ * Complex.I*2*Real.pi)) := by
apply Continuous.mul
exact continuous_const
have h1 : (fun θ:ℝ => Complex.exp (↑θ * Complex.I*2*Real.pi)) = (Complex.exp ∘ funct1) := by
  unfold funct1
  aesop
rw[h1]
apply Continuous.comp
apply Complex.continuous_exp
unfold funct1
repeat apply Continuous.mul
have h2 : Differentiable ℝ (fun x:ℝ => (↑x:ℂ)) := by
  apply Complex.differentiable_coe
apply Differentiable.continuous at h2
exact h2
any_goals exact continuous_const



noncomputable def circlePath (c: ℂ) (R : ℝ) : C1Path := {
  toFun := fun θ:ℝ => c + ↑R * Complex.exp (↑θ * Complex.I*2*Real.pi)
  open_cover := {
      set := Set.univ
      h := ⟨isOpen_univ, Set.subset_univ I⟩
    }
  differentiable_toFun := by
    apply Differentiable.differentiableOn
    exact (auxCircle c R)
  continuous_deriv_toFun := by
         conv => {
          arg 1; intro x
          rewrite [auxCircle']}
         apply Continuous.continuousOn
         exact (auxCircle'' R)
}
