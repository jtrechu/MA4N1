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


lemma helperCircleR : Differentiable ℝ (fun (θ:ℝ) => ↑θ * Complex.I) := by
    have h11 : Differentiable ℝ (fun _:ℝ => Complex.I) := by simp_all only [differentiable_const]
    apply Differentiable.mul
    exact Complex.differentiable_coe
    exact h11


lemma auxCircle (c:ℂ) (R:ℝ) :  Differentiable ℝ (circleMap c R) := by
unfold circleMap
apply Differentiable.add
exact differentiable_const c
apply Differentiable.mul
exact differentiable_const (↑R:ℂ)
have h2 : Differentiable ℝ (fun (θ:ℝ) =>  Complex.exp (↑θ * Complex.I)):= by
    apply (Differentiable.cexp helperCircleR)
exact h2


def funct1 : ℝ → ℂ := (fun x => x*Complex.I)

lemma auxCircle' (x:ℝ) (c:ℂ) (R:ℝ) : deriv (circleMap c R) x = (fun (θ:ℝ) =>(Complex.I)* (↑R:ℂ) * Complex.exp (↑θ * Complex.I)) x:= by
unfold circleMap
have h1 : (fun θ:ℝ => Complex.exp (↑θ * Complex.I)) = (Complex.exp ∘ funct1) := by
  unfold funct1
  aesop
aesop
rw[deriv.comp]
rw[Complex.deriv_exp]
have h2: deriv funct1 x = Complex.I := by
  unfold funct1
  rw[deriv_mul_const]
  rw[Complex.deriv_coe]
  ring_nf
  apply Complex.differentiable_coe
rw[h2]
unfold funct1
ring
unfold funct1
apply  Differentiable.differentiableAt
exact Complex.differentiable_exp
unfold funct1
apply DifferentiableAt.mul
apply  Differentiable.differentiableAt
exact Complex.differentiable_coe
exact differentiableAt_const Complex.I

lemma auxCircle''  (R:ℝ) : Continuous  (fun (θ:ℝ) =>(Complex.I)* (↑R:ℂ) * Complex.exp (↑θ * Complex.I)) := by
apply Continuous.mul
exact continuous_const
have h1 : (fun θ:ℝ => Complex.exp (↑θ * Complex.I)) = (Complex.exp ∘ funct1) := by
  unfold funct1
  aesop
rw[h1]
apply Continuous.comp
apply Complex.continuous_exp
unfold funct1
apply Continuous.mul
have h2 : Differentiable ℝ (fun x:ℝ => (↑x:ℂ)) := by
  apply Complex.differentiable_coe
apply Differentiable.continuous at h2
exact h2
exact continuous_const



noncomputable def circlePath (c: ℂ) (R : ℝ) : C1Path := {
  toFun := circleMap c R
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
