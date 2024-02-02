import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.UnitInterval
import Cauchy.definitions.path_integrals

namespace helpers

--Work done on linear paths prior to the change to C1 Paths

open unitInterval

def ComplexPath := Path (X := ℂ)

def linear_path_a_b (a b : ℂ) : ComplexPath a b where -- this thing took me like 2/3 hours
  toFun := λ t : I => (1 - t)*a + t*b
  source' := by simp
  target' := by simp

lemma simm_linear (a b: ℂ) : Path.symm (linear_path_a_b a b) = (linear_path_a_b b a) := by
  unfold linear_path_a_b
  unfold Path.symm
  aesop
  funext
  aesop
  ring

lemma trans_linear (a b : ℂ) : Path.trans (linear_path_a_b a (0.5*(a+b))) ((linear_path_a_b (0.5*(a+b))) b) = linear_path_a_b a b := by
  unfold linear_path_a_b
  unfold Path.trans
  aesop
  funext
  aesop
  rw[Path.extend_extends]
  aesop
  ring_nf
  norm_num
  have h1: val≤ 2⁻¹ := by trivial
  have h2: 2*val≤2*2⁻¹ := by nlinarith
  simp at h2
  exact⟨left,h2⟩
  funext
  aesop
  rw[Path.extend_extends]
  aesop
  ring_nf
  norm_num
  have h3: 2*2⁻¹ ≤ 2*val := by nlinarith
  simp at h3
  exact⟨h3,right⟩


end helpers
