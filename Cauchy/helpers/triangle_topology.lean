import Cauchy.definitions.triangle
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Topology.Algebra.Module.FiniteDimension

open definitions
namespace helpers

lemma false_of_contradict {p : Prop} (h : p) (nh : ¬p) : False :=
  (and_not_self_iff p).1 ⟨h, nh⟩

noncomputable def triangle_basis {T : Triangle} (hT : LinIndep T) :=
  basisOfLinearIndependentOfCardEqFinrank hT (by simp)

noncomputable def continuous_basis_map {T : Triangle} (hT : LinIndep T) :=
  ContinuousLinearEquiv.continuous_toFun $ LinearEquiv.toContinuousLinearEquiv
    (triangle_basis hT).equivFun

noncomputable def normalise (z : ℂ) := ‖z‖⁻¹

lemma normalise_pos {z : ℂ} (hz : z ≠ 0) : normalise z > 0 := by unfold normalise; aesop

lemma normalise_apply (z : ℂ) (hz : z ≠ 0) : ‖normalise z * z‖ = 1 := by
  unfold normalise
  simp only [Complex.norm_eq_abs, Complex.ofReal_inv, norm_mul, norm_inv, Complex.abs_ofReal,
    Complex.abs_abs, ne_eq, map_eq_zero]
  rw [inv_mul_cancel]
  simp only [ne_eq, map_eq_zero]
  exact hz

lemma reduce_point {z A B C : ℂ} {a b c : ℝ} (sum : a + b + c = 1) :
  z = a*A + b*B + c*C → z - C = a*(A-C) + b*(B-C) := by
  have : c = 1 - a - b := by rewrite [←sum]; ring
  rewrite [this]; simp only [Complex.ofReal_sub, Complex.ofReal_one];
  intro h; rewrite [h]; ring

def coords_as_basis {T : Triangle} (hT : LinIndep T) {z : ℂ} {a b : ℝ}
  (hz : a * (T.a - T.c) + b * (T.b - T.c) = z) : a = (triangle_basis hT).repr z 0 ∧
  b = (triangle_basis hT).repr z 1 := by
  have r := Basis.sum_repr (triangle_basis hT) z
  unfold triangle_basis at r ⊢
  simp only [coe_basisOfLinearIndependentOfCardEqFinrank, Complex.real_smul, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at r
  have : 0 = (a - (triangle_basis hT).repr z 0) * (T.a - T.c) +
    (b - (triangle_basis hT).repr z 1) * (T.b - T.c) := by
    unfold triangle_basis
    rewrite [←r, ←sub_eq_zero] at hz
    rewrite [←hz]
    ring
  simp only [←Complex.ofReal_sub, ←Complex.real_smul] at this
  have l := LinearIndependent.pair_iff.1 hT (a - ((triangle_basis hT).repr z) 0)
    (b - ((triangle_basis hT).repr z) 1) this.symm
  simp only [sub_eq_zero] at l
  exact l
