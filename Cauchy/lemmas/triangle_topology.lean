import Cauchy.definitions.triangle
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.LinearAlgebra.FiniteDimensional

open definitions
namespace lemmas

noncomputable def triangle_basis (T : Triangle) (hT : LinIndep T) :=
  basisOfLinearIndependentOfCardEqFinrank hT (by simp)

lemma set_helper {p q : ℂ → Prop} (h : p = q) : Set {z | p z} = Set {z | q z} := by rw [h]

def triangle_basis_apply (T : Triangle) (hT : LinIndep T) (z : ℂ) :
  ∃rab rbc : ℝ, z = rab*(T.a-T.c) + rbc*(T.b-T.c) := by
  use Basis.coord (triangle_basis T hT) 0 z
  use Basis.coord (triangle_basis T hT) 1 z
  have r := Basis.sum_repr (triangle_basis T hT) z
  simp only [Basis.coord_apply]
  unfold triangle_basis at r ⊢
  simp only [Complex.real_smul, Fin.sum_univ_two, coe_basisOfLinearIndependentOfCardEqFinrank,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at r
  exact r.symm

def triangle_interior_interior (T : Triangle) :
  interior (TriangularSet T) = TriangularInterior T := by sorry
