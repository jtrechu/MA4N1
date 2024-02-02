import Cauchy.definitions.triangle
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Cauchy.helpers.triangle_topology

open definitions helpers
namespace lemmas

--We want to show that the interior of the triangle as we defined it
--is the same as the topological interior of the set

--First we show that the interior is open

def isOpen_triangle_interior {T : Triangle} (hT : LinIndep T) :
  IsOpen $ TriangularInterior T := by
  rewrite [Metric.isOpen_iff]
  intro x ⟨a, b, c, gtza, gtzb, gtzc, sum, defx⟩
  have defx := reduce_point sum defx
  have coords_basis := coords_as_basis hT defx.symm
  have cb := Metric.continuous_iff.1 $ continuous_basis_map hT
  have mingtz : min a (min b (c/2)) > 0 := by
    apply lt_min; exact gtza; apply lt_min; exact gtzb; linarith
  have ⟨d, hd, hbd⟩ := cb (x-T.c) (min a (min b (c/2))) mingtz
  simp only [LinearEquiv.toLinearEquiv_toContinuousLinearEquiv, AddHom.toFun_eq_coe,
    LinearMap.coe_toAddHom, LinearEquiv.coe_coe, Basis.equivFun_apply] at hbd
  refine ⟨d, hd, ?_⟩
  rewrite [Set.subset_def]
  intro z hz
  have hp := hbd (z-T.c) (by simp; exact hz)
  rewrite [dist_pi_lt_iff mingtz, Fin.forall_fin_two, ←coords_basis.1, ←coords_basis.2] at hp
  clear coords_basis cb
  simp only [Real.dist_eq, lt_min_iff] at hp
  have gtz := sub_lt_of_abs_sub_lt_left hp.1.1
  have gtz2 := sub_lt_of_abs_sub_lt_left hp.2.2.1
  have ltc := sub_lt_of_abs_sub_lt_right hp.1.2.2
  have ltc2 := sub_lt_of_abs_sub_lt_right hp.2.2.2
  rewrite [sub_lt_iff_lt_add] at ltc ltc2
  simp only [sub_self] at gtz gtz2
  have cineq := add_lt_add ltc ltc2
  ring_nf at cineq
  conv_rhs at cineq => {
    rewrite [add_assoc]
    conv => { arg 2; rewrite [add_comm]; }
    rewrite [←add_assoc]
  }
  rewrite [sum] at cineq
  refine ⟨(triangle_basis hT).repr (z - T.c) 0, (triangle_basis hT).repr (z - T.c) 1,
          1 - (triangle_basis hT).repr (z - T.c) 0 - (triangle_basis hT).repr (z - T.c) 1,
          gtz, gtz2, ?_, by ring, ?_⟩
  apply LT.lt.gt
  rewrite [lt_sub_iff_add_lt, lt_sub_iff_add_lt, zero_add, add_comm]
  exact cineq
  have defz := Basis.sum_repr (triangle_basis hT) (z-T.c)
  unfold triangle_basis at defz ⊢
  simp only [coe_basisOfLinearIndependentOfCardEqFinrank, Complex.real_smul,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at defz
  rewrite [eq_sub_iff_add_eq] at defz
  simp only [Complex.ofReal_sub, Complex.ofReal_one]
  nth_rewrite 1 [←defz]
  ring

--We now show that there are no open sets which contain points of the boundary and are subsets of the triangle
--i.e. only the sets contained in the interior can be open
lemma triangle_boundary_not_open (T : Triangle) (hT : LinIndep T) :
  ∀z ∈ TriangularBoundary T, ¬∃s ⊆ TriangularSet T, IsOpen s ∧ z ∈ s := by
  intro z ⟨a, b, c, gtza, gtzb, gtzc, sum, mulz, defz⟩
  have nz := reduce_point sum defz
  by_contra h
  simp at mulz
  have ⟨s, ss, ho, hs⟩ := h
  have ⟨e, he, bs⟩ := Metric.isOpen_iff.1 ho z hs
  rewrite [Set.subset_def] at bs
  rcases mulz with (rfl | rfl) | rfl
  . have ssw := bs (z - e/2 * normalise (T.a - T.c)*(T.a-T.c)) ?_
    have ⟨a', b', c', gtza', _, _, sum', defw⟩ := Set.mem_of_subset_of_mem ss ssw
    have nw := Eq.symm $ reduce_point sum' defw
    have : z - T.c = ↑(a' + e / 2 * (normalise (T.a - T.c))) * (T.a - T.c) + ↑b' * (T.b - T.c) := by
      repeat rewrite [eq_sub_iff_add_eq] at nw
      rewrite [←nw]
      simp
      ring
    have c1 := coords_as_basis hT this.symm
    have c2 := coords_as_basis hT nz.symm
    rewrite [←c2.1] at c1
    have p := LT.lt.ne $ add_pos_of_pos_of_nonneg (a:=e / 2 * normalise (T.a - T.c)) ?_ gtza'
    rewrite [add_comm] at p
    exact false_of_contradict c1.1.symm p
    apply div_pos
    linarith
    simp only [Complex.norm_eq_abs, ←Complex.dist_eq, dist_pos]
    exact Ne.symm (linindep_not_trivial T hT).2.2

    rewrite [Metric.mem_ball, dist_self_sub_left, mul_assoc, norm_mul, normalise_apply]
    simp only [norm_div, Complex.norm_eq_abs, Complex.abs_ofReal, IsROrC.norm_ofNat, mul_one]
    rewrite [abs_of_pos he]
    linarith

    rewrite [sub_ne_zero]
    exact Ne.symm (linindep_not_trivial T hT).2.2

  . have ssw := bs (z - e/2 * normalise (T.b - T.c)*(T.b-T.c)) ?_
    have ⟨a', b', c', _, gtzb', _, sum', defw⟩ := Set.mem_of_subset_of_mem ss ssw
    have nw := Eq.symm $ reduce_point sum' defw
    have : z - T.c = ↑a' * (T.a - T.c) + ↑(b' + e / 2 * (normalise (T.b - T.c))) * (T.b - T.c) := by
      repeat rewrite [eq_sub_iff_add_eq] at nw
      rewrite [←nw]
      simp
      ring
    have c1 := coords_as_basis hT this.symm
    have c2 := coords_as_basis hT nz.symm
    rewrite [←c2.2] at c1
    have p := LT.lt.ne $ add_pos_of_pos_of_nonneg (a:=e / 2 * normalise (T.b - T.c)) ?_ gtzb'
    rewrite [add_comm] at p
    exact false_of_contradict c1.2.symm p
    apply div_pos
    linarith
    simp only [Complex.norm_eq_abs, ←Complex.dist_eq, dist_pos]
    exact (linindep_not_trivial T hT).2.1

    rewrite [Metric.mem_ball, dist_self_sub_left, mul_assoc, norm_mul, normalise_apply]
    simp only [norm_div, Complex.norm_eq_abs, Complex.abs_ofReal, IsROrC.norm_ofNat, mul_one]
    rewrite [abs_of_pos he]
    linarith

    rewrite [sub_ne_zero]
    exact (linindep_not_trivial T hT).2.1

  . have ssw := bs (z + e/2 * normalise (T.b - T.c)*(T.b-T.c)) ?_
    have ⟨a', b', c', _, _, gtzc', sum', defw⟩ := Set.mem_of_subset_of_mem ss ssw
    simp only [add_zero] at sum
    have nw := Eq.symm $ reduce_point sum' defw
    have : z - T.c = ↑a' * (T.a - T.c) + ↑(b' - e / 2 * (normalise (T.b - T.c))) * (T.b - T.c) := by
      rewrite [eq_sub_iff_add_eq, ←sub_eq_iff_eq_add] at nw
      rewrite [←nw]
      simp
      ring
    have c1 := coords_as_basis hT this.symm
    have c2 := coords_as_basis hT nz.symm
    rewrite [←c2.1, ←c2.2, sub_eq_iff_eq_add] at c1
    rewrite [c1.1, c1.2, ←add_assoc, sum, add_rotate, ←eq_sub_iff_add_eq,
      add_comm, ←eq_sub_iff_add_eq, sub_self, zero_sub] at sum'
    apply false_of_contradict gtzc'
    simp only [ge_iff_le, not_le]
    rewrite [sum']
    apply neg_neg_of_pos
    apply mul_pos
    linarith
    apply normalise_pos

    swap
    rewrite [Metric.mem_ball, dist_self_add_left, mul_assoc, norm_mul, normalise_apply]
    simp only [norm_div, Complex.norm_eq_abs, Complex.abs_ofReal, IsROrC.norm_ofNat, mul_one]
    rewrite [abs_of_pos he]
    linarith

    all_goals
      rewrite [sub_ne_zero]
      exact (linindep_not_trivial T hT).2.1

end lemmas
open lemmas
namespace theorems

--Now we show that the interior of the triangle set (topologically)
--is the same as the set we previously called Interior
def triangle_interior_interior {T : Triangle} (hT : LinIndep T) :
  interior (TriangularSet T) = TriangularInterior T := by
  apply Set.Subset.antisymm
  . apply interior_subset_iff.2
    intro u hu hut
    have hut' := hut
    rewrite [Set.subset_def] at hut' ⊢
    intro z hz
    have hut' := hut' z hz
    rewrite [triangle_union, Set.mem_union] at hut'
    rcases hut' with b | i
    . have q := triangle_boundary_not_open T hT z b
      push_neg at q
      have := q u hut hu
      contradiction
    exact i
  apply (IsOpen.subset_interior_iff $ isOpen_triangle_interior hT).2
  exact interior_in_set
