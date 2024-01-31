import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Data.Complex.Basic
import Cauchy.definitions.triangle
import Cauchy.definitions.subtriangle
import Cauchy.definitions.path_integrals
import Cauchy.definitions.domain
import Cauchy.helpers.triangle

open definitions

namespace definitions

variable {T : Triangle}

lemma exists_point_around (z : ℂ) (hz : z ∈ (interior $ TriangularSet T)) :
  ∃ε > 0, Metric.ball z ε ⊆ interior (TriangularSet T)
  := Metric.isOpen_iff.1 (isOpen_interior) z hz


lemma point_around (z : ℂ) (hz : z ∈ (interior $ TriangularSet T)) : ℝ := Exists.choose (
  exists_point_around z hz
)

lemma point_around_apply (z : ℂ) (hz : z ∈ (interior $ TriangularSet T)) :
  (point_around z hz) > 0 ∧ Metric.ball z (point_around z hz) ⊆ interior (TriangularSet T) := by
  unfold point_around
  exact Exists.choose_spec $ exists_point_around z hz

lemma ineq : Real.sqrt (4 * 4 + 1)/18 < 1 := by
  rewrite [div_lt_one, Real.sqrt_lt']
  all_goals norm_num

noncomputable def eps_subtriangle (z : ℂ) (hz : z ∈ (interior $ TriangularSet T))
  (ε : ℝ) (he : ε > 0) : SubTriangle T := {
  a := z + 2 * (min ε (point_around z hz))/18 * Complex.I
  b := z - (Complex.I + 4) * (min ε (point_around z hz))/18
  c := z - (Complex.I - 4) * (min ε (point_around z hz))/18
  ha := by {
    have hp := point_around_apply z hz
    simp only []
    apply Set.mem_of_subset_of_mem
    apply interior_subset
    apply Set.mem_of_subset_of_mem
    apply hp.2
    simp only [ge_iff_le, Metric.mem_ball, dist_self_add_left, norm_mul, norm_div,
      IsROrC.norm_ofNat, Complex.norm_eq_abs, Complex.abs_ofReal, Complex.abs_I, mul_one, min_def]
    by_cases ε ≤ point_around z hz
    rewrite [if_pos h, abs_of_pos he]
    linarith
    rewrite [if_neg h, abs_of_pos hp.1]
    linarith
  }
  hb := by {
    have hp := point_around_apply z hz
    simp only []
    apply Set.mem_of_subset_of_mem
    apply interior_subset
    apply Set.mem_of_subset_of_mem
    apply hp.2
    simp only [ge_iff_le, Metric.mem_ball, dist_self_sub_left, norm_div, norm_mul,
      Complex.norm_eq_abs, Complex.abs_ofReal, IsROrC.norm_ofNat, Complex.abs_def,
      Complex.normSq_apply, Complex.add_re, Complex.I_re, Complex.re_ofNat, zero_add,
      Complex.add_im, Complex.I_im, Complex.im_ofNat, add_zero, mul_one, ge_iff_le, min_def]
    by_cases ε ≤ point_around z hz
    rewrite [if_pos h, abs_of_pos he, mul_comm, ←mul_div]
    apply lt_of_lt_of_le ?_ h
    rewrite [mul_lt_iff_lt_one_right]
    exact ineq
    exact he
    rewrite [if_neg h, abs_of_pos hp.1, mul_comm, ←mul_div, mul_lt_iff_lt_one_right]
    exact ineq
    exact hp.1
  }
  hc := by {
    have hp := point_around_apply z hz
    simp only []
    apply Set.mem_of_subset_of_mem
    apply interior_subset
    apply Set.mem_of_subset_of_mem
    apply hp.2
    simp only [ge_iff_le, Metric.mem_ball, dist_self_sub_left, norm_div, norm_mul,
      Complex.norm_eq_abs, Complex.abs_ofReal, IsROrC.norm_ofNat, Complex.abs_def,
      Complex.normSq_apply, Complex.sub_re, Complex.I_re, Complex.re_ofNat, zero_sub, mul_neg,
      neg_mul, neg_neg, Complex.sub_im, Complex.I_im, Complex.im_ofNat, sub_zero, mul_one, min_def]
    by_cases ε ≤ point_around z hz
    rewrite [if_pos h, abs_of_pos he, mul_comm, ←mul_div]
    apply lt_of_lt_of_le ?_ h
    rewrite [mul_lt_iff_lt_one_right]
    exact ineq
    exact he
    rewrite [if_neg h, abs_of_pos hp.1, mul_comm, ←mul_div, mul_lt_iff_lt_one_right]
    exact ineq
    exact hp.1
  }
}

lemma sqrt_25 : Real.sqrt 25 = 5 := by
  rewrite [Real.sqrt_eq_iff_mul_self_eq_of_pos]
  all_goals norm_num

lemma sqrt_324 : Real.sqrt 324 = 18 := by
  rewrite [Real.sqrt_eq_iff_mul_self_eq_of_pos]
  all_goals norm_num

lemma eps_subtriangle_apply (z : ℂ) (hz : z ∈ (interior $ TriangularSet T))
  (ε : ℝ) (he : ε > 0) : (perimeter $ eps_subtriangle z hz ε he) ≤ ε := by
  unfold perimeter
  unfold eps_subtriangle
  simp only [dist_eq_norm]
  ring_nf
  simp only [ge_iff_le, Int.cast_negOfNat, Nat.cast_one, mul_neg, mul_one, Int.ofNat_eq_coe,
    Int.cast_one, Nat.cast_ofNat, one_div, neg_mul, Complex.norm_eq_abs, Int.int_cast_ofNat,
    norm_mul, Complex.abs_ofReal, norm_div, IsROrC.norm_ofNat, Complex.abs_def, Complex.normSq_apply]
  simp only [ge_iff_le, Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_re, zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_self,
    Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat, div_self_mul_self', Complex.mul_im,
    one_mul, zero_add, Complex.inv_im, Complex.im_ofNat, neg_zero, zero_div, sub_zero, add_zero,
    mul_neg, neg_mul, neg_neg, Complex.add_im, Complex.neg_im]
  ring_nf
  rewrite [Real.sqrt_mul, Real.sqrt_sq_eq_abs, Real.sqrt_div]
  simp only [ge_iff_le, Int.ofNat_eq_coe, Nat.cast_ofNat, Int.int_cast_ofNat]
  rewrite [sqrt_25, sqrt_324]
  ring_nf
  rewrite [min_def]
  by_cases ε ≤ point_around z hz
  rewrite [if_pos h, abs_of_pos]
  rfl
  exact he
  rewrite [if_neg h, abs_of_pos]
  linarith
  exact (point_around_apply z hz).1
  norm_num
  apply sq_nonneg
