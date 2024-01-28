import Cauchy.definitions.triangle
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic
import Cauchy.lemmas.triangle_inequality
import Cauchy.lemmas.complex_real_norm_equiv
import Cauchy.helpers.triangle
import Cauchy.theorems.triangle_compact
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open definitions
open lemmas Matrix.vecMul

namespace lemmas

lemma rwsum {a b c : ℝ} : a + b + c = 1 ↔ 1 - a - b = c := by
  constructor
  all_goals
    intro h
    rewrite [←h]
    ring

lemma rwdef {A B C : ℂ} (a b : ℝ) :
  z = a * A + b * B + (1 - a - b) * C ↔ z + -C = a * (A-C) + b * (B-C) := by
  constructor
  all_goals
    intro h
    try rewrite [add_neg_eq_iff_eq_add] at h
    rewrite [h]
    ring

lemma rwsum' {a b c : ℝ} : a + b + c = 1 ↔ 1 - a - c = b := by
  constructor
  all_goals
    intro h
    rewrite [←h]
    ring

lemma rwdef' {A B C : ℂ} (a c : ℝ) :
  z = a * A + (1 - a - c) * B + c * C ↔ z + -B = a * (A-B) + c * (C-B) := by
  constructor
  all_goals
    intro h
    try rewrite [add_neg_eq_iff_eq_add] at h
    rewrite [h]
    ring

lemma linindep_basis_change (T : Triangle) :
  LinIndep T → LinearIndependent ℝ ![T.a - T.b, T.c - T.b] := by
  unfold LinIndep
  intro h
  have : (1:ℝ) * -1 - -1 * 0 ≠ 0 := by norm_num
  have r := LinearIndependent.linear_combination_pair_of_det_ne_zero h this
  simp at r
  exact r

lemma triangle_disjoint_if_linindep (T : Triangle) :
  LinIndep T → Disjoint (TriangularBoundary T) (TriangularInterior T) := by
  unfold LinIndep
  . intro f
    rewrite [Set.disjoint_left]
    intro z ⟨a, b, c, _, _, _, sum, mul_zero, defz⟩
    simp only [mul_eq_zero] at mul_zero
    rcases mul_zero with hab | hc

    any_goals
      unfold TriangularInterior
      rewrite [Set.nmem_setOf_iff]
      by_contra t
      have ⟨a', b', c', gtza', gtzb', gtzc', sum', defz'⟩ := t

    . rewrite [rwsum] at sum sum'
      rewrite [←sum] at defz
      rewrite [←sum'] at defz'
      simp at defz defz'
      rewrite [rwdef] at defz defz'
      rewrite [defz'] at defz
      have LI := LinearIndependent.eq_of_pair f defz
      simp only [Complex.ofReal_re] at LI
      repeat rewrite [Complex.ofReal_inj] at LI
      cases hab with
      | inl az => rewrite [LI.1] at gtza'; have := ne_of_gt gtza'; contradiction
      | inr bz => rewrite [LI.2] at gtzb'; have := ne_of_gt gtzb'; contradiction

    . rewrite [rwsum'] at sum sum'
      rewrite [←sum] at defz
      rewrite [←sum'] at defz'
      simp at defz defz'
      rewrite [rwdef'] at defz defz'
      rewrite [defz'] at defz
      have LI := LinearIndependent.eq_of_pair (linindep_basis_change T f) defz
      simp only [Complex.ofReal_re] at LI
      repeat rewrite [Complex.ofReal_inj] at LI
      rewrite [LI.2] at gtzc'; have := ne_of_gt gtzc'; contradiction

  /--

  lemma div_sum_le_one {a b : ℝ} (ha : a > 0) (hb : b ≥ 0) : (1/2) * a / (a + b) > 0 :=
  by apply mul_pos; linarith; rewrite [inv_pos]; linarith

lemma div_sum_le_one' {a b : ℝ} (ha : a ≥ 0) (hb : b > 0) : (1/2) * b / (a + b) > 0 :=
  by apply mul_pos; linarith; rewrite [inv_pos]; linarith


lemma div_sum_le_one_neg {a b : ℝ} (ha : a < 0) (hb : b ≤ 0) : (1/2) * a / (a + b) ≥ 0 :=
  by apply div_nonneg_of_nonpos; linarith; linarith

lemma div_sum_le_one_neg' {a b : ℝ} (ha : a < 0) (hb : b ≤ 0) : (1/2) * b / (a + b) ≥ 0 :=
  by apply div_nonneg_of_nonpos; linarith; linarith

lemma one_sub_div {a b : ℝ} (hab : a+b≠0) : 1-a/(a+b) = b/(a+b) := by
  rewrite [←div_self (a:=a+b) hab, ←sub_div]; simp

  . contrapose
    unfold definitions.Nontrivial at hT
    rewrite [LinearIndependent.pair_iff, Set.not_disjoint_iff]
    push_neg
    intro nli
    have ⟨t, t1, nlit, nzt⟩ := nli
    use T.c
    constructor
    exact ⟨0, 0, 1, by rfl, by rfl, zero_le_one, by norm_num, by norm_num⟩
    simp only [Complex.real_smul] at nlit
    have : t * (T.a - T.c) + t1 * (T.b - T.c) = t*T.a + t1*T.b - T.c * (t+t1) := by ring
    rewrite [this, sub_eq_zero] at nlit
    have neq : t1 ≠ -t := by
      by_contra h
      rewrite [h] at nlit
      simp only [Complex.ofReal_neg, add_right_neg, mul_zero] at nlit
      have : t * T.a + -↑t * T.b = t* (T.a - T.b) := by ring
      rewrite [this] at nlit
      simp only [mul_eq_zero, Complex.ofReal_eq_zero] at nlit
      cases nlit with
      | inl tz => rewrite [tz] at h; simp at h; have := nzt tz; contradiction
      | inr tnz => rewrite [sub_eq_zero] at tnz; have := hT.1; contradiction
    have neq : (t:ℂ)+t1≠0 := by simp; rewrite [add_comm, ←eq_neg_iff_add_eq_zero,
      ←Complex.ofReal_neg, Complex.ofReal_inj]; exact neq
    rewrite [←div_eq_iff neq, add_div] at nlit
    sorry -- a lot of messy algebra, but possible!--/

lemma nd : Prop := true
