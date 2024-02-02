import Cauchy.definitions.triangle
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic
import Cauchy.lemmas.triangle_inequality
import Cauchy.lemmas.complex_real_norm_equiv
import Cauchy.helpers.triangle
import Cauchy.theorems.triangle_compact

open definitions
open lemmas
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
