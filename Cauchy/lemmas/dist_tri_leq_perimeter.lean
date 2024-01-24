import Cauchy.definitions.triangle
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic
import Cauchy.lemmas.triangle_inequality
import Cauchy.lemmas.complex_real_norm_equiv

open definitions
open lemmas

namespace lemmas

lemma dist_tri_leq_perimeter (T : Triangle) (a b : ℂ) :
  a ∈ TriangularSet T ∧ b ∈ TriangularSet T → dist b a ≤ perimeter T := by
  rewrite [dist_eq_norm]
  intro ⟨ha, hb⟩
  unfold TriangularSet at ha hb
  have ⟨a₁, a₂, a₃, gtza1, gtza2, gtza3, eqa1, defa⟩ := ha
  have ⟨b₁, b₂, b₃, gtzb1, gtzb2, gtzb3, eqb1, defb⟩ := hb
  have : b - a = (↑b₁ - ↑a₁)*(T.a - T.c) + (↑b₂ - ↑a₂)*(T.b - T.c) := by

    have a3eq : a₃ = 1 - a₁ - a₂ := by rw [←eqa1]; ring
    have b3eq : b₃ = 1 - b₁ - b₂ := by rw [←eqb1]; ring
    rewrite [defa, defb, a3eq, b3eq]
    simp -- this simp is necessary, as it moves coercions inside allowing ring to function!
    ring

  rewrite [this]
  unfold perimeter
  apply le_trans
  exact triangle_inequality
  repeat rewrite [norm_mul]

  have bounded1 : ‖b₁-a₁‖ ≤ 1 := by -- have to repeat the proof twice, unfortunate but necessary
    have bbound : b₁ ≤ 1 := by linarith -- (I think!)
    have abound : a₁ ≤ 1 := by linarith
    rewrite [Real.norm_eq_abs, ←max_sub_min_eq_abs, sub_le_iff_le_add']
    apply le_trans
    exact max_le abound bbound
    simp
    exact ⟨gtza1, gtzb1⟩
  have bounded2 : ‖b₂-a₂‖ ≤ 1 := by -- the proof would be fairly compact without them... :(
    have bbound : b₂ ≤ 1 := by linarith
    have abound : a₂ ≤ 1 := by linarith
    rewrite [Real.norm_eq_abs, ←max_sub_min_eq_abs, sub_le_iff_le_add']
    apply le_trans
    exact max_le abound bbound
    simp
    exact ⟨gtza2, gtzb2⟩

  rewrite [Complex.norm_eq_abs (T.a - T.c), Complex.norm_eq_abs (T.b - T.c)]
  repeat rewrite [←Complex.dist_eq]
  rewrite [Complex.instNormedFieldComplex.dist_comm T.b]
  repeat rewrite [complex_real_norm_equiv] -- actually quite an important line (type conversions!)
  have leq1 : ‖b₁ - a₁‖ * dist T.a T.c ≤ dist T.a T.c := by
    exact mul_le_of_le_one_left (by exact dist_nonneg) bounded1
  have leq2 : ‖b₂ - a₂‖ * dist T.c T.b ≤ dist T.c T.b := by
    exact mul_le_of_le_one_left (by exact dist_nonneg) bounded2
  apply le_trans -- these two lines are unnecessary, but I do so much heavy lifting
  exact add_le_add leq1 leq2 -- that it's unfair for linarith to take all the credit for it!
  have : dist T.b T.a ≥ 0 := by exact dist_nonneg
  linarith only [this]
