import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Cauchy.definitions.triangle
import Cauchy.helpers.triangle
import Cauchy.lemmas.triangle_continuity

open definitions
open helpers.triangle
open lemmas

namespace lemmas

lemma R3_pos_closed : IsClosed R3_Pos := by
  have : R3_Pos = (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)) := by
    unfold R3_Pos
    rw [Set.Ici,  Set.ext_iff]
    simp only [Set.mem_prod]
    intro x
    constructor
    . simp
      intro a agtz b bgtz c cgtz v
      rw [v]
      simp
      exact ⟨agtz, bgtz, cgtz⟩
    . simp
      intro agtz bgtz cgtz
      refine ⟨x.1, agtz, x.2.1, bgtz, x.2.2, cgtz, ?_⟩
      simp
  rw [this]
  repeat' apply IsClosed.prod
  all_goals { exact isClosed_Ici }

lemma triangle_in_r3_closed : IsClosed TriangleInR3 := by
  unfold TriangleInR3
  apply IsClosed.inter
  exact R3_pos_closed
  apply IsClosed.preimage
  exact continuous_add_components
  exact T1Space.t1 1

lemma triangle_in_r3_compact : IsCompact TriangleInR3 := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  exact triangle_in_r3_closed
  unfold TriangleInR3 R3_Pos AddComponents
  rw [Metric.isBounded_iff]
  refine Exists.intro 2 ?_
  intro x xtri y ytri
  apply le_trans
  exact dist_triangle x 0 y
  have xbound : ‖x‖ ≤ 1 := by
    simp at xtri
    have ⟨⟨a, agtz, b, bgtz, c, cgtz, defx⟩, sum⟩ := xtri
    repeat rw [norm_prod_le_iff]
    rw [defx] at sum ⊢
    simp at sum ⊢
    repeat' constructor
    all_goals rw [abs_of_nonneg (by assumption)]
    all_goals linarith

  have ybound : ‖y‖ ≤ 1 := by
    simp at ytri
    have ⟨⟨a, agtz, b, bgtz, c, cgtz, defy⟩, sum⟩ := ytri
    repeat rw [norm_prod_le_iff]
    rw [defy] at sum ⊢
    simp at sum ⊢
    repeat' constructor
    all_goals rw [abs_of_nonneg (by assumption)]
    all_goals linarith

  simp
  apply le_trans
  refine add_le_add xbound ybound
  linarith

lemma triangle_is_image_triangle_point_of_triangle_in_r3 {T : Triangle} :
  TriangularSet T = TrianglePoint T '' TriangleInR3 := by
  unfold TriangularSet TrianglePoint TriangleInR3 R3_Pos AddComponents
  refine Set.ext_iff.mpr ?_
  intro x
  constructor
  . simp
    intro a gtza b gtzb c gtzc sum defx
    refine ⟨a, b, c, ⟨?_, sum⟩, defx.symm⟩
    exact ⟨a, gtza, b, gtzb, c, gtzc, (by rfl), (by rfl), (by rfl)⟩
  . simp
    intro a b c a_ gtza b_ gtzb c_ gtzc eqa eqb eqc sum defx
    rw [←eqa] at gtza
    rw [←eqb] at gtzb
    rw [←eqc] at gtzc
    refine ⟨a, gtza, b, gtzb, c, gtzc, sum, defx.symm⟩

end lemmas

namespace theorems
-- proof taken from here https://math.stackexchange.com/questions/3778799/a-triangle-is-a-compact-set
theorem triangle_compact {T : Triangle} : IsCompact $ TriangularSet T := by
  rw [triangle_is_image_triangle_point_of_triangle_in_r3]
  exact IsCompact.image triangle_in_r3_compact continuous_triangle_point
