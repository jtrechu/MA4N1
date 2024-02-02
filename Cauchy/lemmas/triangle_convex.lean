import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.UnitInterval

import Cauchy.definitions.triangle
import Cauchy.definitions.linear_path

open definitions unitInterval

namespace lemmas

-- Here we show that the triangular set is a convex set. This is that given any two points of the set
-- the segment between the points is also contained in the triangular set

lemma linear_path_contained (T : Triangle) (a b : ℂ) (ha : a ∈ TriangularSet T)
  (hb : b ∈ TriangularSet T) : (LinearPath.mk a b) '' I ⊆ TriangularSet T := by
  unfold TriangularSet at ha hb ⊢
  rewrite [Set.image, Set.subset_def]
  simp only [Set.mem_setOf_eq, ge_iff_le, exists_and_left, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  have ⟨a1, a2, a3, gtza1, gtza2, gtza3, suma, defa⟩ := ha
  have ⟨b1, b2, b3, gtzb1, gtzb2, gtzb3, sumb, defb⟩ := hb
  intro t ht
  refine ⟨(1 - t)*a1 + t*b1, ?_, (1 - t)*a2 + t*b2, ?_, (1 - t)*a3 + t*b3, ?_, ?_⟩
  any_goals apply add_nonneg
  any_goals apply mul_nonneg
  any_goals assumption
  any_goals exact Set.Icc.coe_nonneg ⟨t, ht⟩
  any_goals exact Set.Icc.one_sub_nonneg ⟨t, ht⟩
  constructor
  apply Eq.symm
  calc
    1 = (1 - t) * (a1 + a2 + a3) + t * (b1 + b2 + b3) := by aesop
    _ = (1 - t) * a1 + t * b1 + ((1 - t) * a2 + t * b2) + ((1 - t) * a3 + t * b3) := by ring
  rewrite [defa, defb]
  simp
  ring
