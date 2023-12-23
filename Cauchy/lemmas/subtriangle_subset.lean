import Mathlib.Data.Set.Basic
import Cauchy.definitions.triangle
import Cauchy.definitions.subtriangle
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Cauchy.helpers.inequalities

open definitions
open helpers

namespace lemmas

lemma subtriangle_subset (T : Triangle) : (TriangularSet $ subTriangle T) ⊆ TriangularSet T := by
  unfold TriangularSet subTriangle
  simp
  intro z a gtza b gtzb c gtzc sum defz
  refine ⟨(c+a)/2, by linarith, (a+b)/2, by linarith, (b+c)/2, by linarith, ?s, ?dz⟩
  rw [←sum]
  ring
  rw [defz]
  simp
  ring

lemma subtriangle_subset' {T : Triangle } (sT : SubTriangle T) :
  TriangularSet sT ⊆ TriangularSet T := by
    have {a := sTa, b := sTb, c := sTc, ha, hb, hc} := sT
    simp at ha hb hc
    unfold TriangularSet at *
    simp at ha hb hc ⊢
    intro z sa gtzsa sb gtzsb sc gtzsc sum defz
    have ⟨staa, gtzstaa, stab, gtzstab, stac, gtzstac, stasum, defsta⟩ := ha
    have ⟨stba, gtzstba, stbb, gtzstbb, stbc, gtzstbc, stbsum, defstb⟩ := hb
    have ⟨stca, gtzstca, stcb, gtzstcb, stcc, gtzstcc, stcsum, defstc⟩ := hc
    rw [defz, defsta, defstb, defstc]
    clear z defz
    clear ha hb hc
    refine ⟨sa*staa + sb*stba + sc*stca, by apply helpers.inequalities.gt_nonneg_sum_prod_3 <;> assumption,
      sa*stab + sb*stbb + sc*stcb, by apply helpers.inequalities.gt_nonneg_sum_prod_3 <;> assumption,
      sa*stac + sb*stbc + sc*stcc, by apply helpers.inequalities.gt_nonneg_sum_prod_3 <;> assumption,
      ?sum, ?defz⟩
    . ring_nf
      repeat rewrite [←left_distrib]
      rewrite [add_assoc, add_assoc]
      repeat rewrite [←left_distrib]
      rewrite [add_comm]
      rewrite [add_assoc, add_assoc]
      repeat rewrite [←left_distrib]
      repeat rewrite [←add_assoc]
      rewrite [stasum, stbsum, stcsum]
      simp only [mul_one]
      rw [add_rotate]
      exact sum
    . simp
      ring
