import Mathlib.Data.Set.Basic
import Cauchy.helpers.linear_paths
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Cauchy.definitions.triangle
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Init.Data.Float

open definitions
namespace lemmas


lemma perim_subtriangle_is_half_triangle {T : Triangle}
  (h_perimT_eq_l : perimeter T = l) : perimeter (subTriangle T) = l/2 := by
  unfold perimeter
  unfold perimeter at h_perimT_eq_l
  have sTa : (subTriangle T).a =  (T.b + T.a)/2 := by rfl
  have sTb : (subTriangle T).b =  (T.c + T.b)/2 := by rfl
  have sTc : (subTriangle T).c =   (T.a + T.c)/2 := by rfl
  rw[sTa,sTb,sTc]
  repeat rw[dist_eq_norm]
  repeat rw[dist_eq_norm] at h_perimT_eq_l

  calc ‖ (T.c + T.b)/2 -  (T.b + T.a)/2‖ + ‖ (T.a + T.c)/2 - (T.c + T.b)/2‖ +‖(T.b + T.a)/2 - (T.a + T.c)/2‖ = ‖-1/2 *(T.b-T.a)‖ + ‖-1/2 *(T.c-T.b)‖ + ‖-1/2 *(T.a-T.c)‖  := by ring
  _ = ‖(-1/2 : ℂ)‖ * ‖T.b - T.a‖ + ‖(-1/2 : ℂ)‖ * ‖T.c - T.b‖ + ‖(-1/2 : ℂ)‖*‖T.a - T.c‖ := by repeat rw[norm_mul]
  _ = ‖(-1/2 : ℂ)‖*(‖T.b - T.a‖ + ‖ T.c - T.b‖ + ‖T.a - T.c‖)  := by ring
  _ = ‖(-1/2 : ℂ)‖*l := by rw[h_perimT_eq_l]
  _ = 1/2 * l := by aesop
  _ = l/2 := by ring

end lemmas
