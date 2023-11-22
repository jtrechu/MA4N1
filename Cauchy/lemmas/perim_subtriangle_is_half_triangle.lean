import Mathlib.Data.Set.Basic
import Cauchy.helpers.linear_paths
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Cauchy.definitions.triangle

open definitions
namespace lemmas

lemma perim_subtriangle_is_half_triangle {T : Triangle}
  (h_perimT_eq_l : perimeter T = l) : perimeter (subTriangle T) = l/2 := by
  unfold perimeter at h_perimT_eq_l
  unfold perimeter
  sorry

end lemmas
