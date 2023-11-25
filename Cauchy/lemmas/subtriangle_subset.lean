import Mathlib.Data.Set.Basic
import Cauchy.definitions.triangle
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic
import Mathlib.Data.Complex.Basic

open definitions

lemma subtriangle_subset {T : Triangle} : (TriangularSet $ subTriangle T) ⊆ TriangularSet T := by
  unfold TriangularSet subTriangle
  simp
  intro z a gtza b gtzb c gtzc sum defz
  refine ⟨(c+a)/2, by linarith, (a+b)/2, by linarith, (b+c)/2, by linarith, ?s, ?dz⟩
  rw [←sum]
  ring
  rw [defz]
  simp
  ring
