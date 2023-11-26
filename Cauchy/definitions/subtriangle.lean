import Mathlib.Data.Set.Basic
import Cauchy.helpers.linear_paths
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Cauchy.definitions.triangle

open definitions

namespace definitions

structure SubTriangle extends Triangle where
  coveringTriangle : Triangle
  ha : a ∈ TriangularSet coveringTriangle
  hb : b ∈ TriangularSet coveringTriangle
  hc : c ∈ TriangularSet coveringTriangle

instance : Coe SubTriangle Triangle where coe := SubTriangle.toTriangle

def constructSubtriangle (coveringTriangle : Triangle) (a1 b1 c1 a2 b2 c2 a3 b3 c3 : ℝ)
  (hsum1 : a1+b1+c1 = 1 := by ring) (hsum2 : a2+b2+c2 = 1 := by ring) (hsum3 : a3+b3+c3 = 1 := by ring)
  (gtz : a1 ≥ 0 ∧ b1 ≥ 0 ∧ c1 ≥ 0 ∧ a2 ≥ 0 ∧ b2 ≥ 0 ∧ c2 ≥ 0 ∧ a3 ≥ 0 ∧ b3 ≥ 0 ∧ c3 ≥ 0
   := by (repeat' constructor); all_goals {linarith}) : SubTriangle
  := by
  have ⟨a1gtz, b1gtz, c1gtz, a2gtz, b2gtz, c2gtz, a3gtz, b3gtz, c3gtz⟩ := gtz
  exact {
    coveringTriangle := coveringTriangle
    a := coveringTriangle.a * a1 + coveringTriangle.b * b1 + coveringTriangle.c * c1
    b := coveringTriangle.a * a2 + coveringTriangle.b * b2 + coveringTriangle.c * c2
    c := coveringTriangle.a * a3 + coveringTriangle.b * b3 + coveringTriangle.c * c3
    ha := ⟨a1, b1, c1, a1gtz, b1gtz, c1gtz, hsum1, by simp; ring⟩
    hb := ⟨a2, b2, c2, a2gtz, b2gtz, c2gtz, hsum2, by simp; ring⟩
    hc := ⟨a3, b3, c3, a3gtz, b3gtz, c3gtz, hsum3, by simp; ring⟩
  }
