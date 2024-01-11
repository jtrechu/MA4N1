import Mathlib.Data.Set.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Cauchy.definitions.triangle

open definitions

namespace definitions

structure SubTriangle (T : Triangle) extends Triangle where
  ha : a ∈ TriangularSet T
  hb : b ∈ TriangularSet T
  hc : c ∈ TriangularSet T

instance {T : Triangle} (sT : SubTriangle T) : CoeDep (SubTriangle T) sT Triangle where coe := SubTriangle.toTriangle sT

def constructSubTriangle (coveringTriangle : Triangle) (a1 b1 c1 a2 b2 c2 a3 b3 c3 : ℝ)
  (hsum1 : a1+b1+c1 = 1 := by ring) (hsum2 : a2+b2+c2 = 1 := by ring) (hsum3 : a3+b3+c3 = 1 := by ring)
  (gtz : a1 ≥ 0 ∧ b1 ≥ 0 ∧ c1 ≥ 0 ∧ a2 ≥ 0 ∧ b2 ≥ 0 ∧ c2 ≥ 0 ∧ a3 ≥ 0 ∧ b3 ≥ 0 ∧ c3 ≥ 0
   := by (repeat' constructor); all_goals {linarith}) : SubTriangle coveringTriangle
  := by
  have ⟨a1gtz, b1gtz, c1gtz, a2gtz, b2gtz, c2gtz, a3gtz, b3gtz, c3gtz⟩ := gtz
  exact {
    a := coveringTriangle.a * a1 + coveringTriangle.b * b1 + coveringTriangle.c * c1
    b := coveringTriangle.a * a2 + coveringTriangle.b * b2 + coveringTriangle.c * c2
    c := coveringTriangle.a * a3 + coveringTriangle.b * b3 + coveringTriangle.c * c3
    ha := ⟨a1, b1, c1, a1gtz, b1gtz, c1gtz, hsum1, by simp; ring⟩
    hb := ⟨a2, b2, c2, a2gtz, b2gtz, c2gtz, hsum2, by simp; ring⟩
    hc := ⟨a3, b3, c3, a3gtz, b3gtz, c3gtz, hsum3, by simp; ring⟩
  }

noncomputable def subTriangleA (coveringTriangle : Triangle) :=
  constructSubTriangle coveringTriangle 1 0 0 (1/2) (1/2) 0 (1/2) 0 (1/2)

noncomputable def subTriangleB (coveringTriangle : Triangle) :=
  constructSubTriangle coveringTriangle (1/2) (1/2) 0 0 1 0 0 (1/2) (1/2)

noncomputable def subTriangleC (coveringTriangle : Triangle) :=
  constructSubTriangle coveringTriangle (1/2) 0 (1/2) 0 (1/2) (1/2) 0 0 1

noncomputable def subTriangleD (coveringTriangle : Triangle) :=
  constructSubTriangle coveringTriangle (1/2) (1/2) 0 0 (1/2) (1/2) (1/2) 0 (1/2)
