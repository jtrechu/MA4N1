import Mathlib.Data.Set.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic
import Mathlib.Data.Complex.Basic

import Cauchy.definitions.linear_path
import Cauchy.definitions.path_integrals

namespace definitions

structure Triangle where
  a : ℂ
  b : ℂ
  c : ℂ

def Trivial (triangle : Triangle) : Prop :=
  triangle.a = triangle.b ∨
  ∃ t : ℝ, triangle.a + t * (triangle.b - triangle.a) = triangle.c

def nonTrivial (triangle : Triangle) : Prop :=
  ¬ Trivial triangle

-- unsure about computability, but actually may not be on further reflection
def Triangle.path (triangle : Triangle) : PiecewisePath 3 :=
  {
    paths := λ i =>
      match i with
      | 0 => LinearPath.mk triangle.a triangle.b
      | 1 => LinearPath.mk triangle.b triangle.c
      | 2 => LinearPath.mk triangle.c triangle.a
  }

noncomputable def trianglePathIntegral (f : ℂ → ℂ) (T : Triangle) := pathIntegral1 f T.path

noncomputable def perimeter (triangle : Triangle) : ℝ :=
  dist triangle.b triangle.a +
  dist triangle.c triangle.b +
  dist triangle.a triangle.c

def TriangularSet (triangle : Triangle) : Set ℂ :=
  {z | ∃ (t₁ t₂ t₃ : ℝ), t₁ ≥ 0 ∧ t₂ ≥ 0 ∧ t₃ ≥ 0 ∧
    t₁ + t₂ + t₃ = 1 ∧
    (z = t₁*triangle.a + t₂*triangle.b + t₃*triangle.c) }

lemma Triangle.Nonempty (triangle : Triangle) : Set.Nonempty $ TriangularSet triangle := by
  unfold TriangularSet
  rewrite [Set.Nonempty]
  refine ⟨triangle.a, 1, 0, 0, ?_⟩
  repeat constructor; norm_num
  simp

def TriangularBoundary (triangle : Triangle) : Set ℂ :=
  {z | ∃ (t₁ t₂ t₃ : ℝ), t₁ ≥ 0 ∧ t₂ ≥ 0 ∧ t₃ ≥ 0 ∧
    t₁ + t₂ + t₃ = 1 ∧ t₁*t₂*t₃ = 0 ∧
    (z = t₁*triangle.a + t₂*triangle.b + t₃*triangle.c) }

end definitions
