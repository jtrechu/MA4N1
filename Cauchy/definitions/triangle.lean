import Mathlib.Data.Set.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic
import Mathlib.Data.Complex.Basic

import Cauchy.definitions.linear_path
import Cauchy.definitions.path_integrals
import Cauchy.helpers.piecewise_paths

open helpers

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

lemma trianglePathIntegral_apply (f : ℂ → ℂ) (T : Triangle) : trianglePathIntegral f T =
  pathIntegral1' f (LinearPath.mk T.a T.b) +
  pathIntegral1' f (LinearPath.mk T.b T.c) +
  pathIntegral1' f (LinearPath.mk T.c T.a) := by
  unfold trianglePathIntegral
  rewrite [PiecewisePath.path_integral_three]
  unfold Triangle.path PiecewisePath.paths
  aesop

noncomputable def perimeter (triangle : Triangle) : ℝ :=
  dist triangle.b triangle.a +
  dist triangle.c triangle.b +
  dist triangle.a triangle.c

def TriangularSet (triangle : Triangle) : Set ℂ :=
  {z | ∃ (t₁ t₂ t₃ : ℝ), t₁ ≥ 0 ∧ t₂ ≥ 0 ∧ t₃ ≥ 0 ∧
    t₁ + t₂ + t₃ = 1 ∧
    (z = t₁*triangle.a + t₂*triangle.b + t₃*triangle.c) }

def Triangle.contains_a (T : Triangle) : T.a ∈ TriangularSet T := by
  unfold TriangularSet
  simp only [ge_iff_le, exists_and_left, Set.mem_setOf_eq]
  exact ⟨1, zero_le_one, 0, (by exact Eq.le rfl), 0, (by exact Eq.le rfl), by simp, by simp⟩

def Triangle.contains_b (T : Triangle) : T.b ∈ TriangularSet T := by
  unfold TriangularSet
  simp only [ge_iff_le, exists_and_left, Set.mem_setOf_eq]
  exact ⟨0, (by exact Eq.le rfl), 1, zero_le_one, 0, (by exact Eq.le rfl), by simp, by simp⟩

def Triangle.contains_c (T : Triangle) : T.c ∈ TriangularSet T := by
  unfold TriangularSet
  simp only [ge_iff_le, exists_and_left, Set.mem_setOf_eq]
  exact ⟨0, (by exact Eq.le rfl), 0, (by exact Eq.le rfl), 1, zero_le_one, by simp, by simp⟩

lemma Triangle.Nonempty (triangle : Triangle) : Set.Nonempty $ TriangularSet triangle := by
  rewrite [Set.Nonempty]
  exact ⟨triangle.a, triangle.contains_a⟩

def TriangularBoundary (triangle : Triangle) : Set ℂ :=
  {z | ∃ (t₁ t₂ t₃ : ℝ), t₁ ≥ 0 ∧ t₂ ≥ 0 ∧ t₃ ≥ 0 ∧
    t₁ + t₂ + t₃ = 1 ∧ t₁*t₂*t₃ = 0 ∧
    (z = t₁*triangle.a + t₂*triangle.b + t₃*triangle.c) }

end definitions
