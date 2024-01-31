import Mathlib.Data.Set.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic
import Mathlib.Data.Complex.Basic

import Cauchy.definitions.linear_path
import Cauchy.definitions.path_integrals
import Cauchy.helpers.piecewise_paths

open helpers Set

namespace definitions

structure Triangle where
  a : ℂ
  b : ℂ
  c : ℂ

def Trivial (triangle : Triangle) : Prop :=
  triangle.a = triangle.b ∧ triangle.b = triangle.c

def Distinct (triangle : Triangle) : Prop :=
  triangle.a ≠ triangle.b ∧ triangle.b ≠ triangle.c ∧ triangle.c ≠ triangle.a

-- unsure about computability, but actually may not be on further reflection
def Triangle.path (triangle : Triangle) : PiecewisePath 3 :=
  {
    paths := ![LinearPath.mk triangle.a triangle.b,
               LinearPath.mk triangle.b triangle.c,
               LinearPath.mk triangle.c triangle.a]
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

lemma perimeter_nonneg (triangle : Triangle) : perimeter triangle ≥ 0 := by
  unfold perimeter
  repeat apply add_nonneg
  all_goals apply dist_nonneg

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

lemma boundary_in_set {T : Triangle} : TriangularBoundary T ⊆ TriangularSet T := by
  unfold TriangularBoundary TriangularSet
  repeat intro x
  simp at *
  have ⟨a, b, c, d, e, f, g, _, i⟩ := x
  exact ⟨a, b, c, d, e, f, g, i⟩

def TriangularInterior (triangle : Triangle) : Set ℂ :=
  {z | ∃ (t₁ t₂ t₃ : ℝ), t₁ > 0 ∧ t₂ > 0 ∧ t₃ > 0 ∧
    t₁ + t₂ + t₃ = 1 ∧ (z = t₁*triangle.a + t₂*triangle.b + t₃*triangle.c) }

def interior_in_set {T : Triangle} : TriangularInterior T ⊆ TriangularSet T := by
  unfold TriangularInterior TriangularSet
  repeat intro x
  simp at *
  have ⟨a, b, c, d, e, f, g, i⟩ := x
  exact ⟨a, le_of_lt b, c, le_of_lt d, e, le_of_lt f, g, i⟩

lemma triangle_union (T : Triangle) :
  TriangularSet T = TriangularBoundary T ∪ TriangularInterior T := by
  apply Set.Subset.antisymm
  . rewrite [TriangularBoundary, TriangularInterior, TriangularSet,
    Set.subset_def]
    intro x ⟨a, b, c, gtza, gtzb, gtzc, sum, defx⟩
    by_cases a*b*c=0
    apply Or.inl
    exact ⟨a, b, c, gtza, gtzb, gtzc, sum, h, defx⟩
    apply Or.inr
    simp at h; push_neg at h; have ⟨⟨na, nb⟩, nc⟩ := h
    exact ⟨a, b, c, Ne.lt_of_le (Ne.symm na) gtza, Ne.lt_of_le (Ne.symm nb) gtzb,
            Ne.lt_of_le (Ne.symm nc) gtzc, sum, defx⟩
  . exact Set.union_subset boundary_in_set interior_in_set

def LinIndep (T : Triangle) : Prop :=
  LinearIndependent ℝ ![T.a-T.c, T.b-T.c]

lemma linindep_not_trivial (T : Triangle) : LinIndep T → Distinct T := by
  contrapose
  unfold Distinct LinIndep
  repeat rewrite [not_and_or]
  intro ne
  simp only [ne_eq, not_not] at ne
  rcases ne with h | h | h
  all_goals
    rewrite [LinearIndependent.pair_iff]
    push_neg
  . use 1, -1
    rewrite [h]
    simp
  . use 0, 1
    rewrite [h]
    simp
  . use 1, 0
    rewrite [h]
    simp

end definitions
