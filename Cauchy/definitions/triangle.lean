import Mathlib.Data.Set.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic
import Mathlib.Data.Complex.Basic

import Cauchy.definitions.linear_path
import Cauchy.definitions.path_integrals
import Cauchy.helpers.piecewise_paths

open helpers Set

namespace definitions

-- In this file we define the triangles we'll be working with, to start with we define the triangle as its three vertices

structure Triangle where
  a : ℂ
  b : ℂ
  c : ℂ

-- We'll say a triangle is trivial if its vertices are the same

def Trivial (triangle : Triangle) : Prop :=
  triangle.a = triangle.b ∧ triangle.b = triangle.c

-- We say it's distinct if all vertices are different

def Distinct (triangle : Triangle) : Prop :=
  triangle.a ≠ triangle.b ∧ triangle.b ≠ triangle.c ∧ triangle.c ≠ triangle.a

-- We'll now build triangles as paths. Triangles are the main reason we needed to define piece-wise paths
-- as they are not differentiable on their vertices. However a triangles is always a piece wise path of
-- its sides, which are linear paths of the vertices

def Triangle.path (triangle : Triangle) : PiecewisePath 3 :=
  {
    paths := ![LinearPath.mk triangle.a triangle.b,
               LinearPath.mk triangle.b triangle.c,
               LinearPath.mk triangle.c triangle.a]
  }

-- To later simplify readability we add this results that bring path Integrals and triangles together

noncomputable def trianglePathIntegral (f : ℂ → ℂ) (T : Triangle) := pathIntegral1 f T.path

lemma trianglePathIntegral_apply (f : ℂ → ℂ) (T : Triangle) : trianglePathIntegral f T =
  pathIntegral1' f (LinearPath.mk T.a T.b) +
  pathIntegral1' f (LinearPath.mk T.b T.c) +
  pathIntegral1' f (LinearPath.mk T.c T.a) := by
  unfold trianglePathIntegral
  rewrite [PiecewisePath.path_integral_three]
  unfold Triangle.path PiecewisePath.paths
  aesop

-- We now prove some basic properties of our triangles

-- Firstly we define the perimeter, and show it is a non-negative number:

noncomputable def perimeter (triangle : Triangle) : ℝ :=
  dist triangle.b triangle.a +
  dist triangle.c triangle.b +
  dist triangle.a triangle.c

lemma perimeter_nonneg (triangle : Triangle) : perimeter triangle ≥ 0 := by
  unfold perimeter
  repeat apply add_nonneg
  all_goals apply dist_nonneg

-- Now we define the set of points that are contained by the triangle:

def TriangularSet (triangle : Triangle) : Set ℂ :=
  {z | ∃ (t₁ t₂ t₃ : ℝ), t₁ ≥ 0 ∧ t₂ ≥ 0 ∧ t₃ ≥ 0 ∧
    t₁ + t₂ + t₃ = 1 ∧
    (z = t₁*triangle.a + t₂*triangle.b + t₃*triangle.c) }

-- We show that the vertices belong to the triangular set, and also that as a result of this the set is not empty

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

-- We now define the boundary of our triangle and prove that it is contained in the triangular set:

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

-- Now we define the interior of the triangle and show that it is inside the set

def TriangularInterior (triangle : Triangle) : Set ℂ :=
  {z | ∃ (t₁ t₂ t₃ : ℝ), t₁ > 0 ∧ t₂ > 0 ∧ t₃ > 0 ∧
    t₁ + t₂ + t₃ = 1 ∧ (z = t₁*triangle.a + t₂*triangle.b + t₃*triangle.c) }

def interior_in_set {T : Triangle} : TriangularInterior T ⊆ TriangularSet T := by
  unfold TriangularInterior TriangularSet
  repeat intro x
  simp at *
  have ⟨a, b, c, d, e, f, g, i⟩ := x
  exact ⟨a, le_of_lt b, c, le_of_lt d, e, le_of_lt f, g, i⟩

-- Now we show that the triangular set is the union of interior and boundary

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

--We now show that if a triangle is linearly independent then it is distinct, since two of the sides are not
--paralel and therefore the triangle is neither a segment nor a point

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
