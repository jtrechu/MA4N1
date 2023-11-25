import Mathlib.Data.Set.Basic
import Cauchy.helpers.linear_paths
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic
import Mathlib.Data.Complex.Basic

namespace definitions
open helpers
open unitInterval

structure Triangle where
  a : ℂ
  b : ℂ
  c : ℂ

def nonTrivial (triangle : Triangle) : Prop :=
  triangle.a ≠ triangle.b ∧
  ¬ ∃ t : ℝ, triangle.a + t * (triangle.b - triangle.a) = triangle.c

-- unsure about computability, but actually may not be on further reflection
noncomputable def subTriangle (triangle : Triangle) : Triangle :=
  { a := (triangle.b + triangle.a)/2
    b := (triangle.c + triangle.b)/2
    c := (triangle.a + triangle.c)/2 : Triangle }

-- unsure about computability, but actually may not be on further reflection
noncomputable def path (triangle : Triangle) : helpers.ComplexPath triangle.a triangle.a :=
  let p1 := linear_path_a_b triangle.a triangle.b
  let p2 := linear_path_a_b triangle.b triangle.c
  let p3 := linear_path_a_b triangle.c triangle.a
  Path.trans (Path.trans p1 p2) p3

noncomputable def perimeter (triangle : Triangle) : ℝ :=
  dist triangle.b triangle.a +
  dist triangle.c triangle.b +
  dist triangle.a triangle.c

def TriangularSet (triangle : Triangle) : Set ℂ :=
  {z | ∃ (t₁ t₂ t₃ : ℝ), t₁ ≥ 0 ∧ t₂ ≥ 0 ∧ t₃ ≥ 0 ∧
    t₁ + t₂ + t₃ = 1 ∧
    (z = t₁*triangle.a + t₂*triangle.b + t₃*triangle.c) }

def TriangularBoundary (triangle : Triangle) : Set ℂ :=
  {z | ∃ (t₁ t₂ t₃ : ℝ), t₁ ≥ 0 ∧ t₂ ≥ 0 ∧ t₃ ≥ 0 ∧
    t₁ + t₂ + t₃ = 1 ∧ t₁*t₂*t₃ = 0 ∧
    (z = t₁*triangle.a + t₂*triangle.b + t₃*triangle.c) }

end definitions
