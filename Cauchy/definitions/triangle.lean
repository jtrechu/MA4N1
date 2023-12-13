import Mathlib.Data.Set.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic
import Mathlib.Data.Complex.Basic

import Cauchy.definitions.linear_path

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
noncomputable def subTriangle (triangle : Triangle) : Triangle :=
  { a := (triangle.b + triangle.a)/2
    b := (triangle.c + triangle.b)/2
    c := (triangle.a + triangle.c)/2 : Triangle }

-- unsure about computability, but actually may not be on further reflection
def Triangle.path (triangle : Triangle) : PiecewisePath 3 :=
  {
    paths := λ i =>
      match i with
      | 0 => LinearPath.mk triangle.a triangle.b
      | 1 => LinearPath.mk triangle.b triangle.c
      | 2 => LinearPath.mk triangle.c triangle.a
  }

instance : Coe Triangle (PiecewisePath 3) where
  coe := λ t => t.path

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

noncomputable def subTriangleA (triangle : Triangle) : Triangle := --definitions added for proof
  { a := triangle.a                                                --of cauchy's theorem for triangles by Josh
    b := (subTriangle triangle).a
    c := (subTriangle triangle).c : Triangle }

noncomputable def subTriangleB (triangle : Triangle) : Triangle :=
  { a := (subTriangle triangle).a
    b := triangle.b
    c := (subTriangle triangle).b : Triangle }

noncomputable def subTriangleC (triangle : Triangle) : Triangle :=
  { a := (subTriangle triangle).c
    b := (subTriangle triangle).b
    c := triangle.c : Triangle }

end definitions
