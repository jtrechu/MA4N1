import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.UnitInterval

import Cauchy.definitions.triangle
import Cauchy.definitions.path_integrals
import Cauchy.lemmas.mean_leq_max
import Cauchy.definitions.subtriangle

open definitions lemmas Classical
noncomputable def selectSubtriangle (f : ℂ → ℂ) (T : Triangle) : SubTriangle T := by
  have h := abs_ge_sum_4
    (trianglePathIntegral f (subTriangleA T)) (trianglePathIntegral f (subTriangleB T))
    (trianglePathIntegral f (subTriangleC T)) (trianglePathIntegral f (subTriangleD T))
    (sum:=trianglePathIntegral f T) (by sorry)
  exact ( Or.by_cases h (λ_=>subTriangleA T)
    λh => Or.by_cases h (λ_=>subTriangleB T)
    λh => Or.by_cases h (λ_=>subTriangleC T)
                         λ_=>subTriangleD T)

noncomputable def triangleSequence (f : ℂ → ℂ) (T : Triangle) (n : ℕ) : Triangle := by
  match n with
  | 0 => exact T
  | x + 1 => exact SubTriangle.toTriangle $ selectSubtriangle f (triangleSequence f T x)
