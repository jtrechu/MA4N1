import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.UnitInterval

import Cauchy.integral_zero._1_triangle_sequence
import Cauchy.lemmas.dist_tri_leq_perimeter
import Cauchy.lemmas.pow_seq_to_zero

open definitions lemmas Classical theorems

variable {U : Set ℂ} (f : ℂ → ℂ) (T : Triangle) (hU : IsCDomain U)
  (h₁ : DifferentiableOn ℂ f U) (h₂: TriangularBoundary T ⊆ U)

lemma exists_subtriangle_delta (w : ℂ) (hw : ∀n, w ∈ TriangularSet (triangleSequence f T hU h₁ h₂ n).triangle)
  : ∀δ>0, ∃n:ℕ, ∀z ∈ TriangularSet $ (triangleSequence f T hU h₁ h₂ n).triangle,
  ‖z-w‖ < δ := by
  intro d hd
  have ⟨n, hn⟩ := pow_seq_to_zero (perimeter T) 2 one_lt_two d hd
  refine ⟨n, ?_⟩
  intro z hz
  rewrite [←dist_eq_norm]
  apply lt_of_le_of_lt
  apply dist_tri_leq_perimeter (triangleSequence f T hU h₁ h₂ n).triangle
  constructor
  exact hw n
  exact hz
  rewrite [triangleSequence_perim]
  exact hn
