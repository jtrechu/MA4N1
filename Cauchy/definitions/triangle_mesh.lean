import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Data.Complex.Basic
import Cauchy.definitions.triangle
import Cauchy.definitions.path_integrals

open definitions Complex BigOperators

namespace definitions

/--
-- If we had more time we would prove that circle integrals are a limit of triangle
-- integrals. This mesh would allow us to do that.
-/

noncomputable def linterp (a b : ℝ) (p n : ℕ) := a + (b-a) * (p / n)

noncomputable def segment_mesh {n : ℕ} (r θ φ : ℝ) (p : Fin n): Triangle :=
  {
    a := r * (cos (linterp θ φ p (n+1)) + I * sin (linterp θ φ p (n+1)))
    b := r * (cos (linterp θ φ (p+1) (n+1)) + I * sin (linterp θ φ (p+1) (n+1)))
    c := r * (cos φ + I * sin φ)
  }

-- lemma segment_integral {n : ℕ} (f : ℂ → ℂ) (θ φ : ℝ) (p : Fin n) (hn : n > 0) :
--   ∑i : Fin n, trianglePathIntegral f (segment_mesh r θ φ i) =
--   ∑j : Fin (Nat.succ n), pathIntegral1' f (
--     LinearPath.mk (r * (cos (linterp θ φ j (n+1)) + I * sin (linterp θ φ j (n+1))))
--                   (r * (cos (linterp θ φ (j+1) (n+1)) + I * sin (linterp θ φ (j+1) (n+1))))
--     ) + pathIntegral1' f (LinearPath.mk
--       (r * (cos φ + I * sin φ)) (r * (cos θ + I * sin θ))
--     ) := by
--   unfold segment_mesh
