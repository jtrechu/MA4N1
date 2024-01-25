import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Cauchy.definitions.path
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic

open Set
open MeasureTheory
open unitInterval Finset BigOperators
open definitions

namespace definitions

-- Again, we had to change things in the groundwork, starting by the definition of what is considered as a path integral. This has been more challenging as it may seem,
-- since until we created the final structure C1Path, it was difficult to deal with all the coercions and confusing things we got when unfolding pathIntegral1' in 
-- order to prove properties related to path integrals.
noncomputable def aux (f : ℂ → ℂ) (γ : C1Path) : ℝ → ℂ :=
  f ∘ γ * deriv γ

noncomputable def pathIntegral1' (f : ℂ → ℂ) (γ : C1Path ) : ℂ :=
  ∫t in (0)..(1), (aux f γ) t ∂volume

noncomputable def pathIntegral1 {n : ℕ} (f : ℂ → ℂ) (p : PiecewisePath n) : ℂ :=
  ∑ i, pathIntegral1' f (p.paths i)

noncomputable def pathIntegral_bounds (f : ℂ → ℂ) (γ : C1Path) (a b : ℝ) : ℂ :=
  ∫t in (a)..(b), (aux f γ) t ∂volume

noncomputable def length (γ : C1Path) : ℝ :=
∫ t in (0)..(1), Complex.abs (deriv γ t) ∂volume

end definitions
