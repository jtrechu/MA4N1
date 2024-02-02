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

-- With the C1Path structure and the PiecewisePath structure we can now define the path integral

-- For C1 paths we define it naturally as a interval integral of a ℝ valued function

noncomputable def aux (f : ℂ → ℂ) (γ : C1Path) : ℝ → ℂ :=
  f ∘ γ * deriv γ

noncomputable def pathIntegral1' (f : ℂ → ℂ) (γ : C1Path ) : ℂ :=
  ∫t in (0)..(1), (aux f γ) t ∂volume

-- For pieceWise paths we define it as the sum of the pieces, with this we're defining the integral as it is
-- as it is usually defined, avoiding points where the path is continuous but not differentiable

noncomputable def pathIntegral1 {n : ℕ} (f : ℂ → ℂ) (p : PiecewisePath n) : ℂ :=
  ∑ i, pathIntegral1' f (p.paths i)

noncomputable def pathIntegral_bounds (f : ℂ → ℂ) (γ : C1Path) (a b : ℝ) : ℂ :=
  ∫t in (a)..(b), (aux f γ) t ∂volume

--We also define the lenghts of C1Paths

noncomputable def length (γ : C1Path) : ℝ :=
∫ t in (0)..(1), Complex.abs (deriv γ t) ∂volume

end definitions
