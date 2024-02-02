import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Field.Basic

import Cauchy.definitions.path
import Cauchy.definitions.path_integrals
import Cauchy.theorems.integral_restriction
import Cauchy.helpers.piecewise_paths
import Cauchy.lemmas.path_integral_integrable
import Cauchy.helpers.inequalities
import Cauchy.definitions.linear_path

open definitions helpers lemmas theorems

namespace theorems

-- The aim of this file is to apply some results of paths to linear paths particularly

-- We show that the result of splitting a linear path results in two linear paths

-- The first path in the piece-wise path will be a linear path from head to the split point

theorem linear_path_head_split (γ : LinearPath) (split : Set.Ioo 0 1) :
  ((PiecewisePath.paths $ C1Path.split γ split) 0).toFun =
  (LinearPath.mk γ.head (γ split)) := by
  unfold C1Path.split PiecewisePath.paths C1Path.transform
  simp
  rewrite [Function.funext_iff]
  intro a
  ring

-- The second path in the piece-wise path will be a linear path from the split point to the tail

theorem linear_path_split_tail (γ : LinearPath) (split : Set.Ioo 0 1) :
  ((PiecewisePath.paths $ C1Path.split γ split) 1).toFun =
  (LinearPath.mk (γ split) γ.tail) := by
  unfold C1Path.split PiecewisePath.paths C1Path.transform
  simp
  rewrite [Function.funext_iff]
  intro a
  ring

--We now show that the linear path when reversed just gives us the linear path with the
--head as the tail and vice-versa

theorem linear_path_reverse (γ : LinearPath) :
  (C1Path.reverse γ).toFun = LinearPath.mk γ.tail γ.head := by
  unfold C1Path.reverse
  simp
  rewrite [Function.funext_iff]
  intro a
  ring
