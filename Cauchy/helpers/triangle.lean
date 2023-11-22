import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Cauchy.definitions.triangle

open definitions

namespace helpers.triangle

def AddComponents : ℝ × ℝ × ℝ → ℝ := fun v => v.fst + v.snd.fst + v.snd.snd

def TrianglePoint (T : Triangle) : (ℝ × ℝ × ℝ) → ℂ :=
  λ v => v.fst * T.a + v.snd.fst * T.b + v.snd.snd * T.c

def R3_Pos := {v | ∃ a b c : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ v = (a, b, c) }

def TriangleInR3 := R3_Pos ∩ (AddComponents ⁻¹' {1})
