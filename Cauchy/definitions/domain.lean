import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Data.Complex.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

namespace definitions

def IsCDomain (U : Set ℂ ) : Prop := --called CDomain as Domain is already defined as the algebra object
  IsOpen U ∧ SimplyConnectedSpace U

end definitions
