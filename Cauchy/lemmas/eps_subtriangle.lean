import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Data.Complex.Basic
import Cauchy.definitions.eps_subtriangle
import Cauchy.definitions.triangle
import Mathlib.LinearAlgebra.LinearIndependent

open definitions

namespace lemmas

-- Firstly we prove that ε-triangles as we have defined them are not segments, nor points (i.e. they are linearly independent)

lemma eps_subtriangle_linindep (T : Triangle) (z : ℂ) (hz : z ∈ (interior $ TriangularSet T))
  (ε : ℝ) (hε : ε > 0) : LinIndep $ eps_subtriangle z hz ε hε := by
  unfold LinIndep eps_subtriangle
  simp
  rewrite [LinearIndependent.pair_iff]
  intro s t hst
  simp only [ge_iff_le, smul_add, Complex.real_smul, Complex.ext_iff] at hst
  ring_nf at hst
  simp at hst -- simps are huge, best not unfold
  have : min ε (point_around z hz) ≠ 0 := by
    rewrite [ne_iff_lt_or_gt]
    apply Or.inr
    apply lt_min hε
    exact (point_around_apply z hz).1
  have sz : s = 0 := by
    rewrite [←or_false (p:=s = 0)]
    convert hst.2
    rewrite [false_iff]
    exact this
  rewrite [sz] at hst
  simp at hst
  refine ⟨sz, ?_⟩
  rewrite [←or_false (p:=t = 0)]
  convert hst.symm
  rewrite [false_iff]
  exact this

-- We now prove that if we build an ε-triangle around the point z, z will not only be in the ε-triangle
-- but it will also be in the interior of the ε-triangle

lemma eps_subtriange_mem_interior (T : Triangle) (z : ℂ) (hz : z ∈ (interior $ TriangularSet T))
  (ε : ℝ) (hε : ε > 0) : z ∈ (TriangularInterior $ eps_subtriangle z hz ε hε) := by
  unfold TriangularInterior
  refine ⟨(1/3), (1/3), (1/3), by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  unfold eps_subtriangle
  simp only [one_div, Complex.ofReal_inv, Complex.ofReal_ofNat, ge_iff_le]
  ring
