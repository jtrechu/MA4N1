import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Calculus.Dslope
import Mathlib.Data.Complex.Basic
import Cauchy.definitions.triangle
import Cauchy.definitions.path_integrals
import Cauchy.definitions.domain
import Cauchy.helpers.triangle
import Cauchy.lemmas.zero_le_of_gt_zero
import Cauchy.integral_zero._1_triangle_sequence
import Cauchy.integral_zero._4_integral_bound
import Cauchy.integral_formula.sorryed_out_lemmas

open definitions lemmas helpers.triangle sorrylemmas
variable {U : Set ℂ}

lemma UOpen (hU : IsCDomain U) : IsOpen U := by
  unfold IsCDomain at hU
  exact hU.1

lemma U_Punctured_Open (hU : IsCDomain U) : IsOpen (U\{z}) := by
have hz : IsOpen {z}ᶜ  := by exact isOpen_compl_singleton
apply IsOpen.inter (UOpen hU) hz

lemma trivialU : (U\{z}) ⊆ U := by simp_all only [Set.diff_singleton_subset_iff, Set.subset_insert]

lemma dslope_integral_0 {T : Triangle} {f : ℂ → ℂ} (hU: IsCDomain U)
(hT : TriangularBoundary T ⊆ U) (z : ℂ) (hfD : DifferentiableOn ℂ f U) ( hz : z ∈ TriangularBoundary T):
trianglePathIntegral (dslope f z) T = 0 := by
unfold IsCDomain at hU
have  hfC : ContinuousOn f U := by exact DifferentiableOn.continuousOn hfD
have zinU : z ∈ U := by exact hT hz
have Uopen : IsOpen U := by exact UOpen hU
have U_nhd : (U ∈ nhds z) := by
  exact (IsOpen.mem_nhds (Uopen) zinU )
have hderivAt : DifferentiableAt ℂ  f z := by exact DifferentiableOn.differentiableAt hfD U_nhd
have gCont : ContinuousOn f U ∧DifferentiableAt ℂ  f z  := by exact ⟨hfC,hderivAt⟩
rw[←continuousOn_dslope U_nhd] at gCont
have znotInPuncturedU : z∉(U\{z}) := by simp
have hgD : DifferentiableOn ℂ f (U\{z}) := by apply DifferentiableOn.mono hfD trivialU
rw[←differentiableOn_dslope_of_nmem znotInPuncturedU] at hgD
exact(cauchy_for_triangles_generalised hU hT z gCont hgD)

lemma dslope_split {T : Triangle} {f : ℂ → ℂ} (hU: IsCDomain U)
(hT : TriangularBoundary T ⊆ U) (z : ℂ) (hfD : DifferentiableOn ℂ f U) ( hz : z ∈ TriangularBoundary T):
trianglePathIntegral (dslope f z) T = trianglePathIntegral ((fun x => f x/(x-z))) T - trianglePathIntegral ((fun x => f z/(x-z))) T := by
sorry

lemma dslope_split' {T : Triangle} {f : ℂ → ℂ} (hU: IsCDomain U)
(hT : TriangularBoundary T ⊆ U) (z : ℂ) (hfD : DifferentiableOn ℂ f U) ( hz : z ∈ TriangularBoundary T):
trianglePathIntegral ((fun x => f x/(x-z))) T = trianglePathIntegral ((fun x => f z/(x-z))) T := by
have : trianglePathIntegral (dslope f z) T = trianglePathIntegral ((fun x => f x/(x-z))) T - trianglePathIntegral ((fun x => f z/(x-z))) T :=
  by exact dslope_split hU hT z hfD hz
rw[dslope_integral_0 hU hT z hfD hz] at this
rw[eq_sub_iff_add_eq] at this
simp at this
rw[this]
