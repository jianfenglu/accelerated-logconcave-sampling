import AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
import Mathlib.Analysis.InnerProductSpace.Trace

/-! The actual weighted Stein columns, including their sign and basis change.
These identities use original Data and contain no stationary-jet assumptions. -/
noncomputable section
open scoped ContDiff
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Conditional CenteringFlowLp
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "e" => EuclideanSpace.basisFun (Fin D) ℝ

private theorem fluxDivergence_eq_basis (J : E → E) (y : E)
    (hJ : DifferentiableAt ℝ J y) :
    Analysis.Poisson.fluxDivergence J y =
      ∑ i, fderiv ℝ (fun z => inner ℝ (e i) (J z)) y (e i) := by
  have he (v w : E) : fderiv ℝ (fun z => inner ℝ v (J z)) y w =
      inner ℝ v (fderiv ℝ J y w) := by
    exact congrArg (fun L : E →L[ℝ] ℝ => L w)
      ((innerSL ℝ v).hasFDerivAt.comp y hJ.hasFDerivAt).fderiv
  simp_rw [Analysis.Poisson.fluxDivergence,he]
  exact (LinearMap.trace_eq_sum_inner (fderiv ℝ J y).toLinearMap
    (stdOrthonormalBasis ℝ E)).symm.trans
      (LinearMap.trace_eq_sum_inner (fderiv ℝ J y).toLinearMap e)

def sourceScore (d : Data (Fin D)) (y : E) : E := y + (d.r*d.b) • M d y

theorem source_weighted_divergence (d : Data (Fin D)) (y g : E) :
    inner ℝ (sourceScore d y) (K d y g) -
      Analysis.Poisson.fluxDivergence (fun z => K d z g) y =
    inner ℝ (M d y - meanOffset d) g := by
  have hK := Centering.sourceKernel_contDiff_one d.hF d.hell d.hlo d.hup
    d.x d.hr d.hb d.hb1 d.hsmall
  have hs := Centering.source_pointwise_stein_of_contDiff d.hF d.hell d.hlo d.hup
    d.x d.hr d.hb d.hb1 d.hsmall hK y g
  have hd := (hasFDerivAt_interpolationDensity d.hF d.hlo d.hup d.x d.r
    (by linarith [d.hb] : -1 < d.b) d.hb1 y).fderiv
  rw [hd] at hs
  simp only [smul_apply,innerSL_apply_apply,smul_eq_mul] at hs
  have hp : 0 < interpolationDensity d.F d.x d.r d.b y :=
    interpolationDensity_pos d.hF d.hlo d.x d.r d.b
      (conditionalVariance_pos (by linarith [d.hb]) d.hb1) y
  change -interpolationDensity d.F d.x d.r d.b y * inner ℝ (sourceScore d y) (K d y g) +
      interpolationDensity d.F d.x d.r d.b y * Analysis.Poisson.fluxDivergence
        (fun z => K d z g) y =
      -interpolationDensity d.F d.x d.r d.b y * inner ℝ (M d y - meanOffset d) g at hs
  apply mul_left_cancel₀ (ne_of_gt hp)
  nlinarith [hs]

/-- δ_y K equals the centered mean, in the actual coordinate basis. -/
theorem source_weighted_column (d : Data (Fin D)) (y : E) (j : Fin D) :
    (∑ i, (- fderiv ℝ (fun z => inner ℝ (e i) (K d z (e j))) y (e i) +
      inner ℝ (sourceScore d y) (e i) * inner ℝ (e i) (K d y (e j)))) =
    inner ℝ (M d y - meanOffset d) (e j) := by
  have hK := (Centering.sourceKernel_contDiff_one d.hF d.hell d.hlo d.hup
    d.x d.hr d.hb d.hb1 d.hsmall).differentiable (by norm_num) y
  have hJ : DifferentiableAt ℝ (fun z => K d z (e j)) y :=
    hK.clm_apply (differentiableAt_const _)
  have hs := source_weighted_divergence d y (e j)
  rw [fluxDivergence_eq_basis _ y hJ] at hs
  rw [Finset.sum_add_distrib,Finset.sum_neg_distrib,OrthonormalBasis.sum_inner_mul_inner e]
  linarith

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
