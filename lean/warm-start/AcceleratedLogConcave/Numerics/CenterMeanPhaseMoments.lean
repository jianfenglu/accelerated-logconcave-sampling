import AcceleratedLogConcave.Numerics.CenterMeanPhaseGibbsLaw
import AcceleratedLogConcave.Tensor.PhaseGibbsNetwork
import AcceleratedLogConcave.Conditional.PolynomialMoments

/-! Genuine partition integrability and ambient norm moments of the original
stationary phase law. These justify tails, not finished-expression moment bounds. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Conditional CenteringFlowLp
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))

theorem phasePartition_integrable (d : Data (Fin D)) :
    Integrable (fun z => Real.exp (-phasePotential d z)) phaseHaar := by
  unfold phaseHaar
  apply (integrable_map_equiv (phaseProductEquiv (D := D)).toHomeomorph.toMeasurableEquiv
    (fun z : EP => Real.exp (-phasePotential d z))).2
  have hsp := integrable_exp_neg_interpolationPotential d.hF d.hlo d.x d.r
    (by linarith [d.hb]) d.hb1
  have hga : Integrable (fun y : E => Real.exp (-Kinetic.Reheating.gaussianPotential y)) :=
    Kinetic.Reheating.gaussianPotential_integrable
  convert hsp.mul_prod hga using 1
  funext p
  change Real.exp (-phasePotential d (phaseProductEquiv p)) =
    Real.exp (-interpolationPotential d.F d.x d.r d.b p.1) *
      Real.exp (-Kinetic.Reheating.gaussianPotential p.2)
  rw [phasePotential_product]
  simp only [Kinetic.Reheating.gaussianPotential, neg_add, Real.exp_add]

/-- Norm moments survive the actual product-coordinate linear map. -/
theorem phaseSeedLaw_norm_moment (d : Data (Fin D)) (n : ℕ) :
    Integrable (fun z : EP => ‖z‖^n) (phaseSeedLaw d) := by
  rw [phaseSeedLaw_eq_productMap]
  apply (integrable_map_equiv (phaseProductEquiv (D := D)).toHomeomorph.toMeasurableEquiv
    (fun z : EP => ‖z‖^n)).2
  let μ := interpolationLaw d.F d.x d.r d.b
  let ν := stdGaussian E
  let : IsProbabilityMeasure μ := interpolationLaw_isProbabilityMeasure d.hF d.hlo d.x d.r d.b
  have hx : Integrable (fun x : E => ‖x‖^n) μ :=
    interpolationLaw_integrable_norm_pow d.hF d.hlo d.x d.r d.b n
  have hy : Integrable (fun y : E => ‖y‖^n) ν := by
    simpa only [id_eq] using
      (IsGaussian.memLp_id (stdGaussian E) n (by simp)).integrable_norm_pow'
  let L : (E × E) →L[ℝ] EP := (phaseProductEquiv (D := D)).toContinuousLinearMap
  have hi : Integrable (fun p : E × E =>
      ‖L‖^n * (‖p.1‖^n + ‖p.2‖^n)) (μ.prod ν) :=
    ((hx.comp_fst ν).add (hy.comp_snd μ)).const_mul (‖L‖^n)
  apply hi.mono' ((L.continuous.norm.pow n).aestronglyMeasurable)
  filter_upwards [] with p
  simp only [Pi.pow_apply, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  have hp : ‖p‖^n ≤ ‖p.1‖^n + ‖p.2‖^n := by
    rcases le_total ‖p.1‖ ‖p.2‖ with h | h
    · rw [Prod.norm_def, max_eq_right h]
      exact le_add_of_nonneg_left (pow_nonneg (norm_nonneg _) _)
    · rw [Prod.norm_def, max_eq_left h]
      exact le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) _)
  calc
    ‖L p‖^n ≤
        ‖L‖^n * ‖p‖^n := by
      simpa only [mul_pow] using
        pow_le_pow_left₀ (norm_nonneg _) (L.le_opNorm p) n
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (pow_nonneg (norm_nonneg _) _)

theorem phaseSeedLaw_hasMoments (d : Data (Fin D)) :
    Conditional.Appell.HasMoments (phaseSeedLaw d) := phaseSeedLaw_norm_moment d

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
