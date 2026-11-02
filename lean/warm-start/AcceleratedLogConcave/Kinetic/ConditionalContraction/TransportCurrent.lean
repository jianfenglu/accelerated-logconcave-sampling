import AcceleratedLogConcave.Kinetic.ConditionalContraction.CorrectorHamiltonian
import AcceleratedLogConcave.Kinetic.ConditionalContraction.PositionHamiltonian

/-! The source transport-current bound for the actual elliptic corrector. -/
noncomputable section
open MeasureTheory InnerProductSpace ProbabilityTheory
open scoped ContDiff RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.ConditionalContraction
open Analysis.Poisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [BorelSpace E] in
/-- Pairing a genuinely microscopic field only sees the microscopic input. -/
theorem inner_microscopic (μ : Measure E) [IsProbabilityMeasure μ]
    (K f : Lp ℝ 2 (gaussianPhaseMeasure μ)) (hK : gaussianPositionProjection μ K = 0) :
    inner ℝ K f = inner ℝ K (f - gaussianPositionProjection μ f) := by
  rw [inner_sub_right, ← ContinuousLinearMap.adjoint_inner_left,
    gaussianPositionProjection_adjoint, hK, inner_zero_left, sub_zero]

variable (μ : Measure E) [IsProbabilityMeasure μ] (V : E → ℝ)
  (hV : ContDiff ℝ 2 V) (hI : Integrable (fun x => Real.exp (-V x)))
  (hμ : μ = volume.tilted (fun x => -V x)) (m L : ℝ) (hm : 0 < m)
  (hlower : ∀ x a, m * ‖a‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x a a)
  (hupper : ∀ x a, fderiv ℝ (fderiv ℝ V) x a a ≤ L * ‖a‖ ^ 2)

/-- The actual Hamiltonian contribution to the derivative of `<Af,f>` on a
compact C1 density core, with the manuscript's fixed velocity split. -/
def hamiltonianCorrectorCurrent (f : Lp ℝ 2 (gaussianPhaseMeasure μ))
    (φ : GaussianPhase E → ℝ) : ℝ :=
  -(∫ z, (gaussianCorrector μ V hV hI hμ m L hm hlower hupper).adjoint f z *
    hamiltonianTestDerivative V (1/2) (Real.sqrt 3/2) φ z ∂gaussianPhaseMeasure μ) -
  (∫ z, gaussianCorrector μ V hV hI hμ m L hm hlower hupper f z *
    hamiltonianTestDerivative V (1/2) (Real.sqrt 3/2) φ z ∂gaussianPhaseMeasure μ)

/-- The source transport-current estimate, derived from the actual Hamiltonian
IBP identities and actual weak Hessian estimates. Centering and a compact C1
representative are the only assumptions on the density. -/
theorem hamiltonianCorrectorCurrent_le
    (f : Lp ℝ 2 (gaussianPhaseMeasure μ))
    (hmean : mean μ (gaussianAverage μ f) = 0)
    (φ : GaussianPhase E → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hf : f =ᵐ[gaussianPhaseMeasure μ] φ) :
    hamiltonianCorrectorCurrent μ V hV hI hμ m L hm hlower hupper f φ ≤
      -(1/4 : ℝ) * ‖gaussianPositionProjection μ f‖ ^ 2 +
        (9/4 : ℝ) * ‖f - gaussianPositionProjection μ f‖ ^ 2 := by
  obtain ⟨K, hK, hk, hweakK⟩ := gaussianCorrectorAdjoint_hamiltonian_image
    μ V hV hI hμ m L hm hlower hupper f (1/2) (Real.sqrt 3/2)
  obtain ⟨B, hB, hb, hweakB⟩ := gaussianCorrector_hamiltonian_image
    μ V hV hI hμ m L hm hlower hupper f (1/2) (Real.sqrt 3/2) source_split_coefficients
  have hcoef : 2 * (1/2 : ℝ)^2 + (Real.sqrt 3/2)^2 = 5/4 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
  rw [hcoef] at hk
  have hpair (Q : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
      (∫ z, φ z * Q z ∂gaussianPhaseMeasure μ) = inner ℝ Q f := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf] with z hz
    rw [hz]
    rfl
  have hcenter : centerForcing μ (gaussianAverage μ f) = gaussianAverage μ f := by
    rw [centerForcing_apply, hmean, zero_smul, sub_zero]
  have hmacro : (∫ z, φ z * centerForcing μ (gaussianAverage μ f) z.1.1 ∂gaussianPhaseMeasure μ) =
      ‖gaussianPositionProjection μ f‖^2 := by
    rw [hcenter]
    calc
      _ = ∫ z, φ z * gaussianPositionProjection μ f z ∂gaussianPhaseMeasure μ := by
        apply integral_congr_ae
        filter_upwards [positionEmbedding_coe μ (gaussianAverage μ f)] with z hz
        rw [show gaussianPositionProjection μ f z = _ from hz]
      _ = inner ℝ (gaussianPositionProjection μ f) f := hpair _
      _ = _ := by
        have hh := (gaussianPositionProjection μ).adjoint_inner_left f (gaussianPositionProjection μ f)
        rw [gaussianPositionProjection_adjoint, gaussianPositionProjection_idempotent,
          real_inner_self_eq_norm_sq] at hh
        exact hh
  have hcur : hamiltonianCorrectorCurrent μ V hV hI hμ m L hm hlower hupper f φ =
      -(1/2 : ℝ) * ‖gaussianPositionProjection μ f‖^2 -
        inner ℝ K (f - gaussianPositionProjection μ f) +
        inner ℝ B (f - gaussianPositionProjection μ f) := by
    rw [hamiltonianCorrectorCurrent, (hweakK φ hφ hc).2, (hweakB φ hφ hc).2,
      hpair, hpair, hmacro, inner_microscopic μ K f hK, inner_microscopic μ B f hB]
    ring
  rw [hcur]
  have hkpair := neg_le_abs (inner ℝ K (f - gaussianPositionProjection μ f))
  have hkabs := abs_real_inner_le_norm K (f - gaussianPositionProjection μ f)
  have hbpair := real_inner_le_norm B (f - gaussianPositionProjection μ f)
  have hbn := mul_le_mul_of_nonneg_right hb (norm_nonneg (f - gaussianPositionProjection μ f))
  nlinarith [sq_nonneg (‖K‖ - (5/2 : ℝ) * ‖f - gaussianPositionProjection μ f‖)]

end AcceleratedLogConcave.Kinetic.ConditionalContraction
