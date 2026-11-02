import AcceleratedLogConcave.Kinetic.ConditionalContraction.HamiltonianPoisson
import AcceleratedLogConcave.Kinetic.ConditionalContraction.FieldCentering
import AcceleratedLogConcave.Kinetic.PositionGradient

/-! The Hamiltonian image of the actual elliptic corrector adjoint. -/
noncomputable section
open MeasureTheory InnerProductSpace ProbabilityTheory
open scoped ContDiff RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.ConditionalContraction
open Analysis.WeightedGradient Analysis.Poisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [IsProbabilityMeasure μ] (V : E → ℝ)
  (hV : ContDiff ℝ 2 V) (hI : Integrable (fun x => Real.exp (-V x)))
  (hμ : μ = volume.tilted (fun x => -V x))
  (m L : ℝ) (hm : 0 < m)
  (hlower : ∀ x a, m * ‖a‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x a a)
  (hupper : ∀ x a, fderiv ℝ (fderiv ℝ V) x a a ≤ L * ‖a‖ ^ 2)

/-- The genuine adjoint corrector has a microscopic Hamiltonian image whose
squared norm has the exact Gaussian coefficient. The only hypotheses are the
potential assumptions used to construct the actual Poisson inverse. -/
theorem gaussianCorrectorAdjoint_hamiltonian_image
    (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) (s n : ℝ) :
    ∃ K : Lp ℝ 2 (gaussianPhaseMeasure μ),
      gaussianPositionProjection μ K = 0 ∧
      ‖K‖ ^ 2 ≤ (2 * s ^ 2 + n ^ 2) * ‖gaussianPositionProjection μ f‖ ^ 2 ∧
      ∀ (φ : GaussianPhase E → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
        Integrable (fun z => (gaussianCorrector μ V hV hI hμ m L hm hlower hupper).adjoint f z *
          hamiltonianTestDerivative V s n φ z) (gaussianPhaseMeasure μ) ∧
        (∫ z, (gaussianCorrector μ V hV hI hμ m L hm hlower hupper).adjoint f z *
          hamiltonianTestDerivative V s n φ z ∂gaussianPhaseMeasure μ) =
          (∫ z, φ z * K z ∂gaussianPhaseMeasure μ) +
            s * ∫ z, φ z * centerForcing μ (gaussianAverage μ f) z.1.1 ∂gaussianPhaseMeasure μ := by
  classical
  obtain ⟨R, hR, _, _, hbound⟩ :=
    gaussianCorrectorAdjoint_weakPositionGradient_sharp μ V hV hI hμ m L hm hlower hupper f
  refine ⟨hamiltonianField μ (stdOrthonormalBasis ℝ E) (rowCoefficients μ R) s n,
    gaussianPositionProjection_hamiltonianField μ _ _ _ _, ?_, ?_⟩
  · apply (hamiltonianField_rows_norm_sq_le μ R s n).trans
    change (2 * s ^ 2 + n ^ 2) * (∑ i, ‖R i‖ ^ 2) ≤
      (2 * s ^ 2 + n ^ 2) * ‖positionEmbedding μ (gaussianAverage μ f)‖ ^ 2
    rw [(positionEmbedding μ).norm_map]
    exact mul_le_mul_of_nonneg_left hbound (by positivity)
  · intro φ hφ hc
    have hw := (poissonSolution_spec (μ := μ) (V := V) (hV := hV) (hI := hI)
      (hμ := hμ) (m := m) (L := L) (hm := hm) (hlower := hlower) (hupper := hupper)
      (gaussianAverage μ f)).2
    have hi := phase_hamiltonian_poisson_ibp μ V (hV.of_le (by norm_num)) hI hμ
      (gradientPoissonInverse μ V hV hI hμ m L hm hlower hupper (gaussianAverage μ f))
      (centerForcing μ (gaussianAverage μ f)) hw R hR s n φ hφ hc
    simpa only [gaussianCorrector_adjoint, ContinuousLinearMap.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap] using hi

end AcceleratedLogConcave.Kinetic.ConditionalContraction
