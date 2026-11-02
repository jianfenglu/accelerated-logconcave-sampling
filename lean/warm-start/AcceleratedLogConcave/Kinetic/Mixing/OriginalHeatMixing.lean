import AcceleratedLogConcave.Kinetic.Mixing.ClockKernel
import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.OriginalHeatVarianceSupplier
import AcceleratedLogConcave.Gibbs.OriginalStepParameters

/-!

-/
noncomputable section
open MeasureTheory ProbabilityTheory Set InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic
open Analysis.Poisson Reheating ConditionalContraction Gibbs

/-- Explicit scalar proof, without searching the large analytic context. -/
private theorem originalMixingVariance_pos {h : ℝ} (hh0 : 0 < h) :
    0 < 2 * h ^ 2 :=
  mul_pos (by norm_num) (sq_pos_of_pos hh0)

/-- Typed, semireducible name for exactly the original adapter, not new data. -/
def originalHeatMixingFamily {ι : Type*} [Fintype ι] {F : (EuclideanSpace ℝ ι) → ℝ} {κ h R : ℝ}
    (hF : ContDiff ℝ 2 F) (hκ : 0 < κ) (hh0 : 0 < h) (hR : 2 * h ^ 2 < R)
    (hlo : ∀ z v, κ⁻¹ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v)
    (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ ‖v‖ ^ 2) :
    VarianceHeatFamily (volume.tilted (fun x => -F x)) (3 * (2 * h ^ 2) / 4) R :=
  originalVarianceHeatFamily hF hκ (originalMixingVariance_pos hh0) hR hlo hup

/-- The exact proposed adapter has the original common witness on the executed
variance interval. It is NOT asserted constant up to R. -/
theorem originalVarianceHeatFamily_step_lower_eq {ι : Type*} [Fintype ι] {F : (EuclideanSpace ℝ ι) → ℝ} {κ h R : ℝ}
    (hF : ContDiff ℝ 2 F) (hκ : 0 < κ) (hh0 : 0 < h) (hR : 2 * h ^ 2 < R)
    (hlo : ∀ z v, κ⁻¹ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v)
    (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ ‖v‖ ^ 2)
    (v : ℝ)
    (hv : v ∈ Icc (3 * (2 * h ^ 2) / 4) (2 * h ^ 2)) :
    (originalHeatMixingFamily hF hκ hh0 hR hlo hup).source.lower v = ((κ + 2 * h ^ 2)⁻¹) :=
  originalVarianceHeatFamily_lower_eq hF hκ (originalMixingVariance_pos hh0) hR hlo hup v hv

theorem originalHeatPhaseDensity_energy_contraction_of_kernel {ι : Type*} [Fintype ι] {F : (EuclideanSpace ℝ ι) → ℝ} {κ h R : ℝ}
    (hF : ContDiff ℝ 2 F) (hκ : 0 < κ) (hh0 : 0 < h) (hR : 2 * h ^ 2 < R)
    (hlo : ∀ z v, κ⁻¹ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v)
    (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ ‖v‖ ^ 2)
    {θ C : ℝ}
    (hm1 : ((κ + 2 * h ^ 2)⁻¹) ≤ 1) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ (Real.sqrt 2/32)/32) (hC : 0 ≤ C)
    (hh : h ≤ 1/4) (hhC : h ≤ (Real.sqrt 2/32)/(8*(C/2+200)))
    (K : Kernel (Icc (0:ℝ) (1/2) × GaussianPhase (EuclideanSpace ℝ ι)) (EuclideanSpace ℝ ι)) [IsMarkovKernel K]
    (hK : ∀ t, ConditionallyInvariant (stdGaussian (EuclideanSpace ℝ ι)) (clockSection K t))
    :
    letI : IsProbabilityMeasure (volume.tilted (fun x => -F x)) :=
      originalGibbs_probability_of_hessian_lower hF hκ hlo
    ∀ (_hW : ∀ t, physicalDormantW12 (clockTransportFamily (originalHeatMixingFamily hF hκ hh0 hR hlo hup) (originalMixingVariance_pos hh0) hR)
      t (clockSection K t) (hK t) C (2*h^2))
    (f : centered (((clockTransportFamily (originalHeatMixingFamily hF hκ hh0 hR hlo hup) (originalMixingVariance_pos hh0) hR).law 0).prod (stdGaussian (EuclideanSpace ℝ ι)))) ,
    quadraticEnergy (sourceCorrector (originalHeatMixingFamily hF hκ hh0 hR hlo hup) (originalMixingVariance_pos hh0) hR) (θ*Real.sqrt ((κ + 2 * h ^ 2)⁻¹))
      (sourcePhaseDensity (originalHeatMixingFamily hF hκ hh0 hR hlo hup) (originalMixingVariance_pos hh0) hR (Real.sqrt 2*h) (Real.sqrt ((κ + 2 * h ^ 2)⁻¹)*h)
        (mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hh0)) (clockSection K) hK
        (fun f => sourceClockChannel_integrable (originalHeatMixingFamily hF hκ hh0 hR hlo hup) (originalMixingVariance_pos hh0) hR (Real.sqrt 2 * h) (Real.sqrt ((κ + 2 * h ^ 2)⁻¹) * h)
          (mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hh0)) K hK f) f) ≤
      sourceContractionFactor θ ((κ + 2 * h ^ 2)⁻¹) h *
        quadraticEnergy (sourceCorrector (originalHeatMixingFamily hF hκ hh0 hR hlo hup) (originalMixingVariance_pos hh0) hR) (θ*Real.sqrt ((κ + 2 * h ^ 2)⁻¹)) f := by
  let _ : IsProbabilityMeasure (volume.tilted (fun x => -F x)) :=
      originalGibbs_probability_of_hessian_lower hF hκ hlo
  exact fun hW f => sourcePhaseDensity_energy_contraction_of_kernel hh0 (originalHeatMixingFamily hF hκ hh0 hR hlo hup) hR
      (originalVarianceHeatFamily_step_lower_eq hF hκ hh0 hR hlo hup)
      (original_step_curvature_pos (h := h) hκ) hm1 hθ0 hθ hC hh hhC K hK hW f

theorem originalHeatPhase_mixing_of_kernel {ι : Type*} [Fintype ι] {F : (EuclideanSpace ℝ ι) → ℝ} {κ h R : ℝ}
    (hF : ContDiff ℝ 2 F) (hκ : 0 < κ) (hh0 : 0 < h) (hR : 2 * h ^ 2 < R)
    (hlo : ∀ z v, κ⁻¹ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v)
    (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ ‖v‖ ^ 2)
    {θ C : ℝ}
    (hm1 : ((κ + 2 * h ^ 2)⁻¹) ≤ 1) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ (Real.sqrt 2/32)/32) (hC : 0 ≤ C)
    (hh : h ≤ 1/4) (hhC : h ≤ (Real.sqrt 2/32)/(8*(C/2+200)))
    (K : Kernel (Icc (0:ℝ) (1/2) × GaussianPhase (EuclideanSpace ℝ ι)) (EuclideanSpace ℝ ι)) [IsMarkovKernel K]
    (hK : ∀ t, ConditionallyInvariant (stdGaussian (EuclideanSpace ℝ ι)) (clockSection K t))
    :
    letI : IsProbabilityMeasure (volume.tilted (fun x => -F x)) :=
      originalGibbs_probability_of_hessian_lower hF hκ hlo
    ∀ (_hW : ∀ t, physicalDormantW12 (clockTransportFamily (originalHeatMixingFamily hF hκ hh0 hR hlo hup) (originalMixingVariance_pos hh0) hR)
      t (clockSection K t) (hK t) C (2*h^2))
    (k : ℕ),
    ‖(sourceCenteredPhaseDensity (originalHeatMixingFamily hF hκ hh0 hR hlo hup) (originalMixingVariance_pos hh0) hR (Real.sqrt 2*h) (Real.sqrt ((κ + 2 * h ^ 2)⁻¹)*h)
      (mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hh0)) (clockSection K) hK
      (fun f => sourceClockChannel_integrable (originalHeatMixingFamily hF hκ hh0 hR hlo hup) (originalMixingVariance_pos hh0) hR (Real.sqrt 2 * h) (Real.sqrt ((κ + 2 * h ^ 2)⁻¹) * h)
          (mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hh0)) K hK f) : (centered (((clockTransportFamily (originalHeatMixingFamily hF hκ hh0 hR hlo hup) (originalMixingVariance_pos hh0) hR).law 0).prod (stdGaussian (EuclideanSpace ℝ ι))) →L[ℝ] centered (((clockTransportFamily (originalHeatMixingFamily hF hκ hh0 hR hlo hup) (originalMixingVariance_pos hh0) hR).law 0).prod (stdGaussian (EuclideanSpace ℝ ι))))) ^ k‖ ≤
        Real.sqrt ((5/3:ℝ)*(sourceContractionFactor θ ((κ + 2 * h ^ 2)⁻¹) h)^k) ∧
    ‖(sourceCenteredPhaseOperator (originalHeatMixingFamily hF hκ hh0 hR hlo hup) (originalMixingVariance_pos hh0) hR (Real.sqrt 2*h) (Real.sqrt ((κ + 2 * h ^ 2)⁻¹)*h)
      (mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hh0)) (clockSection K) hK
      (fun f => sourceClockChannel_integrable (originalHeatMixingFamily hF hκ hh0 hR hlo hup) (originalMixingVariance_pos hh0) hR (Real.sqrt 2 * h) (Real.sqrt ((κ + 2 * h ^ 2)⁻¹) * h)
          (mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hh0)) K hK f) : (centered (((clockTransportFamily (originalHeatMixingFamily hF hκ hh0 hR hlo hup) (originalMixingVariance_pos hh0) hR).law 0).prod (stdGaussian (EuclideanSpace ℝ ι))) →L[ℝ] centered (((clockTransportFamily (originalHeatMixingFamily hF hκ hh0 hR hlo hup) (originalMixingVariance_pos hh0) hR).law 0).prod (stdGaussian (EuclideanSpace ℝ ι))))) ^ k‖ ≤
        Real.sqrt ((5/3:ℝ)*(sourceContractionFactor θ ((κ + 2 * h ^ 2)⁻¹) h)^k) := by
  let _ : IsProbabilityMeasure (volume.tilted (fun x => -F x)) :=
      originalGibbs_probability_of_hessian_lower hF hκ hlo
  exact fun hW k => sourcePhase_mixing_of_kernel hh0 (originalHeatMixingFamily hF hκ hh0 hR hlo hup) hR
      (originalVarianceHeatFamily_step_lower_eq hF hκ hh0 hR hlo hup)
      (original_step_curvature_pos (h := h) hκ) hm1 hθ0 hθ hC hh hhC K hK hW k

end AcceleratedLogConcave.Kinetic
