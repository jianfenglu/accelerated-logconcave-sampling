import AcceleratedLogConcave.Kinetic.ConditionalContraction.MomentumKernel
import AcceleratedLogConcave.Kinetic.Reheating.Loss

/-! Actual coordinate-kernel commutation for momentum refresh and reheating. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.ConditionalContraction
open Reheating
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [IsProbabilityMeasure μ]

/-- Actual momentum refresh with an independent Gaussian innovation. -/
def momentumRefresh (t : ℝ) (z : GaussianPhase E × E) : GaussianPhase E :=
  ((z.1.1.1, gaussianMix E t (z.1.1.2,z.2)), z.1.2)

theorem momentumRefresh_measurePreserving (t : ℝ) (ht : 0 ≤ t) :
    MeasurePreserving (momentumRefresh (E := E) t)
      ((gaussianPhaseMeasure μ).prod (stdGaussian E)) (gaussianPhaseMeasure μ) :=
  (phaseSwap_measurePreserving μ).comp
    ((ouProductObservation_measurePreserving (μ.prod (stdGaussian E)) t ht).comp
      ((phaseSwap_measurePreserving μ).prod (MeasurePreserving.id (stdGaussian E))))

/-- The actual heat observation retains the momentum OU channel. -/
theorem momentumCollision_heatPullback (r : ℝ) (hr : 0 ≤ r) (t : ℝ)
    (g : Lp ℝ 2 ((heatedLaw μ t).prod (stdGaussian E))) :
    momentumCollision μ r hr (heatPullback μ t g) =
      heatPullback μ t (ouProduct (heatedLaw μ t) r hr g) := by
  apply Lp.ext
  have ha := Measure.ae_ae_of_ae_prod ((momentumRefresh_measurePreserving μ r hr).quasiMeasurePreserving.ae
    (heatPullback_coe μ t g))
  have ho := (heatObservation_measurePreserving μ t).quasiMeasurePreserving.ae
    (ouProduct_coe (heatedLaw μ t) r hr g)
  filter_upwards [momentumCollision_coe μ r hr (heatPullback μ t g),
    heatPullback_coe μ t (ouProduct (heatedLaw μ t) r hr g), ha, ho] with z hz hout ha ho
  rw [hz, hout, ho]
  apply integral_congr_ae
  exact ha

/-- Adjoint form of the genuine heat-observation intertwining. -/
theorem heatDensity_momentumCollision (r : ℝ) (hr : 0 ≤ r) (t : ℝ)
    (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    heatDensity μ t (momentumCollision μ r hr f) = ouProduct (heatedLaw μ t) r hr (heatDensity μ t f) := by
  apply ext_inner_left ℝ
  intro g
  change inner ℝ g ((heatPullback μ t).toContinuousLinearMap.adjoint (momentumCollision μ r hr f)) = _
  rw [ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.adjoint_inner_left,
    momentumCollision_adjoint]
  change inner ℝ (momentumCollision μ r hr (heatPullback μ t g)) f = _
  rw [momentumCollision_heatPullback]
  change inner ℝ ((heatPullback μ t).toContinuousLinearMap (ouProduct (heatedLaw μ t) r hr g)) f = _
  rw [← ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (ouProduct (heatedLaw μ t) r hr g) (heatDensity μ t f) = _
  exact (ouProduct_symmetric (heatedLaw μ t) r hr g (heatDensity μ t f)).symm

/-- Independent momentum and auxiliary OU innovations commute on every joint
L2 density, by the actual product-noise integral and Fubini. -/
theorem momentumCollision_auxiliaryOU (r : ℝ) (hr : 0 ≤ r) (t : ℝ) (ht : 0 ≤ t)
    (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    momentumCollision μ r hr (ouProduct (μ.prod (stdGaussian E)) t ht f) =
      ouProduct (μ.prod (stdGaussian E)) t ht (momentumCollision μ r hr f) := by
  apply Lp.ext
  have hp := momentumRefresh_measurePreserving μ r hr
  have he := ouProductObservation_measurePreserving (E := E) (μ.prod (stdGaussian E)) t ht
  have hpc := Measure.ae_ae_of_ae_prod (hp.quasiMeasurePreserving.ae
    (ouProduct_coe (μ.prod (stdGaussian E)) t ht f))
  have hec := Measure.ae_ae_of_ae_prod (he.quasiMeasurePreserving.ae
    (momentumCollision_coe μ r hr f))
  have hb : MeasurePreserving
      (fun z : GaussianPhase E × (E×E) =>
        ((z.1.1.1,gaussianMix E r (z.1.1.2,z.2.1)),gaussianMix E t (z.1.2,z.2.2)))
      ((gaussianPhaseMeasure μ).prod ((stdGaussian E).prod (stdGaussian E))) (gaussianPhaseMeasure μ) :=
    (he.comp (hp.prod (MeasurePreserving.id (stdGaussian E)))).comp
      ((measurePreserving_prodAssoc (gaussianPhaseMeasure μ) (stdGaussian E) (stdGaussian E)).symm
        MeasurableEquiv.prodAssoc)
  have hi := (((Lp.memLp f).comp_measurePreserving hb).integrable (by norm_num)).prod_right_ae
  filter_upwards [momentumCollision_coe μ r hr (ouProduct (μ.prod (stdGaussian E)) t ht f),
    ouProduct_coe (μ.prod (stdGaussian E)) t ht (momentumCollision μ r hr f), hpc, hec, hi]
    with z hzP hzE hpz hez hiz
  rw [hzP, hzE]
  calc
    _ = ∫ p, ∫ e, f ((z.1.1,gaussianMix E r (z.1.2,p)),gaussianMix E t (z.2,e))
        ∂stdGaussian E ∂stdGaussian E := integral_congr_ae hpz
    _ = ∫ e, ∫ p, f ((z.1.1,gaussianMix E r (z.1.2,p)),gaussianMix E t (z.2,e))
        ∂stdGaussian E ∂stdGaussian E := integral_integral_swap hiz
    _ = _ := (integral_congr_ae hez).symm

/-- Exact order commutation for the physical correlated reheating channel. -/
theorem reheatingDensity_momentumCollision (r : ℝ) (hr : 0 ≤ r) (t : ℝ)
    (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    reheatingDensity μ t (momentumCollision μ r hr f) =
      ouProduct (heatedLaw μ t) r hr (reheatingDensity μ t f) := by
  change heatDensity μ t (ouProduct (μ.prod (stdGaussian E)) hiddenOuTime hiddenOuTime_nonneg
    (momentumCollision μ r hr f)) = _
  rw [← momentumCollision_auxiliaryOU, heatDensity_momentumCollision]
  rfl

end AcceleratedLogConcave.Kinetic.ConditionalContraction
