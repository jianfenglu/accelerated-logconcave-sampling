import AcceleratedLogConcave.Kinetic.ConditionalContraction.MomentumCollision

/-! The actual momentum collision formula and its visible-coordinate restriction. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.ConditionalContraction
open Reheating
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [IsProbabilityMeasure μ]

/-- The full joint-density Mehler formula refreshes P and retains both x and E. -/
theorem momentumCollision_coe (t : ℝ) (ht : 0 ≤ t) (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    momentumCollision μ t ht f =ᵐ[gaussianPhaseMeasure μ]
      fun z => ∫ y, f ((z.1.1, gaussianMix E t (z.1.2,y)), z.2) ∂stdGaussian E := by
  let U := phaseSwapPullback μ
  let O := ouProduct (E := E) (μ.prod (stdGaussian E)) t ht
  have hOU : (fun z => O (U f) (phaseSwap z)) =ᵐ[gaussianPhaseMeasure μ]
      fun z => ∫ y, U f ((z.1.1,z.2), gaussianMix E t (z.1.2,y)) ∂stdGaussian E :=
    (phaseSwap_measurePreserving μ).quasiMeasurePreserving.ae
      (ouProduct_coe (μ.prod (stdGaussian E)) t ht (U f))
  have hq : MeasurePreserving
      (fun z : GaussianPhase E × E => ((z.1.1.1,z.1.2), gaussianMix E t (z.1.1.2,z.2)))
      ((gaussianPhaseMeasure μ).prod (stdGaussian E)) (gaussianPhaseMeasure μ) :=
    (ouProductObservation_measurePreserving (μ.prod (stdGaussian E)) t ht).comp
      ((phaseSwap_measurePreserving μ).prod (MeasurePreserving.id (stdGaussian E)))
  have hf := Measure.ae_ae_of_ae_prod (hq.quasiMeasurePreserving.ae
    (Lp.coeFn_compMeasurePreserving f (phaseSwap_measurePreserving μ)))
  filter_upwards [Lp.coeFn_compMeasurePreserving (O (U f)) (phaseSwap_measurePreserving μ), hOU, hf]
    with z hz hO hzq
  change U (O (U f)) z = _
  change U (O (U f)) z = O (U f) (phaseSwap z) at hz
  rw [hz, hO]
  apply integral_congr_ae
  exact hzq

/-- The actual full-phase kernel restricts to the ordinary visible momentum OU. -/
theorem momentumCollision_hiddenEmbedding (t : ℝ) (ht : 0 ≤ t)
    (f : Lp ℝ 2 (μ.prod (stdGaussian E))) :
    momentumCollision μ t ht (Kinetic.hiddenEmbedding μ f) =
      Kinetic.hiddenEmbedding μ (ouProduct μ t ht f) := by
  apply Lp.ext
  have hq : MeasurePreserving
      (fun z : GaussianPhase E × E => ((z.1.1.1,gaussianMix E t (z.1.1.2,z.2)),z.1.2))
      ((gaussianPhaseMeasure μ).prod (stdGaussian E)) (gaussianPhaseMeasure μ) :=
    (phaseSwap_measurePreserving μ).comp
      ((ouProductObservation_measurePreserving (μ.prod (stdGaussian E)) t ht).comp
        ((phaseSwap_measurePreserving μ).prod (MeasurePreserving.id (stdGaussian E))))
  have ha := Measure.ae_ae_of_ae_prod (hq.quasiMeasurePreserving.ae
    (Lp.coeFn_compMeasurePreserving f measurePreserving_fst))
  have ho := (measurePreserving_fst (ν := stdGaussian E)).quasiMeasurePreserving.ae
    (ouProduct_coe μ t ht f)
  filter_upwards [momentumCollision_coe μ t ht (Kinetic.hiddenEmbedding μ f),
    Lp.coeFn_compMeasurePreserving (ouProduct μ t ht f) measurePreserving_fst, ha, ho]
    with z hz hout ha ho
  change Kinetic.hiddenEmbedding μ (ouProduct μ t ht f) z = ouProduct μ t ht f z.1 at hout
  rw [hz, hout, ho]
  apply integral_congr_ae
  exact ha

end AcceleratedLogConcave.Kinetic.ConditionalContraction
