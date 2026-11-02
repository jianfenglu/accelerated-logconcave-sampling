import AcceleratedLogConcave.Kinetic.ConditionalContraction.MomentumKernel

/-! Exact conditional Gaussian projections and their nested energy split. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.ConditionalContraction
open Reheating
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [IsProbabilityMeasure μ]

/-- Embed `(x,E)` functions, independent of P, into full phase space. -/
def momentumBaseEmbedding : Lp ℝ 2 (μ.prod (stdGaussian E)) →ₗᵢ[ℝ] Lp ℝ 2 (gaussianPhaseMeasure μ) :=
  (phaseSwapPullback μ).comp (Kinetic.hiddenEmbedding μ)

omit [BorelSpace E] in
theorem momentumAverage_pairing (g : Lp ℝ 2 (μ.prod (stdGaussian E)))
    (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    inner ℝ g (momentumAverage μ f) = inner ℝ (momentumBaseEmbedding μ g) f := by
  change inner ℝ g ((Kinetic.hiddenEmbedding μ).toContinuousLinearMap.adjoint (phaseSwapPullback μ f)) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (Kinetic.hiddenEmbedding μ g) ((phaseSwapPullback μ).toContinuousLinearMap f) = _
  rw [← ContinuousLinearMap.adjoint_inner_left, phaseSwapPullback_adjoint]
  rfl

omit [BorelSpace E] in
theorem momentumBaseEmbedding_adjoint : (momentumBaseEmbedding μ).toContinuousLinearMap.adjoint =
    momentumAverage μ := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℝ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_right, momentumAverage_pairing]
  rfl

omit [BorelSpace E] in
theorem momentumBaseEmbedding_position (g : Lp ℝ 2 μ) :
    momentumBaseEmbedding μ (productEmbedding μ (stdGaussian E) g) = positionEmbedding μ g :=
  phaseSwapPullback_position μ g

omit [BorelSpace E] in
theorem gaussianAverage_eq_momentumAverage (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    gaussianAverage μ f = productAverage μ (stdGaussian E) (momentumAverage μ f) := by
  apply ext_inner_left ℝ
  intro g
  change inner ℝ g ((positionEmbedding μ).toContinuousLinearMap.adjoint f) =
    inner ℝ g ((productEmbedding μ (stdGaussian E)).toContinuousLinearMap.adjoint (momentumAverage μ f))
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right]
  rw [momentumAverage_pairing]
  simp only [LinearIsometry.coe_toContinuousLinearMap, momentumBaseEmbedding_position]

omit [BorelSpace E] in
/-- Averaging P in a visible function leaves precisely its position average. -/
theorem momentumAverage_hiddenEmbedding (g : Lp ℝ 2 (μ.prod (stdGaussian E))) :
    momentumAverage μ (Kinetic.hiddenEmbedding μ g) =
      productEmbedding μ (stdGaussian E) (productAverage μ (stdGaussian E) g) := by
  apply Lp.ext
  have hU : phaseSwapPullback μ (Kinetic.hiddenEmbedding μ g) =ᵐ[gaussianPhaseMeasure μ]
      fun z => g (z.1.1,z.2) :=
    (Lp.coeFn_compMeasurePreserving (Kinetic.hiddenEmbedding μ g) (phaseSwap_measurePreserving μ)).trans
      ((phaseSwap_measurePreserving μ).quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving g measurePreserving_fst))
  have havg := (measurePreserving_fst (ν := stdGaussian E)).quasiMeasurePreserving.ae
    (productAverage_coe μ (stdGaussian E) g)
  filter_upwards [productAverage_coe (μ.prod (stdGaussian E)) (stdGaussian E)
      (phaseSwapPullback μ (Kinetic.hiddenEmbedding μ g)), Measure.ae_ae_of_ae_prod hU,
    Lp.coeFn_compMeasurePreserving (productAverage μ (stdGaussian E) g) measurePreserving_fst,
    havg] with z hz hgz hp hpos
  change momentumAverage μ (Kinetic.hiddenEmbedding μ g) z = _
  change momentumAverage μ (Kinetic.hiddenEmbedding μ g) z = _ at hz
  change productEmbedding μ (stdGaussian E) (productAverage μ (stdGaussian E) g) z =
    productAverage μ (stdGaussian E) g z.1 at hp
  rw [hz, hp, hpos]
  exact integral_congr_ae hgz

/-- The momentum conditional average is fixed by the actual momentum refresh. -/
theorem momentumAverage_momentumCollision (t : ℝ) (ht : 0 ≤ t)
    (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    momentumAverage μ (momentumCollision μ t ht f) = momentumAverage μ f := by
  change productAverage (μ.prod (stdGaussian E)) (stdGaussian E)
    (phaseSwapPullback μ (phaseSwapPullback μ
      (ouProduct (μ.prod (stdGaussian E)) t ht (phaseSwapPullback μ f)))) = _
  rw [phaseSwapPullback_involutive, productAverage_ouProduct]
  rfl

omit [BorelSpace E] in
theorem momentumAverage_norm_bound (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    ‖momentumAverage μ f‖ ≤ ‖f‖ := by
  have h := (productAverage (μ.prod (stdGaussian E)) (stdGaussian E)).le_opNorm (phaseSwapPullback μ f)
  have hn := mul_le_mul_of_nonneg_right (productAverage_norm_le (μ.prod (stdGaussian E)) (stdGaussian E))
    (norm_nonneg (phaseSwapPullback μ f))
  exact (h.trans hn).trans_eq (by rw [one_mul, (phaseSwapPullback μ).norm_map])

omit [BorelSpace E] in
/-- Exact nested Gaussian projection decomposition of the full microscopic energy. -/
theorem momentum_micro_decomposition (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    ‖f - gaussianPositionProjection μ f‖^2 =
      ‖f - momentumBaseEmbedding μ (momentumAverage μ f)‖^2 +
      ‖momentumAverage μ f - productEmbedding μ (stdGaussian E) (gaussianAverage μ f)‖^2 := by
  have h1 := isometry_adjoint_loss (momentumBaseEmbedding μ) f
  rw [momentumBaseEmbedding_adjoint] at h1
  have h2 := isometry_adjoint_loss (productEmbedding μ (stdGaussian E)) (momentumAverage μ f)
  change ‖momentumAverage μ f‖^2 - ‖productAverage μ (stdGaussian E) (momentumAverage μ f)‖^2 =
    ‖momentumAverage μ f - productEmbedding μ (stdGaussian E)
      (productAverage μ (stdGaussian E) (momentumAverage μ f))‖^2 at h2
  rw [← gaussianAverage_eq_momentumAverage] at h2
  have h3 := gaussianPositionProjection_norm_sq μ f
  change ‖positionEmbedding μ (gaussianAverage μ f)‖^2 + ‖f - gaussianPositionProjection μ f‖^2 = _ at h3
  rw [(positionEmbedding μ).norm_map] at h3
  linarith

omit [BorelSpace E] [IsProbabilityMeasure μ] in
theorem gaussianAverage_eq_hiddenAverage (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    gaussianAverage μ f = productAverage μ (stdGaussian E)
      (productAverage (μ.prod (stdGaussian E)) (stdGaussian E) f) := by
  apply ext_inner_left ℝ
  intro g
  change inner ℝ g ((positionEmbedding μ).toContinuousLinearMap.adjoint f) =
    inner ℝ g ((productEmbedding μ (stdGaussian E)).toContinuousLinearMap.adjoint
      ((Kinetic.hiddenEmbedding μ).toContinuousLinearMap.adjoint f))
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_right]
  rfl

end AcceleratedLogConcave.Kinetic.ConditionalContraction
