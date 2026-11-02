import AcceleratedLogConcave.Kinetic.ConditionalContraction.TransportCurrent

/-! The actual phase mean agrees with the mean of the position average. -/
noncomputable section
open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.ConditionalContraction
open Analysis.Poisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [IsProbabilityMeasure μ]

omit [BorelSpace E] in
theorem positionEmbedding_oneL2 : positionEmbedding μ (oneL2 μ) = oneL2 (gaussianPhaseMeasure μ) := by
  apply Lp.ext
  have hpos : MeasurePreserving (fun z : GaussianPhase E => z.1.1) (gaussianPhaseMeasure μ) μ :=
    measurePreserving_fst.comp measurePreserving_fst
  filter_upwards [positionEmbedding_coe μ (oneL2 μ),
    hpos.quasiMeasurePreserving.ae ((memLp_const (1 : ℝ) (μ := μ) (p := 2)).coeFn_toLp),
    (memLp_const (1 : ℝ) (μ := gaussianPhaseMeasure μ) (p := 2)).coeFn_toLp] with z hz hx h1
  exact hz.trans (hx.trans h1.symm)

omit [BorelSpace E] in
theorem mean_gaussianAverage (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    mean μ (gaussianAverage μ f) = mean (gaussianPhaseMeasure μ) f := by
  change inner ℝ (oneL2 μ) ((positionEmbedding μ).toContinuousLinearMap.adjoint f) =
    inner ℝ (oneL2 (gaussianPhaseMeasure μ)) f
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (positionEmbedding μ (oneL2 μ)) f = _
  rw [positionEmbedding_oneL2]

end AcceleratedLogConcave.Kinetic.ConditionalContraction
