import AcceleratedLogConcave.Kinetic.ConditionalContraction.MomentumReheatingCommute
import AcceleratedLogConcave.Kinetic.ConditionalContraction.MomentumAveraging

/-! The combined actual momentum-refresh and correlated-reheating loss controls
all nonposition directions, without a product assumption on the density. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.ConditionalContraction
open Reheating
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [IsProbabilityMeasure μ]

private theorem ou_decay_lower (r : ℝ) (hr : 0 ≤ r) (hr' : r ≤ 1/2) :
    r ≤ 1 - Real.exp (-2*r) := by
  have he := Real.add_one_le_exp (2*r)
  have hexp : Real.exp (-2*r) * Real.exp (2*r) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos (-2*r)).le
  rw [hexp] at hm
  by_contra h
  have hp : 0 < Real.exp (-2*r) + r - 1 := by linarith
  have hpos := mul_pos (show 0 < 1 + 2*r by linarith) hp
  nlinarith

/-- The part of the P-average still depending on E is controlled by the actual
hidden residual after momentum refresh. -/
theorem momentumAverage_hidden_residual_le (r : ℝ) (hr : 0 ≤ r)
    (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    ‖momentumAverage μ f - productEmbedding μ (stdGaussian E) (gaussianAverage μ f)‖ ≤
      ‖momentumCollision μ r hr f - Reheating.hiddenEmbedding μ
        (hiddenAverage μ (momentumCollision μ r hr f))‖ := by
  have h := momentumAverage_norm_bound μ (momentumCollision μ r hr f -
    Reheating.hiddenEmbedding μ (hiddenAverage μ (momentumCollision μ r hr f)))
  rw [map_sub, momentumAverage_momentumCollision] at h
  change ‖momentumAverage μ f - momentumAverage μ (Kinetic.hiddenEmbedding μ
    (productAverage (μ.prod (stdGaussian E)) (stdGaussian E) (momentumCollision μ r hr f)))‖ ≤ _ at h
  rw [momentumAverage_hiddenEmbedding, ← gaussianAverage_eq_hiddenAverage,
    gaussianAverage_momentumCollision] at h
  exact h

/-- The manuscript's combined microscopic loss for the actual physical order:
correlated reheating followed by visible momentum OU. -/
theorem momentum_reheating_micro_loss (r : ℝ) (hr : 0 ≤ r) (hr' : r ≤ 1/2)
    (t : ℝ) (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    (r/16) * ‖f - gaussianPositionProjection μ f‖^2 ≤
      ‖f‖^2 - ‖ouProduct (heatedLaw μ t) r hr (reheatingDensity μ t f)‖^2 := by
  let O := momentumCollision μ r hr
  let X := ‖f - momentumBaseEmbedding μ (momentumAverage μ f)‖^2
  let Y := ‖momentumAverage μ f - productEmbedding μ (stdGaussian E) (gaussianAverage μ f)‖^2
  let Z := ‖O f - Reheating.hiddenEmbedding μ (hiddenAverage μ (O f))‖^2
  have hP := momentumCollision_loss μ r hr f
  change (1 - Real.exp (-2*r)) * X ≤ ‖f‖^2 - ‖O f‖^2 at hP
  have hE := reheating_hidden_loss μ t (O f)
  change (1/4 : ℝ) * Z ≤ ‖O f‖^2 - ‖reheatingDensity μ t (O f)‖^2 at hE
  have hYZ : Y ≤ Z := by
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (momentumAverage_hidden_residual_le μ r hr f)
  have hfirst : (r/16) * X ≤ ‖f‖^2 - ‖O f‖^2 := by
    apply le_trans _ hP
    exact mul_le_mul_of_nonneg_right (by linarith [ou_decay_lower r hr hr']) (sq_nonneg _)
  have hsecond : (r/16) * Y ≤ ‖O f‖^2 - ‖reheatingDensity μ t (O f)‖^2 := by
    apply le_trans _ hE
    calc
      _ ≤ (r/16) * Z := mul_le_mul_of_nonneg_left hYZ (by positivity)
      _ ≤ (1/4 : ℝ) * Z := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  rw [← reheatingDensity_momentumCollision]
  have hsplit := momentum_micro_decomposition μ f
  change ‖f - gaussianPositionProjection μ f‖^2 = X + Y at hsplit
  rw [hsplit, mul_add]
  linarith

end AcceleratedLogConcave.Kinetic.ConditionalContraction
