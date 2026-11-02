import AcceleratedLogConcave.Kinetic.Corrector
import AcceleratedLogConcave.Kinetic.Reheating.OUProduct
import AcceleratedLogConcave.Kinetic.Reheating.HeatPhaseGradient

/-! The actual momentum Ornstein--Uhlenbeck collision, with the auxiliary
Gaussian coordinate retained. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.ConditionalContraction
open Reheating
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [IsProbabilityMeasure μ]

def phaseSwapPullback : Lp ℝ 2 (gaussianPhaseMeasure μ) →ₗᵢ[ℝ] Lp ℝ 2 (gaussianPhaseMeasure μ) :=
  Lp.compMeasurePreservingₗᵢ ℝ phaseSwap (phaseSwap_measurePreserving μ)

omit [BorelSpace E] in
theorem phaseSwapPullback_involutive (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    phaseSwapPullback μ (phaseSwapPullback μ f) = f := by
  apply Lp.ext
  have h := (Lp.coeFn_compMeasurePreserving (phaseSwapPullback μ f) (phaseSwap_measurePreserving μ)).trans
    ((phaseSwap_measurePreserving μ).quasiMeasurePreserving.ae
      (Lp.coeFn_compMeasurePreserving f (phaseSwap_measurePreserving μ)))
  exact h

omit [BorelSpace E] in
theorem phaseSwapPullback_adjoint : (phaseSwapPullback μ).toContinuousLinearMap.adjoint =
    (phaseSwapPullback μ).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℝ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (phaseSwapPullback μ g) f = inner ℝ g (phaseSwapPullback μ f)
  calc
    _ = inner ℝ (phaseSwapPullback μ g) (phaseSwapPullback μ (phaseSwapPullback μ f)) := by
      rw [phaseSwapPullback_involutive]
    _ = _ := (phaseSwapPullback μ).inner_map_map _ _

omit [BorelSpace E] in
theorem phaseSwapPullback_position (f : Lp ℝ 2 μ) :
    phaseSwapPullback μ (positionEmbedding μ f) = positionEmbedding μ f := by
  apply Lp.ext
  exact ((Lp.coeFn_compMeasurePreserving (positionEmbedding μ f) (phaseSwap_measurePreserving μ)).trans
    ((phaseSwap_measurePreserving μ).quasiMeasurePreserving.ae (positionEmbedding_coe μ f))).trans
      (positionEmbedding_coe μ f).symm

/-- The actual Mehler kernel on P, retaining both x and E. -/
def momentumCollision (t : ℝ) (ht : 0 ≤ t) :
    Lp ℝ 2 (gaussianPhaseMeasure μ) →L[ℝ] Lp ℝ 2 (gaussianPhaseMeasure μ) :=
  (phaseSwapPullback μ).toContinuousLinearMap.comp
    ((ouProduct (μ.prod (stdGaussian E)) t ht).comp (phaseSwapPullback μ).toContinuousLinearMap)

theorem momentumCollision_apply (t : ℝ) (ht : 0 ≤ t) (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    momentumCollision μ t ht f = phaseSwapPullback μ
      (ouProduct (μ.prod (stdGaussian E)) t ht (phaseSwapPullback μ f)) := rfl

theorem momentumCollision_adjoint (t : ℝ) (ht : 0 ≤ t) :
    (momentumCollision μ t ht).adjoint = momentumCollision μ t ht := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℝ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_right]
  let U := phaseSwapPullback μ
  let O := ouProduct (E := E) (μ.prod (stdGaussian E)) t ht
  have hU (a b : Lp ℝ 2 (gaussianPhaseMeasure μ)) : inner ℝ (U a) b = inner ℝ a (U b) := by
    change inner ℝ ((phaseSwapPullback μ).toContinuousLinearMap a) b = _
    rw [← ContinuousLinearMap.adjoint_inner_right, phaseSwapPullback_adjoint]
    rfl
  change inner ℝ (U (O (U g))) f = inner ℝ g (U (O (U f)))
  calc
    _ = inner ℝ (O (U g)) (U f) := hU _ _
    _ = inner ℝ (U g) (O (U f)) :=
      (ouProduct_symmetric (μ.prod (stdGaussian E)) t ht (U g) (U f)).symm
    _ = _ := hU _ _

theorem momentumCollision_norm_le (t : ℝ) (ht : 0 ≤ t) : ‖momentumCollision μ t ht‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [momentumCollision_apply, (phaseSwapPullback μ).norm_map]
  have h := (ouProduct (μ.prod (stdGaussian E)) t ht).le_opNorm (phaseSwapPullback μ f)
  have hn := mul_le_mul_of_nonneg_right (ouProduct_norm_le (E := E) (μ.prod (stdGaussian E)) t ht)
    (norm_nonneg (phaseSwapPullback μ f))
  simpa only [one_mul, (phaseSwapPullback μ).norm_map] using h.trans hn

/-- First momentum chaos is an exact eigenfunction of the actual collision. -/
theorem momentumCollision_momentumEmbedding (t : ℝ) (ht : 0 ≤ t) (G : Lp E 2 μ) :
    momentumCollision μ t ht (gaussianMomentumEmbedding μ G) =
      Real.exp (-t) • gaussianMomentumEmbedding μ G := by
  have hcoe : phaseSwapPullback μ (gaussianMomentumEmbedding μ G) =ᵐ[gaussianPhaseMeasure μ]
      fun z => inner ℝ (G z.1.1) z.2 :=
    (Lp.coeFn_compMeasurePreserving (gaussianMomentumEmbedding μ G) (phaseSwap_measurePreserving μ)).trans
      ((phaseSwap_measurePreserving μ).quasiMeasurePreserving.ae (gaussianMomentumEmbedding_coe μ G))
  have h := ouProduct_firstChaos (μ.prod (stdGaussian E)) t ht
    (phaseSwapPullback μ (gaussianMomentumEmbedding μ G)) (fun z : E×E => G z.1) hcoe
  rw [momentumCollision_apply, h, map_smul, phaseSwapPullback_involutive]

/-- Every position observable is fixed by the actual momentum collision. -/
theorem momentumCollision_positionEmbedding (t : ℝ) (ht : 0 ≤ t) (g : Lp ℝ 2 μ) :
    momentumCollision μ t ht (positionEmbedding μ g) = positionEmbedding μ g := by
  have hrepr : positionEmbedding μ g = productEmbedding (μ.prod (stdGaussian E)) (stdGaussian E)
      (productEmbedding μ (stdGaussian E) g) := rfl
  rw [momentumCollision_apply, phaseSwapPullback_position, hrepr, ouProduct_embedding, ← hrepr,
    phaseSwapPullback_position]

/-- The exact conditional P-average, retaining `(x,E)`. -/
def momentumAverage : Lp ℝ 2 (gaussianPhaseMeasure μ) →L[ℝ] Lp ℝ 2 (μ.prod (stdGaussian E)) :=
  (productAverage (μ.prod (stdGaussian E)) (stdGaussian E)).comp (phaseSwapPullback μ).toContinuousLinearMap

/-- The collision norm loss controls the entire conditionally centered P part. -/
theorem momentumCollision_loss (t : ℝ) (ht : 0 ≤ t) (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    (1 - Real.exp (-2*t)) *
      ‖f - phaseSwapPullback μ (productEmbedding (μ.prod (stdGaussian E)) (stdGaussian E)
        (momentumAverage μ f))‖^2 ≤ ‖f‖^2 - ‖momentumCollision μ t ht f‖^2 := by
  have h := ouProduct_loss (μ.prod (stdGaussian E)) t ht (phaseSwapPullback μ f)
  rw [momentumCollision_apply, (phaseSwapPullback μ).norm_map]
  rw [← (phaseSwapPullback μ).norm_map (f - _), map_sub, phaseSwapPullback_involutive]
  have hdef : momentumAverage μ f = productAverage (μ.prod (stdGaussian E)) (stdGaussian E)
      (phaseSwapPullback μ f) := rfl
  rw [hdef]
  simpa only [(phaseSwapPullback μ).norm_map] using h

/-- Exact first-moment action on arbitrary joint input densities. -/
theorem gaussianMomentumAdjoint_momentumCollision (t : ℝ) (ht : 0 ≤ t)
    (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    gaussianMomentumAdjoint μ (momentumCollision μ t ht f) =
      Real.exp (-t) • gaussianMomentumAdjoint μ f := by
  apply ext_inner_left ℝ
  intro G
  change inner ℝ G ((gaussianMomentumEmbedding μ).toContinuousLinearMap.adjoint
    (momentumCollision μ t ht f)) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ ((gaussianMomentumEmbedding μ).toContinuousLinearMap G) (momentumCollision μ t ht f) = _
  rw [← ContinuousLinearMap.adjoint_inner_left, momentumCollision_adjoint]
  simp only [LinearIsometry.coe_toContinuousLinearMap]
  rw [momentumCollision_momentumEmbedding, real_inner_smul_left, real_inner_smul_right]
  change Real.exp (-t) * inner ℝ ((gaussianMomentumEmbedding μ).toContinuousLinearMap G) f = _
  rw [← ContinuousLinearMap.adjoint_inner_right]
  rfl

/-- Momentum collision preserves the actual position average. -/
theorem gaussianAverage_momentumCollision (t : ℝ) (ht : 0 ≤ t)
    (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    gaussianAverage μ (momentumCollision μ t ht f) = gaussianAverage μ f := by
  apply ext_inner_left ℝ
  intro g
  change inner ℝ g ((positionEmbedding μ).toContinuousLinearMap.adjoint (momentumCollision μ t ht f)) =
    inner ℝ g ((positionEmbedding μ).toContinuousLinearMap.adjoint f)
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right]
  rw [← ContinuousLinearMap.adjoint_inner_left, momentumCollision_adjoint]
  exact congrArg (fun q => inner ℝ q f) (momentumCollision_positionEmbedding μ t ht g)

open Analysis.Poisson
variable (V : E → ℝ) (hV : ContDiff ℝ 2 V)
  (hI : Integrable (fun x => Real.exp (-V x)))
  (hμ : μ = volume.tilted (fun x => -V x)) (m L : ℝ) (hm : 0 < m)
  (hlower : ∀ x a, m * ‖a‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x a a)
  (hupper : ∀ x a, fderiv ℝ (fderiv ℝ V) x a a ≤ L * ‖a‖ ^ 2)

/-- Exact source corrector-current decay under the actual momentum OU kernel. -/
theorem momentumCollision_corrector_inner (t : ℝ) (ht : 0 ≤ t)
    (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    inner ℝ (gaussianCorrector μ V hV hI hμ m L hm hlower hupper (momentumCollision μ t ht f))
      (momentumCollision μ t ht f) =
      Real.exp (-t) * inner ℝ (gaussianCorrector μ V hV hI hμ m L hm hlower hupper f) f := by
  have hA : gaussianCorrector μ V hV hI hμ m L hm hlower hupper (momentumCollision μ t ht f) =
      Real.exp (-t) • gaussianCorrector μ V hV hI hμ m L hm hlower hupper f := by
    simp only [gaussianCorrector_apply, gaussianMomentumAdjoint_momentumCollision, map_smul]
  rw [hA, real_inner_smul_left, ← ContinuousLinearMap.adjoint_inner_left, momentumCollision_adjoint]
  rw [gaussianCorrector_apply, momentumCollision_positionEmbedding]

/-- The precise corrector energy cost of momentum refresh. No estimate on a
hypothetical collision operator is assumed. -/
theorem momentumCollision_correctedEnergy_le (t : ℝ) (ht : 0 ≤ t) (θ : ℝ) (hθ : 0 ≤ θ)
    (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    gaussianCorrectedEnergy μ V hV hI hμ m L hm hlower hupper (θ * Real.sqrt m)
      (momentumCollision μ t ht f) ≤
      gaussianCorrectedEnergy μ V hV hI hμ m L hm hlower hupper (θ * Real.sqrt m) f -
      (1/2 : ℝ) * (‖f‖^2 - ‖momentumCollision μ t ht f‖^2) +
      (t/32) * ‖f - gaussianPositionProjection μ f‖^2 +
      8 * θ^2 * t * ‖gaussianPositionProjection μ f‖^2 := by
  let A := gaussianCorrector μ V hV hI hμ m L hm hlower hupper
  let M := ‖gaussianPositionProjection μ f‖
  let R := ‖f - gaussianPositionProjection μ f‖
  let J := inner ℝ (A f) f
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hexp : 0 ≤ 1 - Real.exp (-t) := sub_nonneg.mpr ((Real.exp_le_one_iff).mpr (neg_nonpos.mpr ht))
  have he : 1 - Real.exp (-t) ≤ t := by linarith [Real.add_one_le_exp (-t)]
  have hJ := gaussianCorrector_inner_bound μ V hV hI hμ m L hm hlower hupper f
  change |J| ≤ (Real.sqrt m)⁻¹ * M * R at hJ
  have hscaled : (θ * Real.sqrt m) * |J| ≤ θ * M * R := by
    calc
      _ ≤ (θ * Real.sqrt m) * ((Real.sqrt m)⁻¹ * M * R) :=
        mul_le_mul_of_nonneg_left hJ (mul_nonneg hθ hs.le)
      _ = _ := by field_simp
  have hcost : (θ * Real.sqrt m) * ((Real.exp (-t) - 1) * J) ≤ θ * t * M * R := by
    have h1 := mul_le_mul_of_nonneg_left (neg_le_abs J) (mul_nonneg (mul_nonneg hθ hs.le) hexp)
    have h2 := mul_le_mul_of_nonneg_left hscaled hexp
    have h3 := mul_le_mul_of_nonneg_right he (mul_nonneg (mul_nonneg hθ (norm_nonneg (gaussianPositionProjection μ f)))
      (norm_nonneg (f - gaussianPositionProjection μ f)))
    change (1 - Real.exp (-t)) * (θ * M * R) ≤ t * (θ * M * R) at h3
    nlinarith
  have hy : θ * t * M * R ≤ (t/32) * R^2 + 8 * θ^2 * t * M^2 := by
    have h := mul_nonneg ht (sq_nonneg (4 * θ * M - R / 4))
    nlinarith
  unfold gaussianCorrectedEnergy
  rw [momentumCollision_corrector_inner]
  change (1/2 : ℝ) * ‖momentumCollision μ t ht f‖^2 + (θ * Real.sqrt m) * (Real.exp (-t) * J) ≤ _
  change _ ≤ (1/2 : ℝ) * ‖f‖^2 + (θ * Real.sqrt m) * J -
    (1/2 : ℝ) * (‖f‖^2 - ‖momentumCollision μ t ht f‖^2) + (t/32) * R^2 + 8 * θ^2 * t * M^2
  nlinarith

end AcceleratedLogConcave.Kinetic.ConditionalContraction
