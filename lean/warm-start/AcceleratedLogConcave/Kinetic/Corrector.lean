import AcceleratedLogConcave.Kinetic.GaussianEmbedding
import AcceleratedLogConcave.Analysis.Poisson.GradientInverse

/-!
# The concrete Gaussian kinetic corrector

The corrector is `I S J*`, where `I` and `J` are the actual Gaussian position
and momentum embeddings and `S` is the genuine vector Poisson inverse. Its
bounds therefore follow from the proved weighted variational problems.
-/

noncomputable section
open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace

namespace AcceleratedLogConcave.Kinetic
open Analysis.Poisson Analysis.WeightedGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [IsProbabilityMeasure μ] (V : E → ℝ)
  (hV : ContDiff ℝ 2 V) (hI : Integrable (fun x => Real.exp (-V x)))
  (hμ : μ = volume.tilted (fun x => -V x))
  (m L : ℝ) (hm : 0 < m)
  (hlower : ∀ x a, m * ‖a‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x a a)
  (hupper : ∀ x a, fderiv ℝ (fderiv ℝ V) x a a ≤ L * ‖a‖ ^ 2)

/-- The actual kinetic corrector `I S J*`. -/
def gaussianCorrector : Lp ℝ 2 (gaussianPhaseMeasure μ) →L[ℝ]
    Lp ℝ 2 (gaussianPhaseMeasure μ) :=
  (positionEmbedding μ).toContinuousLinearMap.comp
    ((vectorPoissonInverse μ V hV hI hμ m L hm hlower hupper).comp
      (gaussianMomentumAdjoint μ))

@[simp] theorem gaussianCorrector_apply (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    gaussianCorrector μ V hV hI hμ m L hm hlower hupper f =
      positionEmbedding μ (vectorPoissonInverse μ V hV hI hμ m L hm hlower hupper
        (gaussianMomentumAdjoint μ f)) := rfl

/-- Its adjoint is the genuine Gaussian lift of the scalar gradient inverse. -/
theorem gaussianCorrector_adjoint :
    (gaussianCorrector μ V hV hI hμ m L hm hlower hupper).adjoint =
      (gaussianMomentumEmbedding μ).toContinuousLinearMap.comp
        ((gradientPoissonInverse μ V hV hI hμ m L hm hlower hupper).comp
          (gaussianAverage μ)) := by
  unfold gaussianCorrector gaussianMomentumAdjoint gaussianAverage
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, vectorPoissonInverse_adjoint]
  exact ContinuousLinearMap.comp_assoc _ _ _

theorem gaussianCorrector_bound (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    ‖gaussianCorrector μ V hV hI hμ m L hm hlower hupper f‖ ≤
      (Real.sqrt m)⁻¹ * ‖f‖ := by
  rw [gaussianCorrector_apply, (positionEmbedding μ).norm_map, vectorPoissonInverse_apply]
  apply (vectorPoissonSolution_norm_le (gaussianMomentumAdjoint μ f)).trans
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Real.sqrt_nonneg m))
  exact ((gaussianMomentumAdjoint μ).le_opNorm f).trans
    (by simpa only [one_mul] using (mul_le_mul_of_nonneg_right
      (gaussianMomentumAdjoint_norm_le μ) (norm_nonneg f)))

theorem gaussianCorrector_norm_le :
    ‖gaussianCorrector μ V hV hI hμ m L hm hlower hupper‖ ≤ (Real.sqrt m)⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (Real.sqrt_nonneg m))
    (gaussianCorrector_bound μ V hV hI hμ m L hm hlower hupper)

@[simp] theorem gaussianCorrector_positionProjection (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    gaussianCorrector μ V hV hI hμ m L hm hlower hupper (gaussianPositionProjection μ f) = 0 := by
  change positionEmbedding μ (vectorPoissonInverse μ V hV hI hμ m L hm hlower hupper
    (gaussianMomentumAdjoint μ (positionEmbedding μ (gaussianAverage μ f)))) = 0
  rw [gaussianMomentumAdjoint_positionEmbedding, map_zero, map_zero]

@[simp] theorem positionProjection_gaussianCorrector (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    gaussianPositionProjection μ (gaussianCorrector μ V hV hI hμ m L hm hlower hupper f) =
      gaussianCorrector μ V hV hI hμ m L hm hlower hupper f := by
  rw [gaussianCorrector_apply, gaussianPositionProjection_positionEmbedding]

theorem gaussianCorrector_comp_positionProjection :
    (gaussianCorrector μ V hV hI hμ m L hm hlower hupper).comp (gaussianPositionProjection μ) = 0 := by
  apply ContinuousLinearMap.ext
  exact gaussianCorrector_positionProjection μ V hV hI hμ m L hm hlower hupper

theorem positionProjection_comp_gaussianCorrector :
    (gaussianPositionProjection μ).comp (gaussianCorrector μ V hV hI hμ m L hm hlower hupper) =
      gaussianCorrector μ V hV hI hμ m L hm hlower hupper := by
  apply ContinuousLinearMap.ext
  exact positionProjection_gaussianCorrector μ V hV hI hμ m L hm hlower hupper

/-- The corrector pairs only the position and nonposition components. -/
theorem gaussianCorrector_inner_bound (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    |inner ℝ (gaussianCorrector μ V hV hI hμ m L hm hlower hupper f) f| ≤
      (Real.sqrt m)⁻¹ * ‖gaussianPositionProjection μ f‖ * ‖f - gaussianPositionProjection μ f‖ := by
  let A := gaussianCorrector μ V hV hI hμ m L hm hlower hupper
  let P := gaussianPositionProjection μ
  have hp : inner ℝ (A f) f = inner ℝ (A f) (P f) := by
    have he := P.adjoint_inner_left f (A f)
    rw [gaussianPositionProjection_adjoint, positionProjection_gaussianCorrector] at he
    exact he
  have hq : A (f - P f) = A f := by
    rw [map_sub, gaussianCorrector_positionProjection, sub_zero]
  have hb : ‖A f‖ ≤ (Real.sqrt m)⁻¹ * ‖f - P f‖ := by
    rw [← hq]
    exact gaussianCorrector_bound μ V hV hI hμ m L hm hlower hupper _
  change |inner ℝ (A f) f| ≤ _
  rw [hp]
  calc
    _ ≤ ‖A f‖ * ‖P f‖ := abs_real_inner_le_norm _ _
    _ ≤ ((Real.sqrt m)⁻¹ * ‖f - P f‖) * ‖P f‖ :=
      mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ = _ := by ring

omit V hV hI hμ m L hm hlower hupper [BorelSpace E] [IsProbabilityMeasure μ] in
/-- Orthogonal position/nonposition splitting for the actual Gaussian projection. -/
theorem gaussianPositionProjection_norm_sq (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    ‖gaussianPositionProjection μ f‖ ^ 2 + ‖f - gaussianPositionProjection μ f‖ ^ 2 = ‖f‖ ^ 2 := by
  let P := gaussianPositionProjection μ
  have he := P.adjoint_inner_left f (P f)
  rw [gaussianPositionProjection_adjoint, gaussianPositionProjection_idempotent,
    real_inner_self_eq_norm_sq] at he
  have hsym := real_inner_comm f (P f)
  rw [← real_inner_self_eq_norm_sq (f - P f)]
  simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq]
  rw [← hsym, he]
  ring

/-- The source corrected energy, with its positive corrector cross term. -/
def gaussianCorrectedEnergy (ε : ℝ) (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) : ℝ :=
  (1 / 2 : ℝ) * ‖f‖ ^ 2 + ε * inner ℝ (gaussianCorrector μ V hV hI hμ m L hm hlower hupper f) f

/-- Multiplying by `θ √m` cancels the inverse-gap factor in the corrector estimate. -/
theorem gaussianCorrector_scaled_inner_bound (θ : ℝ) (hθ : 0 ≤ θ)
    (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    |(θ * Real.sqrt m) * inner ℝ (gaussianCorrector μ V hV hI hμ m L hm hlower hupper f) f| ≤
      (θ / 2) * ‖f‖ ^ 2 := by
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hb := gaussianCorrector_inner_bound μ V hV hI hμ m L hm hlower hupper f
  have hp := gaussianPositionProjection_norm_sq μ f
  have hprod : ‖gaussianPositionProjection μ f‖ * ‖f - gaussianPositionProjection μ f‖ ≤
      (1 / 2 : ℝ) * ‖f‖ ^ 2 := by
    nlinarith [sq_nonneg (‖gaussianPositionProjection μ f‖ - ‖f - gaussianPositionProjection μ f‖)]
  calc
    _ = (θ * Real.sqrt m) * |inner ℝ (gaussianCorrector μ V hV hI hμ m L hm hlower hupper f) f| := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg hθ hs.le)]
    _ ≤ (θ * Real.sqrt m) * ((Real.sqrt m)⁻¹ * ‖gaussianPositionProjection μ f‖ *
        ‖f - gaussianPositionProjection μ f‖) := mul_le_mul_of_nonneg_left hb (mul_nonneg hθ hs.le)
    _ = θ * (‖gaussianPositionProjection μ f‖ * ‖f - gaussianPositionProjection μ f‖) := by
      field_simp
    _ ≤ θ * ((1 / 2 : ℝ) * ‖f‖ ^ 2) := mul_le_mul_of_nonneg_left hprod hθ
    _ = _ := by ring

/-- Exact source energy equivalence for `ε = θ √m`. -/
theorem gaussianCorrectedEnergy_bounds (θ : ℝ) (hθ : 0 ≤ θ)
    (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    ((1 - θ) / 2) * ‖f‖ ^ 2 ≤
      gaussianCorrectedEnergy μ V hV hI hμ m L hm hlower hupper (θ * Real.sqrt m) f ∧
    gaussianCorrectedEnergy μ V hV hI hμ m L hm hlower hupper (θ * Real.sqrt m) f ≤
      ((1 + θ) / 2) * ‖f‖ ^ 2 := by
  have hb := abs_le.mp (gaussianCorrector_scaled_inner_bound μ V hV hI hμ m L hm hlower hupper θ hθ f)
  unfold gaussianCorrectedEnergy
  constructor <;> nlinarith

/-- The customary `θ ≤ 1/4` choice gives uniform positive energy constants. -/
theorem gaussianCorrectedEnergy_bounds_quarter (θ : ℝ) (hθ : 0 ≤ θ) (hθq : θ ≤ 1 / 4)
    (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    (3 / 8 : ℝ) * ‖f‖ ^ 2 ≤
      gaussianCorrectedEnergy μ V hV hI hμ m L hm hlower hupper (θ * Real.sqrt m) f ∧
    gaussianCorrectedEnergy μ V hV hI hμ m L hm hlower hupper (θ * Real.sqrt m) f ≤
      (5 / 8 : ℝ) * ‖f‖ ^ 2 := by
  have hb := gaussianCorrectedEnergy_bounds μ V hV hI hμ m L hm hlower hupper θ hθ f
  have hn := sq_nonneg ‖f‖
  constructor <;> nlinarith

/-- The genuine closed spatial gradient of the corrector's position representative. -/
def gaussianCorrectorPositionGradient : Lp ℝ 2 (gaussianPhaseMeasure μ) →L[ℝ] Lp E 2 μ :=
  (weightedGradientProjection μ V hV hI hμ m L hm hlower hupper).comp (gaussianMomentumAdjoint μ)

/-- Graph membership ties the bounded gradient map to the actual closed gradient. -/
theorem gaussianCorrectorPositionGradient_graph (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    (vectorPoissonInverse μ V hV hI hμ m L hm hlower hupper (gaussianMomentumAdjoint μ f),
      gaussianCorrectorPositionGradient μ V hV hI hμ m L hm hlower hupper f) ∈
      (closedGradient μ V (hV.of_le (by norm_num)) hI hμ).graph :=
  LinearPMap.mem_graph _ (vectorPoissonSolution μ V hV hI hμ m L hm hlower hupper
    (gaussianMomentumAdjoint μ f))

/-- The spatial gradient of the corrector position representative is a contraction. -/
theorem gaussianCorrectorPositionGradient_norm_le :
    ‖gaussianCorrectorPositionGradient μ V hV hI hμ m L hm hlower hupper‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖weightedGradientProjection μ V hV hI hμ m L hm hlower hupper
    (gaussianMomentumAdjoint μ f)‖ ≤ 1 * ‖f‖
  have hp := (weightedGradientProjection μ V hV hI hμ m L hm hlower hupper).le_opNorm
    (gaussianMomentumAdjoint μ f)
  have hpn := weightedGradientProjection_norm_le μ V hV hI hμ m L hm hlower hupper
  have hj := (gaussianMomentumAdjoint μ).le_opNorm f
  have hjn := gaussianMomentumAdjoint_norm_le μ
  have h1 := mul_le_mul_of_nonneg_right hpn (norm_nonneg (gaussianMomentumAdjoint μ f))
  have h2 := mul_le_mul_of_nonneg_right hjn (norm_nonneg f)
  nlinarith


/-- The adjoint corrector's momentum coefficient has genuine closed spatial
Hessian rows, whose total squared norm is bounded by the phase input energy. -/
theorem gaussianCorrectorAdjoint_spatial_rows (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    ∃ R : Fin (Module.finrank ℝ E) → Lp E 2 μ,
      (∀ j, ((innerSL ℝ ((stdOrthonormalBasis ℝ E) j)).compLp
        (gradientPoissonInverse μ V hV hI hμ m L hm hlower hupper (gaussianAverage μ f)), R j) ∈
        (closedGradient μ V (hV.of_le (by norm_num)) hI hμ).graph) ∧
      (∑ j, ‖R j‖ ^ 2) ≤ ‖f‖ ^ 2 := by
  have hs := poissonSolution_spec (μ := μ) (V := V) (hV := hV) (hI := hI)
    (hμ := hμ) (m := m) (L := L) (hm := hm) (hlower := hlower) (hupper := hupper)
    (gaussianAverage μ f)
  obtain ⟨R, hR, he⟩ := weak_poisson_bochner μ V hV hI hμ m L hm hlower hupper
    (poissonSolution μ V hV hI hμ m L hm hlower hupper (gaussianAverage μ f))
    (centerForcing μ (gaussianAverage μ f)) hs.2
  refine ⟨R, hR, ?_⟩
  have hpos (G : Lp E 2 μ) : 0 ≤ inner ℝ (hessianMultiplier μ V hV m L hlower hupper G) G := by
    rw [inner_hessianMultiplier]
    exact integral_nonneg (fun x => (mul_nonneg hm.le (sq_nonneg _)).trans (hlower x (G x)))
  have hc := norm_centerForcing_le μ (gaussianAverage μ f)
  have ha := (gaussianAverage μ).le_opNorm f
  have han := mul_le_mul_of_nonneg_right (gaussianAverage_norm_le μ) (norm_nonneg f)
  have hn := norm_nonneg (centerForcing μ (gaussianAverage μ f))
  have hav := norm_nonneg (gaussianAverage μ f)
  have hpp := hpos (closedGradient μ V (hV.of_le (by norm_num)) hI hμ
    (poissonSolution μ V hV hI hμ m L hm hlower hupper (gaussianAverage μ f)))
  nlinarith

end AcceleratedLogConcave.Kinetic
