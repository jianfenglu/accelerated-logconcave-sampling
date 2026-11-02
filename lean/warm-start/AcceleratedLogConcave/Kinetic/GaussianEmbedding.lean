import AcceleratedLogConcave.Probability.WarmInitialization
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# Gaussian averaging and first momentum chaos

The phase coordinates are `((x,p),e)`, with independent standard Gaussian
momentum `p` and auxiliary coordinate `e`, matching warm initialization.
All embeddings below are constructed for this actual product measure.
-/

noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace

namespace AcceleratedLogConcave.Kinetic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Position, momentum, and independent auxiliary Gaussian coordinates. -/
abbrev GaussianPhase (E : Type*) := (E × E) × E

/-- The actual phase reference law, in the same coordinate order as W01. -/
def gaussianPhaseMeasure (μ : Measure E) : Measure (GaussianPhase E) :=
  (μ.prod (stdGaussian E)).prod (stdGaussian E)

instance gaussianPhaseMeasure_probability (μ : Measure E) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (gaussianPhaseMeasure μ) := by
  unfold gaussianPhaseMeasure
  infer_instance

private theorem gaussian_inner_sq (v : E) :
    ∫ p, (inner ℝ v p) ^ 2 ∂stdGaussian E = ‖v‖ ^ 2 := by
  have h := covarianceBilin_apply (IsGaussian.memLp_two_id (μ := stdGaussian E)) v v
  rw [covarianceBilin_stdGaussian] at h
  change inner ℝ v v = _ at h
  simpa only [integral_id_stdGaussian, id_eq, sub_zero, ← pow_two,
    real_inner_self_eq_norm_sq] using h.symm

private theorem gaussian_inner_mean (v : E) :
    ∫ p, inner ℝ v p ∂stdGaussian E = 0 :=
  integral_strongDual_stdGaussian (innerSL ℝ v)

variable (μ : Measure E) [IsProbabilityMeasure μ]

private theorem momentum_memLp (G : Lp E 2 μ) :
    MemLp (fun z : E × E => inner ℝ (G z.1) z.2) 2 (μ.prod (stdGaussian E)) := by
  have hm : AEStronglyMeasurable (fun z : E × E => inner ℝ (G z.1) z.2)
      (μ.prod (stdGaussian E)) :=
    ((Lp.memLp G).comp_fst (stdGaussian E)).aestronglyMeasurable.inner
      ((IsGaussian.memLp_two_id (μ := stdGaussian E)).comp_snd μ).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).mpr
  have hg := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable G)).mp (Lp.memLp G)
  have hp := (memLp_two_iff_integrable_sq_norm
    (IsGaussian.memLp_two_id (μ := stdGaussian E)).aestronglyMeasurable).mp
      (IsGaussian.memLp_two_id (μ := stdGaussian E))
  apply (hg.mul_prod hp).mono' (hm.pow 2)
  exact Filter.Eventually.of_forall fun z => by
    change ‖(inner ℝ (G z.1) z.2) ^ 2‖ ≤ ‖G z.1‖ ^ 2 * ‖z.2‖ ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← mul_pow]
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
        (abs_real_inner_le_norm (G z.1) z.2)

private def momentumAction (G : Lp E 2 μ) : Lp ℝ 2 (μ.prod (stdGaussian E)) :=
  (momentum_memLp μ G).toLp _

private theorem momentumAction_coe (G : Lp E 2 μ) :
    momentumAction μ G =ᵐ[μ.prod (stdGaussian E)] fun z => inner ℝ (G z.1) z.2 :=
  (momentum_memLp μ G).coeFn_toLp

private theorem momentumAction_norm (G : Lp E 2 μ) : ‖momentumAction μ G‖ = ‖G‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def]
  calc
    _ = ∫ z, (inner ℝ (G z.1) z.2) ^ 2 ∂(μ.prod (stdGaussian E)) := by
      apply integral_congr_ae
      filter_upwards [momentumAction_coe μ G] with z hz
      simp only [hz, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    _ = ∫ x, ∫ p, (inner ℝ (G x) p) ^ 2 ∂stdGaussian E ∂μ :=
      integral_prod _ (momentum_memLp μ G).integrable_sq
    _ = _ := by simp only [gaussian_inner_sq, real_inner_self_eq_norm_sq]

/-- The actual first momentum chaos on position-momentum L2. -/
def momentumEmbedding : Lp E 2 μ →ₗᵢ[ℝ] Lp ℝ 2 (μ.prod (stdGaussian E)) where
  toFun := momentumAction μ
  map_add' G F := by
    apply Lp.ext
    filter_upwards [momentumAction_coe μ (G + F), momentumAction_coe μ G,
      momentumAction_coe μ F, Lp.coeFn_add (momentumAction μ G) (momentumAction μ F),
      measurePreserving_fst.quasiMeasurePreserving.ae (Lp.coeFn_add G F)] with z hGF hG hF ha hb
    simp only [hGF, ha, Pi.add_apply, hG, hF, hb, inner_add_left]
  map_smul' c G := by
    apply Lp.ext
    filter_upwards [momentumAction_coe μ (c • G), momentumAction_coe μ G,
      Lp.coeFn_smul c (momentumAction μ G),
      measurePreserving_fst.quasiMeasurePreserving.ae (Lp.coeFn_smul c G)] with z hc hG ha hb
    simp only [RingHom.id_apply, hc, ha, Pi.smul_apply, hG, hb, real_inner_smul_left,
      smul_eq_mul]
  norm_map' := momentumAction_norm μ

theorem momentumEmbedding_coe (G : Lp E 2 μ) :
    momentumEmbedding μ G =ᵐ[μ.prod (stdGaussian E)] fun z => inner ℝ (G z.1) z.2 :=
  momentumAction_coe μ G

/-- Add the independent auxiliary Gaussian coordinate by composition. -/
def hiddenEmbedding : Lp ℝ 2 (μ.prod (stdGaussian E)) →ₗᵢ[ℝ]
    Lp ℝ 2 (gaussianPhaseMeasure μ) :=
  Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst

/-- Scalar position functions embedded into the actual three-coordinate phase law. -/
def positionEmbedding : Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 (gaussianPhaseMeasure μ) :=
  (hiddenEmbedding μ).comp (Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst)

/-- The first momentum chaos: J_P G(x,p,e) = inner(G(x),p). -/
def gaussianMomentumEmbedding : Lp E 2 μ →ₗᵢ[ℝ] Lp ℝ 2 (gaussianPhaseMeasure μ) :=
  (hiddenEmbedding μ).comp (momentumEmbedding μ)

omit [BorelSpace E] [IsProbabilityMeasure μ] in
theorem positionEmbedding_coe (f : Lp ℝ 2 μ) :
    positionEmbedding μ f =ᵐ[gaussianPhaseMeasure μ] fun z => f z.1.1 := by
  exact (Lp.coeFn_compMeasurePreserving _ measurePreserving_fst).trans
    (measurePreserving_fst.quasiMeasurePreserving.ae
      (Lp.coeFn_compMeasurePreserving f measurePreserving_fst))

theorem gaussianMomentumEmbedding_coe (G : Lp E 2 μ) :
    gaussianMomentumEmbedding μ G =ᵐ[gaussianPhaseMeasure μ]
      fun z => inner ℝ (G z.1.1) z.1.2 := by
  exact (Lp.coeFn_compMeasurePreserving _ measurePreserving_fst).trans
    (measurePreserving_fst.quasiMeasurePreserving.ae (momentumAction_coe μ G))

private theorem momentum_orthogonal_position (G : Lp E 2 μ) (f : Lp ℝ 2 μ) :
    inner ℝ (momentumEmbedding μ G)
      (Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst f) = 0 := by
  let If : Lp ℝ 2 (μ.prod (stdGaussian E)) :=
    Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst f
  have hae : (fun z => inner ℝ (momentumEmbedding μ G z) (If z)) =ᵐ[μ.prod (stdGaussian E)]
      fun z => inner ℝ (G z.1) z.2 * f z.1 := by
    filter_upwards [momentumAction_coe μ G,
      Lp.coeFn_compMeasurePreserving f (measurePreserving_fst (ν := stdGaussian E))] with z hG hf
    change inner ℝ (momentumAction μ G z) (If z) = _
    change If z = f z.1 at hf
    rw [hG, hf, real_inner_comm]
    rfl
  have hint := (L2.integrable_inner (momentumEmbedding μ G) If).congr hae
  rw [L2.inner_def, integral_congr_ae hae, integral_prod _ hint]
  simp only [integral_mul_const, gaussian_inner_mean, zero_mul, integral_zero]

/-- Position functions and first momentum chaos are orthogonal for the actual Gaussian law. -/
theorem gaussianMomentumEmbedding_inner_position (G : Lp E 2 μ) (f : Lp ℝ 2 μ) :
    inner ℝ (gaussianMomentumEmbedding μ G) (positionEmbedding μ f) = 0 := by
  change inner ℝ (hiddenEmbedding μ (momentumEmbedding μ G))
    (hiddenEmbedding μ (Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst f)) = 0
  rw [(hiddenEmbedding μ).inner_map_map]
  exact momentum_orthogonal_position μ G f

/-- Averaging over the two Gaussian coordinates, as the adjoint of the actual position embedding. -/
def gaussianAverage : Lp ℝ 2 (gaussianPhaseMeasure μ) →L[ℝ] Lp ℝ 2 μ :=
  (positionEmbedding μ).toContinuousLinearMap.adjoint

/-- The actual orthogonal projection onto position functions in phase L2. -/
def gaussianPositionProjection : Lp ℝ 2 (gaussianPhaseMeasure μ) →L[ℝ]
    Lp ℝ 2 (gaussianPhaseMeasure μ) :=
  (positionEmbedding μ).toContinuousLinearMap.comp (gaussianAverage μ)

/-- The first Gaussian momentum coefficient is the adjoint of the constructed chaos isometry. -/
def gaussianMomentumAdjoint : Lp ℝ 2 (gaussianPhaseMeasure μ) →L[ℝ] Lp E 2 μ :=
  (gaussianMomentumEmbedding μ).toContinuousLinearMap.adjoint

omit [BorelSpace E] [IsProbabilityMeasure μ] in
@[simp] theorem gaussianAverage_positionEmbedding (f : Lp ℝ 2 μ) :
    gaussianAverage μ (positionEmbedding μ f) = f := by
  have h := congrArg (fun T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ => T f)
    (positionEmbedding μ).adjoint_comp_self
  exact h

@[simp] theorem gaussianMomentumAdjoint_embedding (G : Lp E 2 μ) :
    gaussianMomentumAdjoint μ (gaussianMomentumEmbedding μ G) = G := by
  have h := congrArg (fun T : Lp E 2 μ →L[ℝ] Lp E 2 μ => T G)
    (gaussianMomentumEmbedding μ).adjoint_comp_self
  exact h

@[simp] theorem gaussianMomentumAdjoint_positionEmbedding (f : Lp ℝ 2 μ) :
    gaussianMomentumAdjoint μ (positionEmbedding μ f) = 0 := by
  apply ext_inner_left ℝ
  intro G
  rw [inner_zero_right]
  exact ((gaussianMomentumEmbedding μ).toContinuousLinearMap.adjoint_inner_right G _).trans
    (gaussianMomentumEmbedding_inner_position μ G f)

@[simp] theorem gaussianAverage_momentumEmbedding (G : Lp E 2 μ) :
    gaussianAverage μ (gaussianMomentumEmbedding μ G) = 0 := by
  apply ext_inner_right ℝ
  intro f
  rw [inner_zero_left]
  exact ((positionEmbedding μ).toContinuousLinearMap.adjoint_inner_left f _).trans
    (gaussianMomentumEmbedding_inner_position μ G f)

omit [BorelSpace E] [IsProbabilityMeasure μ] in
@[simp] theorem gaussianPositionProjection_idempotent (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    gaussianPositionProjection μ (gaussianPositionProjection μ f) =
      gaussianPositionProjection μ f := by
  change positionEmbedding μ (gaussianAverage μ (positionEmbedding μ (gaussianAverage μ f))) = _
  rw [gaussianAverage_positionEmbedding]
  rfl

omit [BorelSpace E] [IsProbabilityMeasure μ] in
/-- Explicit Gaussian integral characterization of the averaging adjoint. -/
theorem gaussianAverage_pairing (f : Lp ℝ 2 μ)
    (F : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    inner ℝ f (gaussianAverage μ F) =
      ∫ z, f z.1.1 * F z ∂gaussianPhaseMeasure μ := by
  unfold gaussianAverage
  rw [ContinuousLinearMap.adjoint_inner_right, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [positionEmbedding_coe μ f] with z hz
  change inner ℝ (positionEmbedding μ f z) (F z) = _
  rw [hz, real_inner_comm]
  rfl

/-- Integral characterization of the first momentum coefficient adjoint. -/
theorem gaussianMomentumAdjoint_pairing (G : Lp E 2 μ)
    (F : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    inner ℝ G (gaussianMomentumAdjoint μ F) =
      ∫ z, inner ℝ (G z.1.1) z.1.2 * F z ∂gaussianPhaseMeasure μ := by
  unfold gaussianMomentumAdjoint
  rw [ContinuousLinearMap.adjoint_inner_right, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [gaussianMomentumEmbedding_coe μ G] with z hz
  change inner ℝ (gaussianMomentumEmbedding μ G z) (F z) = _
  rw [hz, real_inner_comm]
  rfl

omit [BorelSpace E] in
/-- Averaging really is integration over momentum and the independent Gaussian coordinate. -/
theorem gaussianAverage_coe (F : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    gaussianAverage μ F =ᵐ[μ] fun x =>
      ∫ p, ∫ e, F ((x, p), e) ∂stdGaussian E ∂stdGaussian E := by
  have hF : Integrable F (gaussianPhaseMeasure μ) := (Lp.memLp F).integrable (by norm_num)
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    ((Lp.memLp (gaussianAverage μ F)).integrable (by norm_num))
    hF.integral_prod_left.integral_prod_left
  intro s hs hμs
  let f : Lp ℝ 2 μ := indicatorConstLp 2 hs hμs.ne (1 : ℝ)
  have htest := gaussianAverage_pairing μ f F
  have hleft : inner ℝ f (gaussianAverage μ F) = ∫ x in s, gaussianAverage μ F x ∂μ :=
    L2.inner_indicatorConstLp_one hs hμs.ne _
  rw [hleft] at htest
  rw [htest]
  have hcoe : (fun z : GaussianPhase E => f z.1.1 * F z) =ᵐ[gaussianPhaseMeasure μ]
      fun z => s.indicator (fun x => F ((x, z.1.2), z.2)) z.1.1 := by
    filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae
      (measurePreserving_fst.quasiMeasurePreserving.ae
        (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs.ne) (c := (1 : ℝ))))] with z hz
    change f z.1.1 = _ at hz
    rw [hz]
    by_cases hx : z.1.1 ∈ s <;> simp [hx]
  rw [integral_congr_ae hcoe]
  have hi : Integrable (fun z : GaussianPhase E =>
      s.indicator (fun x => F ((x, z.1.2), z.2)) z.1.1) (gaussianPhaseMeasure μ) := by
    have h := hF.indicator (hs.preimage (measurable_fst.comp measurable_fst))
    convert h using 1
    ext z
    by_cases hz : z.1.1 ∈ s <;> simp [hz]
  calc
    _ = ∫ z : E × E, ∫ e, s.indicator (fun x => F ((x, z.2), e)) z.1
        ∂stdGaussian E ∂(μ.prod (stdGaussian E)) := integral_prod _ hi
    _ = ∫ x, ∫ p, ∫ e, s.indicator (fun y => F ((y, p), e)) x
        ∂stdGaussian E ∂stdGaussian E ∂μ := integral_prod _ hi.integral_prod_left
    _ = _ := by
      rw [← integral_indicator hs]
      congr 1
      ext x
      by_cases hx : x ∈ s <;> simp [hx]

omit [BorelSpace E] [IsProbabilityMeasure μ] in
theorem gaussianAverage_norm_le : ‖gaussianAverage μ‖ ≤ 1 := by
  change ‖ContinuousLinearMap.adjoint (positionEmbedding μ).toContinuousLinearMap‖ ≤ 1
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simp)

theorem gaussianMomentumAdjoint_norm_le : ‖gaussianMomentumAdjoint μ‖ ≤ 1 := by
  change ‖ContinuousLinearMap.adjoint (gaussianMomentumEmbedding μ).toContinuousLinearMap‖ ≤ 1
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simp)

omit [BorelSpace E] [IsProbabilityMeasure μ] in
theorem gaussianPositionProjection_norm_le : ‖gaussianPositionProjection μ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖positionEmbedding μ (gaussianAverage μ f)‖ ≤ 1 * ‖f‖
  rw [(positionEmbedding μ).norm_map]
  exact ((gaussianAverage μ).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (gaussianAverage_norm_le μ) (norm_nonneg _))

omit [BorelSpace E] [IsProbabilityMeasure μ] in
/-- The position projection is self-adjoint, since it is I composed with its adjoint. -/
theorem gaussianPositionProjection_adjoint :
    (gaussianPositionProjection μ).adjoint = gaussianPositionProjection μ := by
  unfold gaussianPositionProjection gaussianAverage
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]

omit [BorelSpace E] [IsProbabilityMeasure μ] in
@[simp] theorem gaussianPositionProjection_positionEmbedding (f : Lp ℝ 2 μ) :
    gaussianPositionProjection μ (positionEmbedding μ f) = positionEmbedding μ f := by
  change positionEmbedding μ (gaussianAverage μ (positionEmbedding μ f)) = _
  rw [gaussianAverage_positionEmbedding]

@[simp] theorem gaussianPositionProjection_momentumEmbedding (G : Lp E 2 μ) :
    gaussianPositionProjection μ (gaussianMomentumEmbedding μ G) = 0 := by
  change positionEmbedding μ (gaussianAverage μ (gaussianMomentumEmbedding μ G)) = 0
  rw [gaussianAverage_momentumEmbedding, map_zero]

end AcceleratedLogConcave.Kinetic
