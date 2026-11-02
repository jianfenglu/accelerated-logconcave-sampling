import AcceleratedLogConcave.Kinetic.GaussianEmbedding
import AcceleratedLogConcave.Kinetic.ReferenceFlow.GaussianDensity
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! Genuine Gaussian phase integration by parts. The position coefficient is
only L2 and its continuous multiplier can grow without a global bound; compact
phase tests supply all additional integrability. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace Set Function
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Directional Gaussian Stein identity for a genuine compact C1 test. -/
theorem stdGaussian_compact_fderiv (f : E → ℝ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (v : E) :
    (∫ x, fderiv ℝ f x v ∂stdGaussian E) =
      ∫ x, inner ℝ v x * f x ∂stdGaussian E := by
  let d : E → ℝ := standardGaussianDensity
  have hd : ContDiff ℝ 1 d := standardGaussianDensity_contDiff
  have hi1 : Integrable (fun x => fderiv ℝ d x v * f x) :=
    (((hd.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul hf.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hi2 : Integrable (fun x => d x * fderiv ℝ f x v) :=
    (hd.continuous.mul ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const)).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ v).mul_left
  have hi3 : Integrable (fun x => d x * f x) :=
    (hd.continuous.mul hf.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi1 hi2 hi3
    (fun x _ => hd.differentiable_one x) (fun x _ => hf.differentiable_one x)
  have hdv (x : E) : fderiv ℝ d x v = -d x * inner ℝ v x := by
    rw [(standardGaussianDensity_hasFDerivAt x).fderiv]
    simp [d, real_inner_comm]
  simp_rw [hdv] at hh
  have integral_density (g : E → ℝ) :
      (∫ x, g x ∂stdGaussian E) = ∫ x, d x * g x := by
    rw [stdGaussian_eq_volume_density,
      integral_withDensity_eq_integral_toReal_smul hd.continuous.measurable.ennreal_ofReal
        (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (le_of_lt (standardGaussianDensity_pos _)), smul_eq_mul, d]
  rw [integral_density, integral_density, hh, ← integral_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by ring

omit [BorelSpace E] in
private theorem phase_position_mp (μ : Measure E) :
    MeasurePreserving (fun z : GaussianPhase E => z.1.1) (gaussianPhaseMeasure μ) μ :=
  (measurePreserving_fst (μ := μ) (ν := stdGaussian E)).comp
    (measurePreserving_fst (μ := μ.prod (stdGaussian E)) (ν := stdGaussian E))

/-- Compact continuous phase coefficients can multiply any actual L2 position coefficient. -/
theorem phase_compact_position_integrable (μ : Measure E) [IsProbabilityMeasure μ]
    (a : Lp ℝ 2 μ) (c : E → ℝ) (hc : Continuous c)
    (F : GaussianPhase E → ℝ) (hF : Continuous F) (hK : HasCompactSupport F) :
    Integrable (fun z => a z.1.1 * c z.1.1 * F z) (gaussianPhaseMeasure μ) := by
  have ha := (Lp.memLp a).comp_measurePreserving (phase_position_mp μ)
  have hb : MemLp (fun z : GaussianPhase E => c z.1.1 * F z) 2 (gaussianPhaseMeasure μ) :=
    ((hc.comp (continuous_fst.comp continuous_fst)).mul hF).memLp_of_hasCompactSupport hK.mul_left
  convert ha.integrable_mul hb using 1
  funext z
  dsimp only [Pi.mul_apply, Function.comp_apply]
  ring

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem momentum_slice_compact {φ : GaussianPhase E → ℝ}
    (hc : HasCompactSupport φ) (x e : E) : HasCompactSupport (fun p => φ ((x,p),e)) := by
  apply HasCompactSupport.of_support_subset_isCompact (hc.image (continuous_snd.comp continuous_fst))
  intro p hp
  exact ⟨((x,p),e), subset_tsupport _ hp, rfl⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem momentum_slice_fderiv {φ : GaussianPhase E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (x p e v : E) :
    fderiv ℝ (fun y => φ ((x,y),e)) p v = fderiv ℝ φ ((x,p),e) ((0,v),0) := by
  have hi := ((hasFDerivAt_const x p).prodMk (hasFDerivAt_id (𝕜 := ℝ) p)).prodMk
    (hasFDerivAt_const e p)
  exact congrArg (fun L : E →L[ℝ] ℝ => L v)
    (((hφ.differentiable one_ne_zero ((x,p),e)).hasFDerivAt).comp p hi).fderiv

/-- Gaussian momentum integration by parts, with no derivative assumed on the
position coefficient or its continuous multiplier. -/
theorem phase_momentum_ibp (μ : Measure E) [IsProbabilityMeasure μ]
    (a : Lp ℝ 2 μ) (c : E → ℝ) (hc : Continuous c) (v : E)
    (φ : GaussianPhase E → ℝ) (hφ : ContDiff ℝ 1 φ) (hK : HasCompactSupport φ) :
    Integrable (fun z => a z.1.1 * c z.1.1 * fderiv ℝ φ z ((0,v),0)) (gaussianPhaseMeasure μ) ∧
    Integrable (fun z => a z.1.1 * c z.1.1 * (inner ℝ v z.1.2 * φ z)) (gaussianPhaseMeasure μ) ∧
    (∫ z, a z.1.1 * c z.1.1 * fderiv ℝ φ z ((0,v),0) ∂gaussianPhaseMeasure μ) =
      ∫ z, a z.1.1 * c z.1.1 * (inner ℝ v z.1.2 * φ z) ∂gaussianPhaseMeasure μ := by
  have hl := phase_compact_position_integrable μ a c hc _
    ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const) (hK.fderiv_apply ℝ ((0,v),0))
  have hr := phase_compact_position_integrable μ a c hc (fun z => inner ℝ v z.1.2 * φ z)
    ((continuous_const.inner (continuous_snd.comp continuous_fst)).mul hφ.continuous) hK.mul_left
  refine ⟨hl, hr, ?_⟩
  change (∫ z, _ ∂(μ.prod (stdGaussian E)).prod (stdGaussian E)) = ∫ z, _ ∂(μ.prod (stdGaussian E)).prod (stdGaussian E)
  rw [integral_prod_symm _ hl, integral_prod_symm _ hr]
  apply integral_congr_ae
  filter_upwards [hl.prod_left_ae, hr.prod_left_ae] with e hle hre
  rw [integral_prod _ hle, integral_prod _ hre]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [integral_const_mul, integral_const_mul]
    congr 1
    have hs : ContDiff ℝ 1 (fun p => φ ((x,p),e)) :=
      hφ.comp ((contDiff_const.prodMk contDiff_id).prodMk contDiff_const)
    simpa only [momentum_slice_fderiv hφ] using
      stdGaussian_compact_fderiv _ hs (momentum_slice_compact hK x e) v

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem auxiliary_slice_compact {φ : GaussianPhase E → ℝ}
    (hc : HasCompactSupport φ) (x p : E) : HasCompactSupport (fun e => φ ((x,p),e)) := by
  apply HasCompactSupport.of_support_subset_isCompact (hc.image continuous_snd)
  intro e he
  exact ⟨((x,p),e), subset_tsupport _ he, rfl⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem auxiliary_slice_fderiv {φ : GaussianPhase E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (x p e v : E) :
    fderiv ℝ (fun y => φ ((x,p),y)) e v = fderiv ℝ φ ((x,p),e) ((0,0),v) := by
  have hi := (hasFDerivAt_const (x,p) e).prodMk (hasFDerivAt_id (𝕜 := ℝ) e)
  exact congrArg (fun L : E →L[ℝ] ℝ => L v)
    (((hφ.differentiable one_ne_zero ((x,p),e)).hasFDerivAt).comp e hi).fderiv

/-- The corresponding identity for the auxiliary Gaussian. -/
theorem phase_auxiliary_ibp (μ : Measure E) [IsProbabilityMeasure μ]
    (a : Lp ℝ 2 μ) (c : E → ℝ) (hc : Continuous c) (v : E)
    (φ : GaussianPhase E → ℝ) (hφ : ContDiff ℝ 1 φ) (hK : HasCompactSupport φ) :
    Integrable (fun z => a z.1.1 * c z.1.1 * fderiv ℝ φ z ((0,0),v)) (gaussianPhaseMeasure μ) ∧
    Integrable (fun z => a z.1.1 * c z.1.1 * (inner ℝ v z.2 * φ z)) (gaussianPhaseMeasure μ) ∧
    (∫ z, a z.1.1 * c z.1.1 * fderiv ℝ φ z ((0,0),v) ∂gaussianPhaseMeasure μ) =
      ∫ z, a z.1.1 * c z.1.1 * (inner ℝ v z.2 * φ z) ∂gaussianPhaseMeasure μ := by
  have hl := phase_compact_position_integrable μ a c hc _
    ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const) (hK.fderiv_apply ℝ ((0,0),v))
  have hr := phase_compact_position_integrable μ a c hc (fun z => inner ℝ v z.2 * φ z)
    ((continuous_const.inner continuous_snd).mul hφ.continuous) hK.mul_left
  refine ⟨hl, hr, ?_⟩
  change (∫ z, _ ∂(μ.prod (stdGaussian E)).prod (stdGaussian E)) = ∫ z, _ ∂(μ.prod (stdGaussian E)).prod (stdGaussian E)
  rw [integral_prod _ hl, integral_prod _ hr]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun xp => by
    dsimp only
    rw [integral_const_mul, integral_const_mul]
    congr 1
    have hs : ContDiff ℝ 1 (fun e => φ (xp,e)) :=
      hφ.comp (contDiff_const.prodMk contDiff_id)
    simpa only [auxiliary_slice_fderiv hφ] using
      stdGaussian_compact_fderiv _ hs (auxiliary_slice_compact hK xp.1 xp.2) v

/-- Momentum Stein identity with the first-chaos prefactor. -/
theorem phase_momentum_linear_ibp (μ : Measure E) [IsProbabilityMeasure μ]
    (a : Lp ℝ 2 μ) (c : E → ℝ) (hc : Continuous c) (b v : E)
    (φ : GaussianPhase E → ℝ) (hφ : ContDiff ℝ 1 φ) (hK : HasCompactSupport φ) :
    Integrable (fun z => a z.1.1 * c z.1.1 *
      (inner ℝ b z.1.2 * fderiv ℝ φ z ((0,v),0))) (gaussianPhaseMeasure μ) ∧
    Integrable (fun z => a z.1.1 * c z.1.1 *
      ((inner ℝ b z.1.2 * inner ℝ v z.1.2 - inner ℝ b v) * φ z)) (gaussianPhaseMeasure μ) ∧
    (∫ z, a z.1.1 * c z.1.1 * (inner ℝ b z.1.2 * fderiv ℝ φ z ((0,v),0))
      ∂gaussianPhaseMeasure μ) =
      ∫ z, a z.1.1 * c z.1.1 *
        ((inner ℝ b z.1.2 * inner ℝ v z.1.2 - inner ℝ b v) * φ z)
        ∂gaussianPhaseMeasure μ := by
  let l : GaussianPhase E →L[ℝ] ℝ := (innerSL ℝ b).comp
    ((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.fst ℝ (E×E) E))
  let ψ : GaussianPhase E → ℝ := fun z => l z * φ z
  have hψ : ContDiff ℝ 1 ψ := l.contDiff.mul hφ
  have hψK : HasCompactSupport ψ := hK.mul_left
  have hd (z : GaussianPhase E) : fderiv ℝ ψ z ((0,v),0) =
      inner ℝ b z.1.2 * fderiv ℝ φ z ((0,v),0) + inner ℝ b v * φ z := by
    change (fderiv ℝ (⇑l * φ) z) _ = _
    rw [((l.hasFDerivAt).mul (hφ.differentiable_one z).hasFDerivAt).fderiv]
    simp [l, mul_comm]
  have hl := phase_compact_position_integrable μ a c hc
    (fun z => inner ℝ b z.1.2 * fderiv ℝ φ z ((0,v),0))
    ((continuous_const.inner (continuous_snd.comp continuous_fst)).mul
      ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const))
    (hK.fderiv_apply ℝ ((0,v),0)).mul_left
  have hr := phase_compact_position_integrable μ a c hc
    (fun z => (inner ℝ b z.1.2 * inner ℝ v z.1.2 - inner ℝ b v) * φ z)
    (by fun_prop) hK.mul_left
  have h0 := phase_compact_position_integrable μ a c hc (fun z => inner ℝ b v * φ z)
    (continuous_const.mul hφ.continuous) hK.mul_left
  refine ⟨hl, hr, ?_⟩
  have hi := (phase_momentum_ibp μ a c hc v ψ hψ hψK).2.2
  have heL : (∫ z, a z.1.1 * c z.1.1 * fderiv ℝ ψ z ((0,v),0) ∂gaussianPhaseMeasure μ) =
      (∫ z, a z.1.1 * c z.1.1 * (inner ℝ b z.1.2 * fderiv ℝ φ z ((0,v),0)) ∂gaussianPhaseMeasure μ) +
      ∫ z, a z.1.1 * c z.1.1 * (inner ℝ b v * φ z) ∂gaussianPhaseMeasure μ := by
    rw [← integral_add hl h0]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by dsimp only; rw [hd]; ring
  have heR : (∫ z, a z.1.1 * c z.1.1 * (inner ℝ v z.1.2 * ψ z) ∂gaussianPhaseMeasure μ) =
      (∫ z, a z.1.1 * c z.1.1 * ((inner ℝ b z.1.2 * inner ℝ v z.1.2 - inner ℝ b v) * φ z)
        ∂gaussianPhaseMeasure μ) +
      ∫ z, a z.1.1 * c z.1.1 * (inner ℝ b v * φ z) ∂gaussianPhaseMeasure μ := by
    rw [← integral_add hr h0]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by dsimp [ψ, l]; ring
  rw [heL, heR] at hi
  exact add_right_cancel hi

/-- Auxiliary Stein identity with a retained first momentum-chaos prefactor. -/
theorem phase_auxiliary_linear_ibp (μ : Measure E) [IsProbabilityMeasure μ]
    (a : Lp ℝ 2 μ) (c : E → ℝ) (hc : Continuous c) (b v : E)
    (φ : GaussianPhase E → ℝ) (hφ : ContDiff ℝ 1 φ) (hK : HasCompactSupport φ) :
    Integrable (fun z => a z.1.1 * c z.1.1 *
      (inner ℝ b z.1.2 * fderiv ℝ φ z ((0,0),v))) (gaussianPhaseMeasure μ) ∧
    Integrable (fun z => a z.1.1 * c z.1.1 *
      (inner ℝ b z.1.2 * inner ℝ v z.2 * φ z)) (gaussianPhaseMeasure μ) ∧
    (∫ z, a z.1.1 * c z.1.1 * (inner ℝ b z.1.2 * fderiv ℝ φ z ((0,0),v))
      ∂gaussianPhaseMeasure μ) =
      ∫ z, a z.1.1 * c z.1.1 * (inner ℝ b z.1.2 * inner ℝ v z.2 * φ z)
        ∂gaussianPhaseMeasure μ := by
  let l : GaussianPhase E →L[ℝ] ℝ := (innerSL ℝ b).comp
    ((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.fst ℝ (E×E) E))
  let ψ : GaussianPhase E → ℝ := fun z => l z * φ z
  have hψ : ContDiff ℝ 1 ψ := l.contDiff.mul hφ
  have hd (z : GaussianPhase E) : fderiv ℝ ψ z ((0,0),v) =
      inner ℝ b z.1.2 * fderiv ℝ φ z ((0,0),v) := by
    change (fderiv ℝ (⇑l * φ) z) _ = _
    rw [((l.hasFDerivAt).mul (hφ.differentiable_one z).hasFDerivAt).fderiv]
    simp [l]
  have hl := phase_compact_position_integrable μ a c hc
    (fun z => inner ℝ b z.1.2 * fderiv ℝ φ z ((0,0),v))
    ((continuous_const.inner (continuous_snd.comp continuous_fst)).mul
      ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const))
    (hK.fderiv_apply ℝ ((0,0),v)).mul_left
  have hr := phase_compact_position_integrable μ a c hc
    (fun z => inner ℝ b z.1.2 * inner ℝ v z.2 * φ z) (by fun_prop) hK.mul_left
  refine ⟨hl, hr, ?_⟩
  have hi := (phase_auxiliary_ibp μ a c hc v ψ hψ hK.mul_left).2.2
  simp_rw [hd] at hi
  rw [hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by dsimp [ψ, l]; ring

end AcceleratedLogConcave.Kinetic
