import AcceleratedLogConcave.Kinetic.GaussianEmbedding
import AcceleratedLogConcave.Analysis.WeightedGradient.Basic

/-! Weighted position integration by parts against arbitrary compact C1 phase
space tests. Compact test coefficients and genuine L2 gradients justify Fubini. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Function ProbabilityTheory
open scoped ContDiff RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic
open Analysis.WeightedGradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem phase_slice_compact {φ : GaussianPhase E → ℝ}
    (hφ : HasCompactSupport φ) (p e : E) : HasCompactSupport (fun x => φ ((x, p), e)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (hφ.image (continuous_fst.comp continuous_fst))
  intro x hx
  exact ⟨((x, p), e), subset_tsupport _ hx, rfl⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem phase_slice_fderiv {φ : GaussianPhase E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (x p e v : E) :
    fderiv ℝ (fun y => φ ((y, p), e)) x v = fderiv ℝ φ ((x, p), e) ((v, 0), 0) := by
  have hi := ((hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const p x)).prodMk
    (hasFDerivAt_const e x)
  have hh := ((hφ.differentiable one_ne_zero ((x, p), e)).hasFDerivAt).comp x hi
  exact congrArg (fun L : E →L[ℝ] ℝ => L v) hh.fderiv

omit [BorelSpace E] in
private theorem phase_position_measurePreserving (μ : Measure E) :
    MeasurePreserving (fun z : GaussianPhase E => z.1.1) (gaussianPhaseMeasure μ) μ :=
  (measurePreserving_fst (μ := μ) (ν := stdGaussian E)).comp
    (measurePreserving_fst (μ := μ.prod (stdGaussian E)) (ν := stdGaussian E))

/-- Genuine weak weighted position integration by parts, sliced over the two
actual Gaussian coordinates. Both whole-phase products are integrable. -/
theorem phase_test_weighted_ibp_mul (μ : Measure E) [IsProbabilityMeasure μ]
    (V : E → ℝ) (hV : ContDiff ℝ 1 V)
    (hI : Integrable (fun x => Real.exp (-V x)))
    (hμ : μ = volume.tilted (fun x => -V x))
    (u : Sobolev μ V hV hI hμ) (w : E → ℝ) (hw : Continuous w) (v : E)
    (φ : GaussianPhase E → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    Integrable (fun z => φ z * inner ℝ (closedGradient μ V hV hI hμ u z.1.1) v *
      w z.1.2) (gaussianPhaseMeasure μ) ∧
    Integrable (fun z => (u : Lp ℝ 2 μ) z.1.1 * w z.1.2 *
      (fderiv ℝ φ z ((v, 0), 0) - φ z * fderiv ℝ V z.1.1 v)) (gaussianPhaseMeasure μ) ∧
    (∫ z, φ z * inner ℝ (closedGradient μ V hV hI hμ u z.1.1) v * w z.1.2
      ∂gaussianPhaseMeasure μ) =
      -∫ z, (u : Lp ℝ 2 μ) z.1.1 * w z.1.2 *
        (fderiv ℝ φ z ((v, 0), 0) - φ z * fderiv ℝ V z.1.1 v)
        ∂gaussianPhaseMeasure μ := by
  let A : GaussianPhase E → ℝ := fun z => φ z * w z.1.2
  let B : GaussianPhase E → ℝ := fun z => w z.1.2 *
    (fderiv ℝ φ z ((v, 0), 0) - φ z * fderiv ℝ V z.1.1 v)
  have hA : MemLp A 2 (gaussianPhaseMeasure μ) := by
    apply Continuous.memLp_of_hasCompactSupport
    · exact hφ.continuous.mul (hw.comp (continuous_snd.comp continuous_fst))
    · exact hc.mul_right
  have hB : MemLp B 2 (gaussianPhaseMeasure μ) := by
    apply Continuous.memLp_of_hasCompactSupport
    · exact (hw.comp (continuous_snd.comp continuous_fst)).mul
        (((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const).sub
          (hφ.continuous.mul (((hV.continuous_fderiv one_ne_zero).comp
            (continuous_fst.comp continuous_fst)).clm_apply continuous_const)))
    · exact ((hc.fderiv_apply ℝ ((v, 0), 0)).sub hc.mul_right).mul_left
  have hu : MemLp (fun z : GaussianPhase E => (u : Lp ℝ 2 μ) z.1.1) 2
      (gaussianPhaseMeasure μ) :=
    (Lp.memLp (u : Lp ℝ 2 μ)).comp_measurePreserving (phase_position_measurePreserving μ)
  have hD : MemLp (fun z : GaussianPhase E => inner ℝ (closedGradient μ V hV hI hμ u z.1.1) v)
      2 (gaussianPhaseMeasure μ) :=
    ((Lp.memLp (closedGradient μ V hV hI hμ u)).inner_const v).comp_measurePreserving
      (phase_position_measurePreserving μ)
  let f : GaussianPhase E → ℝ := fun z => φ z * inner ℝ (closedGradient μ V hV hI hμ u z.1.1) v * w z.1.2
  let g : GaussianPhase E → ℝ := fun z => (u : Lp ℝ 2 μ) z.1.1 * w z.1.2 *
    (fderiv ℝ φ z ((v, 0), 0) - φ z * fderiv ℝ V z.1.1 v)
  have hf : Integrable f (gaussianPhaseMeasure μ) := by
    convert hA.integrable_mul hD using 1
    funext z
    dsimp [f, A]
    ring
  have hg : Integrable g (gaussianPhaseMeasure μ) := by
    convert hu.integrable_mul hB using 1
    funext z
    dsimp [g, B]
    ring
  refine ⟨hf, hg, ?_⟩
  change (∫ z, f z ∂(μ.prod (stdGaussian E)).prod (stdGaussian E)) =
    -∫ z, g z ∂(μ.prod (stdGaussian E)).prod (stdGaussian E)
  rw [integral_prod_symm f hf, integral_prod_symm g hg, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [hf.prod_left_ae, hg.prod_left_ae] with e hfe hge
  rw [integral_prod_symm _ hfe, integral_prod_symm _ hge, ← integral_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p => by
    have hs : ContDiff ℝ 1 (fun x => φ ((x, p), e)) :=
      hφ.comp ((contDiff_id.prodMk contDiff_const).prodMk contDiff_const)
    have hi := (closedGradient_integrationByParts μ V hV hI hμ u
      (fun x => φ ((x, p), e)) hs (phase_slice_compact hc p e) v).2.2
    simp_rw [phase_slice_fderiv hφ] at hi
    change (∫ x, (φ ((x, p), e) * inner ℝ (closedGradient μ V hV hI hμ u x) v) * w p ∂μ) =
      -(∫ x, (u : Lp ℝ 2 μ) x * w p *
        (fderiv ℝ φ ((x, p), e) ((v, 0), 0) - φ ((x, p), e) * fderiv ℝ V x v) ∂μ)
    rw [integral_mul_const, hi]
    have hr : (fun x => (u : Lp ℝ 2 μ) x * w p *
        (fderiv ℝ φ ((x, p), e) ((v, 0), 0) - φ ((x, p), e) * fderiv ℝ V x v)) =
        (fun x => ((u : Lp ℝ 2 μ) x *
        (fderiv ℝ φ ((x, p), e) ((v, 0), 0) - φ ((x, p), e) * fderiv ℝ V x v)) * w p) := by
      funext x
      ring
    rw [hr, integral_mul_const, neg_mul]

/-- First momentum-chaos specialization of the genuine phase test identity. -/
theorem phase_test_weighted_ibp (μ : Measure E) [IsProbabilityMeasure μ]
    (V : E → ℝ) (hV : ContDiff ℝ 1 V)
    (hI : Integrable (fun x => Real.exp (-V x)))
    (hμ : μ = volume.tilted (fun x => -V x))
    (u : Sobolev μ V hV hI hμ) (b v : E)
    (φ : GaussianPhase E → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    Integrable (fun z => φ z * inner ℝ (closedGradient μ V hV hI hμ u z.1.1) v *
      inner ℝ b z.1.2) (gaussianPhaseMeasure μ) ∧
    Integrable (fun z => (u : Lp ℝ 2 μ) z.1.1 * inner ℝ b z.1.2 *
      (fderiv ℝ φ z ((v, 0), 0) - φ z * fderiv ℝ V z.1.1 v)) (gaussianPhaseMeasure μ) ∧
    (∫ z, φ z * inner ℝ (closedGradient μ V hV hI hμ u z.1.1) v * inner ℝ b z.1.2
      ∂gaussianPhaseMeasure μ) =
      -∫ z, (u : Lp ℝ 2 μ) z.1.1 * inner ℝ b z.1.2 *
        (fderiv ℝ φ z ((v, 0), 0) - φ z * fderiv ℝ V z.1.1 v)
        ∂gaussianPhaseMeasure μ := by
  exact phase_test_weighted_ibp_mul μ V hV hI hμ u (fun p => inner ℝ b p)
    (continuous_const.inner continuous_id) v φ hφ hc

/-- Position-embedding specialization, with momentum weight one. -/
theorem phase_test_weighted_ibp_position (μ : Measure E) [IsProbabilityMeasure μ]
    (V : E → ℝ) (hV : ContDiff ℝ 1 V)
    (hI : Integrable (fun x => Real.exp (-V x)))
    (hμ : μ = volume.tilted (fun x => -V x))
    (u : Sobolev μ V hV hI hμ) (v : E)
    (φ : GaussianPhase E → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    Integrable (fun z => φ z * inner ℝ (closedGradient μ V hV hI hμ u z.1.1) v) (gaussianPhaseMeasure μ) ∧
    Integrable (fun z => (u : Lp ℝ 2 μ) z.1.1 *
      (fderiv ℝ φ z ((v, 0), 0) - φ z * fderiv ℝ V z.1.1 v)) (gaussianPhaseMeasure μ) ∧
    (∫ z, φ z * inner ℝ (closedGradient μ V hV hI hμ u z.1.1) v
      ∂gaussianPhaseMeasure μ) =
      -∫ z, (u : Lp ℝ 2 μ) z.1.1 *
        (fderiv ℝ φ z ((v, 0), 0) - φ z * fderiv ℝ V z.1.1 v)
        ∂gaussianPhaseMeasure μ := by
  simpa only [mul_one] using phase_test_weighted_ibp_mul μ V hV hI hμ u
    (fun _ => (1 : ℝ)) continuous_const v φ hφ hc

end AcceleratedLogConcave.Kinetic
