import AcceleratedLogConcave.Kinetic.GaussianEmbedding
import AcceleratedLogConcave.Analysis.Poisson.StrongDerivative
import AcceleratedLogConcave.Analysis.MovingPoisson

/-! Moving correctors on the fixed Gaussian reference space. Strong derivatives
of the Poisson gradient yield scalar derivatives and norm increments of the
corrector; no strong derivative is inferred merely by taking an adjoint. -/
noncomputable section
open MeasureTheory InnerProductSpace Set
open scoped Topology
namespace AcceleratedLogConcave.Kinetic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [IsProbabilityMeasure μ]

/-- The corrector built from a gradient inverse on the fixed position space. -/
def referenceCorrector (G : Lp ℝ 2 μ →L[ℝ] Lp E 2 μ) :
    Lp ℝ 2 (gaussianPhaseMeasure μ) →L[ℝ] Lp ℝ 2 (gaussianPhaseMeasure μ) :=
  (positionEmbedding μ).toContinuousLinearMap ∘L G.adjoint ∘L gaussianMomentumAdjoint μ

/-- A scalar pairing uses the original gradient operator, not a differentiated adjoint. -/
theorem referenceCorrector_pairing (G : Lp ℝ 2 μ →L[ℝ] Lp E 2 μ)
    (f g : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    inner ℝ f (referenceCorrector μ G g) =
      inner ℝ (G (gaussianAverage μ f)) (gaussianMomentumAdjoint μ g) := by
  change inner ℝ f ((positionEmbedding μ).toContinuousLinearMap (G.adjoint (gaussianMomentumAdjoint μ g))) = _
  rw [← (positionEmbedding μ).toContinuousLinearMap.adjoint_inner_left,
    G.adjoint_inner_right]
  rfl

/-- The corrector is contractive as a function of its gradient inverse. -/
theorem referenceCorrector_norm_le (G : Lp ℝ 2 μ →L[ℝ] Lp E 2 μ) :
    ‖referenceCorrector μ G‖ ≤ ‖G‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg G)
  intro f
  change ‖positionEmbedding μ (G.adjoint (gaussianMomentumAdjoint μ f))‖ ≤ _
  rw [(positionEmbedding μ).norm_map]
  apply (G.adjoint.le_opNorm _).trans
  rw [ContinuousLinearMap.adjoint.norm_map]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg G)
  exact ((gaussianMomentumAdjoint μ).le_opNorm f).trans
    (by simpa using mul_le_mul_of_nonneg_right (gaussianMomentumAdjoint_norm_le μ) (norm_nonneg f))

/-- Adjoint norm equality, rather than adjoint differentiation, controls increments. -/
theorem referenceCorrector_norm_sub_le (G H : Lp ℝ 2 μ →L[ℝ] Lp E 2 μ) :
    ‖referenceCorrector μ G - referenceCorrector μ H‖ ≤ ‖G - H‖ := by
  have he : referenceCorrector μ G - referenceCorrector μ H = referenceCorrector μ (G - H) := by
    apply ContinuousLinearMap.ext
    intro f
    simp only [referenceCorrector, ContinuousLinearMap.comp_apply, sub_apply, map_sub,
      ContinuousLinearMap.adjoint]
  rw [he]
  exact referenceCorrector_norm_le μ (G - H)

/-- A strong gradient derivative gives the correct scalar derivative for a fixed phase test. -/
theorem hasDerivAt_referenceCorrector_pairing
    (G B : ℝ → Lp ℝ 2 μ →L[ℝ] Lp E 2 μ) (t : ℝ)
    (hd : ∀ g, HasDerivAt (fun s => G s g) (B t g) t)
    (f g : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    HasDerivAt (fun s => inner ℝ f (referenceCorrector μ (G s) g))
      (inner ℝ (B t (gaussianAverage μ f)) (gaussianMomentumAdjoint μ g)) t := by
  simp_rw [referenceCorrector_pairing]
  simpa only [inner_zero_right, zero_add] using
    (hd (gaussianAverage μ f)).inner ℝ (hasDerivAt_const t (gaussianMomentumAdjoint μ g))

set_option maxHeartbeats 800000 in
/-- The quadratic corrector term along a differentiable phase curve.
This uses strong differentiation of the original gradient inverse and norm
continuity, and does not assume strong differentiation of the adjoint. -/
theorem hasDerivAt_referenceCorrector_quadratic
    (G B : ℝ → Lp ℝ 2 μ →L[ℝ] Lp E 2 μ) (t : ℝ)
    (hcont : ContinuousAt G t)
    (hd : ∀ g, HasDerivAt (fun s => G s g) (B t g) t)
    (f : ℝ → Lp ℝ 2 (gaussianPhaseMeasure μ)) (f' : Lp ℝ 2 (gaussianPhaseMeasure μ))
    (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => inner ℝ (f s) (referenceCorrector μ (G s) (f s)))
      (inner ℝ f' (referenceCorrector μ (G t) (f t)) +
        inner ℝ (f t) (referenceCorrector μ (G t) f') +
        inner ℝ (B t (gaussianAverage μ (f t))) (gaussianMomentumAdjoint μ (f t))) t := by
  have hfi := (gaussianAverage μ).hasFDerivAt.comp_hasDerivAt t hf
  have hfj := (gaussianMomentumAdjoint μ).hasFDerivAt.comp_hasDerivAt t hf
  have hgf := Analysis.Poisson.hasDerivAt_strong_apply G
    (fun s => gaussianAverage μ (f s)) t (gaussianAverage μ f')
    (B t (gaussianAverage μ (f t))) hcont hfi (hd (gaussianAverage μ (f t)))
  have h := hgf.inner ℝ hfj
  simp only [referenceCorrector_pairing]
  convert h using 1 <;> first | rfl | (simp only [inner_add_left, Function.comp_apply]; ring)

/-- The material scalar pairing has the same sharp bound as the gradient derivative. -/
theorem referenceCorrector_material_pairing_bound
    (B : Lp ℝ 2 μ →L[ℝ] Lp E 2 μ) (f g : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    |inner ℝ (B (gaussianAverage μ f)) (gaussianMomentumAdjoint μ g)| ≤
      ‖B‖ * ‖f‖ * ‖g‖ := by
  have hf : ‖gaussianAverage μ f‖ ≤ ‖f‖ :=
    ((gaussianAverage μ).le_opNorm f).trans
      (by simpa using mul_le_mul_of_nonneg_right (gaussianAverage_norm_le μ) (norm_nonneg f))
  have hg : ‖gaussianMomentumAdjoint μ g‖ ≤ ‖g‖ :=
    ((gaussianMomentumAdjoint μ).le_opNorm g).trans
      (by simpa using mul_le_mul_of_nonneg_right (gaussianMomentumAdjoint_norm_le μ) (norm_nonneg g))
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul ((B.le_opNorm _).trans (mul_le_mul_of_nonneg_left hf (norm_nonneg B)))
      hg (norm_nonneg _) (mul_nonneg (norm_nonneg B) (norm_nonneg f)))

/-- The material term has the exact macroscopic/microscopic factors from the
moving-current estimate. -/
theorem referenceCorrector_material_macro_micro_bound
    (B : Lp ℝ 2 μ →L[ℝ] Lp E 2 μ) (f g : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    |inner ℝ (B (gaussianAverage μ f)) (gaussianMomentumAdjoint μ g)| ≤
      ‖B‖ * ‖gaussianPositionProjection μ f‖ * ‖g - gaussianPositionProjection μ g‖ := by
  have hf : ‖gaussianAverage μ f‖ = ‖gaussianPositionProjection μ f‖ := by
    change ‖gaussianAverage μ f‖ = ‖positionEmbedding μ (gaussianAverage μ f)‖
    rw [(positionEmbedding μ).norm_map]
  have he : gaussianMomentumAdjoint μ (g - gaussianPositionProjection μ g) =
      gaussianMomentumAdjoint μ g := by
    rw [map_sub]
    change gaussianMomentumAdjoint μ g -
      gaussianMomentumAdjoint μ (positionEmbedding μ (gaussianAverage μ g)) = _
    rw [gaussianMomentumAdjoint_positionEmbedding, sub_zero]
  have hg : ‖gaussianMomentumAdjoint μ g‖ ≤ ‖g - gaussianPositionProjection μ g‖ := by
    rw [← he]
    exact ((gaussianMomentumAdjoint μ).le_opNorm _).trans
      (by simpa using (mul_le_mul_of_nonneg_right (gaussianMomentumAdjoint_norm_le μ)
          (norm_nonneg (g - gaussianPositionProjection μ g))))
  apply (abs_real_inner_le_norm _ _).trans
  apply mul_le_mul _ hg (norm_nonneg _) (mul_nonneg (norm_nonneg B) (norm_nonneg _))
  simpa only [hf] using B.le_opNorm (gaussianAverage μ f)

/-- The integrated corrector estimate follows from the actual strong gradient derivative. -/
theorem referenceCorrector_norm_sub_le_integral
    (G B : ℝ → Lp ℝ 2 μ →L[ℝ] Lp E 2 μ) (C : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hcont : ∀ g, ContinuousOn (fun t => G t g) (Icc a b))
    (hderiv : ∀ g t, t ∈ Ioo a b → HasDerivAt (fun s => G s g) (B t g) t)
    (hbound : ∀ t ∈ Ioo a b, ‖B t‖ ≤ C t)
    (hC : ∀ t ∈ Icc a b, 0 ≤ C t) (hCi : IntervalIntegrable C volume a b) :
    ‖referenceCorrector μ (G b) - referenceCorrector μ (G a)‖ ≤ ∫ t in a..b, C t :=
  (referenceCorrector_norm_sub_le μ (G b) (G a)).trans
    (Analysis.Poisson.norm_sub_le_integral_of_strong_derivative G B C hab hcont hderiv hbound hC hCi)

end AcceleratedLogConcave.Kinetic
