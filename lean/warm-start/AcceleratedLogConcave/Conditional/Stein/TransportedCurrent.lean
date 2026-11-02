import AcceleratedLogConcave.Conditional.Stein.Transport

/-! # Conditional-current differentiation against the actual backward test -/

noncomputable section
set_option maxHeartbeats 1600000
open Set Function MeasureTheory
open scoped Topology NNReal

namespace AcceleratedLogConcave.Conditional
open Analysis.Poisson OAI.LogConcaveSampling.GlobalODE

section TestDefinition
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
  (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
  (x : E) {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)

/-- The scalar compact test transported to the terminal interpolation time. -/
def transportedSteinTest (φ : E → ℝ) (p : ℝ × E) : ℝ :=
  φ (forwardProbabilityTransport hF hell hlo hup x hr hb hb1 p.1 p.2)

theorem contDiffAt_transportedSteinTest (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ)
    (p : ℝ × E) (hp : p.1 ∈ Ioo 0 b) :
    ContDiffAt ℝ 1 (transportedSteinTest hF hell hlo hup x hr hb hb1 φ) p := by
  let hc := clippedProbabilityVelocity_continuous hb r
    (continuousOn_conditionalMean hF hlo hup x r (by norm_num) hb1)
  let hL := fun t (_ : t ∈ Icc 0 b) => clippedProbabilityVelocity_lipschitz hb r
    (fun s hs => lipschitzWith_conditionalMean hF hell hlo hup x hr
      (by linarith [hs.1]) (hs.2.trans_lt hb1)) t
  have heq : backwardTest hb hc hL ⟨b, hb, le_rfl⟩ φ =
      transportedSteinTest hF hell hlo hup x hr hb hb1 φ := by
    funext q
    rw [backwardTest_eq]
    rfl
  rw [← heq]
  exact backwardTest_contDiffAt_one hb hc hL
    (continuous_clippedConditionalVelocityDerivative hF hlo hup x (r := r) hb hb1)
    (hasFDerivAt_clippedConditionalVelocity hF hlo hup x (r := r) hb hb1)
    ⟨b, hb, le_rfl⟩ hφ p hp

/-- Spatial chain rule for the actual transported scalar test. -/
theorem fderiv_transportedSteinTest_spatial (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ)
    {ρ : ℝ} (hρ : ρ ∈ Ioo 0 b) (y v : E) :
    fderiv ℝ (transportedSteinTest hF hell hlo hup x hr hb hb1 φ) (ρ, y) (0, v) =
      fderiv ℝ φ (forwardProbabilityTransport hF hell hlo hup x hr hb hb1 ρ y)
        (fderiv ℝ (forwardProbabilityTransport hF hell hlo hup x hr hb hb1 ρ) y v) := by
  have hj := ((contDiffAt_transportedSteinTest hF hell hlo hup x hr hb hb1 φ hφ
    (ρ, y) hρ).differentiableAt (by norm_num)).hasFDerivAt.comp y
      ((hasFDerivAt_const (𝕜 := ℝ) ρ y).prodMk (hasFDerivAt_id y))
  have hs := (hφ.differentiable_one
    (forwardProbabilityTransport hF hell hlo hup x hr hb hb1 ρ y)).hasFDerivAt.comp y
    ((contDiff_one_forwardProbabilityTransport hF hell hlo hup x hr hb hb1 ρ).differentiable_one y).hasFDerivAt
  have heq := hj.unique hs
  exact congrArg (fun D : E →L[ℝ] ℝ => D v) heq

end TestDefinition

section DensityPairing
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

private theorem continuousOn_integral_explicitDensity
    {a b : ℝ} (μ : ℝ → Measure V) (p W : ℝ → V → ℝ)
    (hp : ContinuousOn (uncurry p) (Icc a b ×ˢ (univ : Set V)))
    (hW : ContinuousOn (uncurry W) (Icc a b ×ˢ (univ : Set V)))
    (hpos : ∀ t ∈ Icc a b, ∀ y, 0 ≤ p t y)
    (hμ : ∀ t ∈ Icc a b, μ t = volume.withDensity (fun y => ENNReal.ofReal (p t y)))
    (K : Set V) (hK : IsCompact K)
    (hzero : ∀ t ∈ Icc a b, ∀ y ∉ K, W t y = 0) :
    ContinuousOn (fun t => ∫ y, W t y ∂μ t) (Icc a b) := by
  have hH := continuousOn_integral_of_common_compact_support
    (fun t y => p t y * W t y) (hp.mul hW) K hK
    (fun t ht y hy => by rw [hzero t ht y hy, mul_zero])
  apply hH.congr
  intro t ht
  change (∫ y, W t y ∂μ t) = ∫ y, p t y * W t y
  rw [hμ t ht]
  have hpc : Continuous (p t) := hp.comp_continuous
    (continuous_const.prodMk continuous_id) (fun y => ⟨ht, mem_univ y⟩)
  rw [integral_withDensity_eq_integral_toReal_smul hpc.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [ENNReal.toReal_ofReal (hpos t ht y)]
  rfl
end DensityPairing

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι
/-- The conditional-current identity with the actual transport pullback.
The material derivative of the test cancels, leaving the covariance current.
This is the derivative integrated in the transported Stein identity. -/
theorem hasDerivAt_conditionalMean_transportedTest
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
  (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
  (x : E) {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (u : E) {ρ : ℝ} (hρ : ρ ∈ Ioo 0 b)
    (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ) (hφK : HasCompactSupport φ) :
    HasDerivAt
      (fun t => ∫ y, inner ℝ u (conditionalMean F x r t y) *
        transportedSteinTest hF hell hlo hup x hr hb hb1 φ (t, y)
        ∂interpolationLaw F x r t)
      (∫ y, fderiv ℝ (transportedSteinTest hF hell hlo hup x hr hb hb1 φ) (ρ, y)
        (0, firstScaledJetRow F x u r ρ y) ∂interpolationLaw F x r ρ) ρ := by
  let v := clippedProbabilityVelocity hb r (conditionalMean F x r)
  let hc := clippedProbabilityVelocity_continuous hb r
    (continuousOn_conditionalMean hF hlo hup x r (by norm_num) hb1)
  let hL := fun t (_ : t ∈ Icc 0 b) => clippedProbabilityVelocity_lipschitz hb r
    (fun s hs => lipschitzWith_conditionalMean hF hell hlo hup x hr
      (by linarith [hs.1]) (hs.2.trans_lt hb1)) t
  let hD := continuous_clippedConditionalVelocityDerivative hF hlo hup x (r := r) hb hb1
  let hf := hasFDerivAt_clippedConditionalVelocity hF hlo hup x (r := r) hb hb1
  let T : Icc 0 b := ⟨b, hb, le_rfl⟩
  let ψ := backwardTest hb hc hL T φ
  have hψeq : ψ = transportedSteinTest hF hell hlo hup x hr hb hb1 φ := by
    funext p
    change backwardTest hb hc hL T φ p = _
    rw [backwardTest_eq]
    rfl
  have hd := hasDerivAt_weightedInterpolation_test hF hlo hup x u r
    (by norm_num : (-1 : ℝ) < 0) hb1 hρ ψ
    (backwardTest_continuous hb hc hL T hφ.continuous)
    (backwardTest_contDiffAt_one hb hc hL hD hf T hφ)
    (backwardTest_common_compact_support hb hc hL T hφK)
  have hm (y : E) : fderiv ℝ ψ (ρ, y) (1, probabilityVelocity F x r ρ y) = 0 := by
    have h := backwardTest_material_zero hb hc hL hD hf T hφ.differentiable_one (ρ, y) hρ
    simpa only [v, clippedProbabilityVelocity_eq hb r (conditionalMean F x r)
      ⟨hρ.1.le, hρ.2.le⟩, meanVelocity, probabilityVelocity] using h
  have heq : (∫ y, ∫ z, inner ℝ u (primitiveObservable F x r z) *
        fderiv ℝ ψ (ρ, y) (1, (conditionalVariance ρ)⁻¹ • (z - ρ • y))
          ∂conditionalLaw F x r ρ y ∂interpolationLaw F x r ρ) =
      ∫ y, fderiv ℝ ψ (ρ, y) (0, firstScaledJetRow F x u r ρ y)
        ∂interpolationLaw F x r ρ := by
    apply integral_congr_ae
    filter_upwards [] with y
    rw [integral_weighted_conditional_spaceTime_velocity hF hlo hup x u r
      (by linarith [hρ.1]) (hρ.2.trans hb1), hm, mul_zero, zero_add]
  rw [heq, hψeq] at hd
  exact hd

/-- Endpoint continuity of the current pairing follows from the actual
positive interpolation density and the common compact support of backward tests. -/
theorem continuousOn_conditionalMean_transportedTest
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (u : E) (φ : E → ℝ) (hφ : Continuous φ) (hφK : HasCompactSupport φ) :
    ContinuousOn (fun t => ∫ y, inner ℝ u (conditionalMean F x r t y) *
      transportedSteinTest hF hell hlo hup x hr hb hb1 φ (t, y)
        ∂interpolationLaw F x r t) (Icc 0 b) := by
  let hc := clippedProbabilityVelocity_continuous hb r
    (continuousOn_conditionalMean hF hlo hup x r (by norm_num) hb1)
  let hL := fun t (_ : t ∈ Icc 0 b) => clippedProbabilityVelocity_lipschitz hb r
    (fun s hs => lipschitzWith_conditionalMean hF hell hlo hup x hr
      (by linarith [hs.1]) (hs.2.trans_lt hb1)) t
  let T : Icc 0 b := ⟨b, hb, le_rfl⟩
  let ψ := transportedSteinTest hF hell hlo hup x hr hb hb1 φ
  have hψeq : backwardTest hb hc hL T φ = ψ := by
    funext p
    rw [backwardTest_eq]
    rfl
  have hψ : Continuous ψ := hψeq ▸ backwardTest_continuous hb hc hL T hφ
  obtain ⟨K, hK, hzero⟩ := backwardTest_common_compact_support hb hc hL T hφK
  have hp : ContinuousOn (fun p : ℝ × E => interpolationDensity F x r p.1 p.2)
      (Icc 0 b ×ˢ (univ : Set E)) :=
    (contDiffOn_interpolationDensity hF hlo x r).continuousOn.mono
      (fun p hp => ⟨by linarith [hp.1.1], hp.1.2.trans_lt hb1⟩)
  have hm := continuousOn_conditionalMean hF hlo hup x r (by norm_num : (-1 : ℝ) < 0) hb1
  apply continuousOn_integral_explicitDensity (interpolationLaw F x r)
    (interpolationDensity F x r) (fun t y => inner ℝ u (conditionalMean F x r t y) * ψ (t, y))
    hp (((continuousOn_const (c := u)).inner hm).mul hψ.continuousOn)
  · intro t ht y
    exact (interpolationDensity_pos hF hlo x r t
      (conditionalVariance_pos (by linarith [ht.1]) (ht.2.trans_lt hb1)) y).le
  · intro t ht
    exact interpolationLaw_eq_explicitDensity hF hlo x r t
      (conditionalVariance_pos (by linarith [ht.1]) (ht.2.trans_lt hb1))
  · exact hK
  · intro t _ y hy
    rw [show ψ (t, y) = 0 by rw [← hψeq]; exact hzero t y hy, mul_zero]

end AcceleratedLogConcave.Conditional
