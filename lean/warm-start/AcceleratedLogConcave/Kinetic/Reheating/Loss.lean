import AcceleratedLogConcave.Kinetic.Reheating.OUProduct

/-! Actual correlated reheating and its norm losses. The old hidden variable may
be coupled arbitrarily to the visible variables through the supplied L2 density. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating

/-- OU time corresponding to the source correlation squared `n² = 3/4`. -/
def hiddenOuTime : ℝ := Real.log (4 / 3) / 2

theorem hiddenOuTime_nonneg : 0 ≤ hiddenOuTime := by
  exact div_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)

theorem hiddenOuTime_decay : Real.exp (-2 * hiddenOuTime) = 3 / 4 := by
  rw [show -2 * hiddenOuTime = -Real.log (4/3) by unfold hiddenOuTime; ring,
    Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4/3)]
  norm_num

/-- The source uses exactly `n = sqrt(3)/2`. -/
theorem hiddenOuTime_correlation : Real.exp (-hiddenOuTime) = Real.sqrt 3 / 2 := by
  have hp : (Real.exp (-hiddenOuTime))^2 = (3/4 : ℝ) := by
    rw [pow_two, ← Real.exp_add]
    convert hiddenOuTime_decay using 1
    congr 1
    ring
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hpos := Real.exp_pos (-hiddenOuTime)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  nlinarith

/-- The fresh-noise coefficient is exactly `s = 1/2`. -/
theorem hiddenOuTime_noise : Real.sqrt (1-Real.exp (-2*hiddenOuTime)) = 1/2 := by
  rw [hiddenOuTime_decay]
  apply (Real.sqrt_eq_iff_eq_sq (by norm_num : (0 : ℝ) ≤ 1-3/4) (by norm_num : (0 : ℝ) ≤ 1/2)).2
  norm_num

section Geometry
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- The orthogonal residual of an actual observation is a contraction. -/
theorem isometry_residual_sq_le (B : K →ₗᵢ[ℝ] H) (f : H) :
    ‖f - B (B.toContinuousLinearMap.adjoint f)‖^2 ≤ ‖f‖^2 := by
  rw [← isometry_adjoint_loss]
  exact sub_le_self _ (sq_nonneg _)

/-- A useful loss comparison for the two actual observation residuals. -/
theorem isometry_residual_sub_sq_le (B : K →ₗᵢ[ℝ] H) (f w : H) :
    ‖(f-w) - B (B.toContinuousLinearMap.adjoint (f-w))‖^2 ≤
      2 * ‖f - B (B.toContinuousLinearMap.adjoint f)‖^2 + 2 * ‖w‖^2 := by
  let r := f - B (B.toContinuousLinearMap.adjoint f)
  let s := w - B (B.toContinuousLinearMap.adjoint w)
  have he : (f-w) - B (B.toContinuousLinearMap.adjoint (f-w)) = r-s := by
    simp only [map_sub, r, s]
    abel
  rw [he]
  have hp := sq_nonneg ‖r+s‖
  rw [norm_add_sq_real] at hp
  have hs := isometry_residual_sq_le B w
  change ‖s‖^2 ≤ ‖w‖^2 at hs
  rw [norm_sub_sq_real]
  nlinarith
end Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsProbabilityMeasure μ]

/-- Conditional average over the old hidden Gaussian, retaining `(x,p)`. -/
def hiddenAverage : Lp ℝ 2 (gaussianPhaseMeasure μ) →L[ℝ]
    Lp ℝ 2 (μ.prod (stdGaussian E)) := productAverage _ _

/-- The visible-coordinate embedding into the actual phase reference. -/
def hiddenEmbedding : Lp ℝ 2 (μ.prod (stdGaussian E)) →ₗᵢ[ℝ]
    Lp ℝ 2 (gaussianPhaseMeasure μ) := productEmbedding _ _

/-- Hidden OU acting on the actual phase reference. -/
def hiddenOU : Lp ℝ 2 (gaussianPhaseMeasure μ) →L[ℝ]
    Lp ℝ 2 (gaussianPhaseMeasure μ) :=
  ouProduct (μ.prod (stdGaussian E)) hiddenOuTime hiddenOuTime_nonneg

/-- The actual correlated reheating density operator. -/
def reheatingDensity (t : ℝ) : Lp ℝ 2 (gaussianPhaseMeasure μ) →L[ℝ]
    Lp ℝ 2 ((heatedLaw μ t).prod (stdGaussian E)) :=
  (heatDensity μ t).comp (hiddenOU μ)

/-- Correlated reheating is L2 contractive. -/
theorem reheatingDensity_norm_le (t : ℝ) : ‖reheatingDensity μ t‖ ≤ 1 := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul (heatDensity_norm_le μ t)
      (ouProduct_norm_le (μ.prod (stdGaussian E)) hiddenOuTime hiddenOuTime_nonneg)
      (norm_nonneg _) zero_le_one).trans (by norm_num))

/-- The exact loss is OU loss plus the genuine observation-projection residual. -/
theorem reheating_loss_eq (t : ℝ) (F : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    ‖F‖^2 - ‖reheatingDensity μ t F‖^2 =
      (‖F‖^2 - ‖hiddenOU μ F‖^2) +
      ‖hiddenOU μ F -
        heatPullback μ t (reheatingDensity μ t F)‖^2 := by
  have h := heatDensity_loss μ t
    (hiddenOU μ F)
  change ‖hiddenOU μ F‖^2 -
    ‖reheatingDensity μ t F‖^2 =
    ‖hiddenOU μ F - heatPullback μ t (reheatingDensity μ t F)‖^2 at h
  rw [← h]
  ring

/-- Actual reheating pays at least `s²=1/4` of every hidden centered direction. -/
theorem reheating_hidden_loss (t : ℝ) (F : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    (1/4 : ℝ) * ‖F - hiddenEmbedding μ
      (hiddenAverage μ F)‖^2 ≤ ‖F‖^2 - ‖reheatingDensity μ t F‖^2 := by
  have h := ouProduct_loss (μ.prod (stdGaussian E)) hiddenOuTime hiddenOuTime_nonneg F
  rw [hiddenOuTime_decay] at h
  norm_num at h
  change (1/4 : ℝ) * ‖F - hiddenEmbedding μ (hiddenAverage μ F)‖^2 ≤
    ‖F‖^2 - ‖hiddenOU μ F‖^2 at h
  rw [reheating_loss_eq]
  change (1/4 : ℝ) * ‖F - hiddenEmbedding μ
    (hiddenAverage μ F)‖^2 ≤ _
  nlinarith [sq_nonneg ‖hiddenOU μ F -
    heatPullback μ t (reheatingDensity μ t F)‖]

/-- The hidden-centered component after the actual OU stage. -/
def reheatingHiddenPart (F : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    Lp ℝ 2 (gaussianPhaseMeasure μ) :=
  hiddenOU μ
    (F - hiddenEmbedding μ (hiddenAverage μ F))

/-- The actual ordinary-heat loss is bounded by eight times the correlated loss. -/
theorem reheating_ordinary_loss_le (t : ℝ) (F : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    let g := hiddenEmbedding μ (hiddenAverage μ F)
    ‖g‖^2 - ‖heatDensity μ t g‖^2 ≤
      8 * (‖F‖^2 - ‖reheatingDensity μ t F‖^2) := by
  let I := hiddenEmbedding μ
  let A := hiddenAverage μ
  let O := hiddenOU μ
  let g := I (A F)
  let z := F-g
  let w := O z
  have hAz : A z = 0 := by
    change A (F - I (A F)) = 0
    rw [map_sub]
    have ha : A (I (A F)) = A F := productAverage_embedding _ _ _
    rw [ha, sub_self]
  have hw : ‖w‖^2 ≤ (3/4 : ℝ)*‖z‖^2 := by
    have h := ouProduct_variance (μ.prod (stdGaussian E)) hiddenOuTime hiddenOuTime_nonneg z
    change ‖w‖^2 - ‖A z‖^2 ≤ Real.exp (-2*hiddenOuTime)*(‖z‖^2-‖A z‖^2) at h
    rw [hAz, hiddenOuTime_decay] at h
    simpa only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      sub_zero] using h
  have hAg : A (O F) = A F := productAverage_ouProduct _ _ _ F
  have hOg : O g = g := ouProduct_embedding _ _ _ _
  have hw' : w = O F - g := by simp only [w, z, map_sub, hOg]
  have hs1 := isometry_adjoint_loss I F
  have hs2 := isometry_adjoint_loss I (O F)
  change ‖F‖^2 - ‖A F‖^2 = ‖z‖^2 at hs1
  change ‖O F‖^2 - ‖A (O F)‖^2 = ‖O F-I (A (O F))‖^2 at hs2
  rw [hAg] at hs2
  change ‖O F‖^2 - ‖A F‖^2 = ‖O F-g‖^2 at hs2
  rw [← hw'] at hs2
  have hD := reheating_loss_eq μ t F
  change ‖F‖^2 - ‖reheatingDensity μ t F‖^2 =
    (‖F‖^2 - ‖O F‖^2) + ‖O F - heatPullback μ t (reheatingDensity μ t F)‖^2 at hD
  have hr := isometry_residual_sub_sq_le (heatPullback μ t) (O F) w
  have he : O F-w = g := by rw [hw']; abel
  rw [he] at hr
  change ‖g - heatPullback μ t (heatDensity μ t g)‖^2 ≤
    2*‖O F - heatPullback μ t (reheatingDensity μ t F)‖^2 + 2*‖w‖^2 at hr
  change ‖g‖^2 - ‖heatDensity μ t g‖^2 ≤ _
  rw [heatDensity_loss]
  nlinarith [sq_nonneg ‖z‖,
    sq_nonneg ‖O F - heatPullback μ t (reheatingDensity μ t F)‖]

/-- The literal random-tape map in the Gaussian reheating lemma. -/
def reheatingObservation (t : ℝ) (z : GaussianPhase E × E) : E × E :=
  (z.1.1.1 + Real.sqrt t • ((Real.sqrt 3 / 2) • z.1.2 + (1/2 : ℝ) • z.2), z.1.1.2)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem reheatingObservation_eq (t : ℝ) :
    reheatingObservation (E := E) t = heatObservation t ∘
      ouProductObservation (X := E×E) (E := E) hiddenOuTime := by
  funext z
  simp only [reheatingObservation, Function.comp_apply, heatObservation, ouProductObservation,
    gaussianMix, hiddenOuTime_correlation, hiddenOuTime_noise]

theorem reheatingObservation_measurePreserving (t : ℝ) :
    MeasurePreserving (reheatingObservation (E := E) t)
      ((gaussianPhaseMeasure μ).prod (stdGaussian E)) ((heatedLaw μ t).prod (stdGaussian E)) := by
  rw [reheatingObservation_eq]
  exact (heatObservation_measurePreserving μ t).comp
    (ouProductObservation_measurePreserving (μ.prod (stdGaussian E)) hiddenOuTime hiddenOuTime_nonneg)

/-- The factorized density operator is the ordinary L2 adjoint of the actual
random-tape channel with the manuscript's exact coefficients. -/
theorem reheatingDensity_eq_referenceChannel_adjoint (t : ℝ) :
    reheatingDensity μ t = (referenceChannel
      (measurePreserving_fst (μ := gaussianPhaseMeasure μ) (ν := stdGaussian E))
      (reheatingObservation_measurePreserving μ t)).adjoint := by
  apply ContinuousLinearMap.ext
  intro F
  apply ext_inner_right ℝ
  intro φ
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℝ (heatDensity μ t (hiddenOU μ F)) φ = _
  rw [heatDensity, ContinuousLinearMap.adjoint_inner_left]
  have hs := ouProduct_symmetric (μ.prod (stdGaussian E)) hiddenOuTime hiddenOuTime_nonneg
    F (heatPullback μ t φ)
  change inner ℝ F (hiddenOU μ (heatPullback μ t φ)) =
    inner ℝ (hiddenOU μ F) (heatPullback μ t φ) at hs
  change inner ℝ (hiddenOU μ F) (heatPullback μ t φ) = _
  rw [← hs]
  have hp := referenceChannel_pairing
    (measurePreserving_fst (μ := gaussianPhaseMeasure μ) (ν := stdGaussian E))
    (ouProductObservation_measurePreserving (μ.prod (stdGaussian E)) hiddenOuTime hiddenOuTime_nonneg)
    F (heatPullback μ t φ)
  change inner ℝ F (hiddenOU μ (heatPullback μ t φ)) = _ at hp
  rw [hp, referenceChannel_pairing]
  apply integral_congr_ae
  have hae := (ouProductObservation_measurePreserving (μ.prod (stdGaussian E)) hiddenOuTime
    hiddenOuTime_nonneg).quasiMeasurePreserving.ae (heatPullback_coe μ t φ)
  filter_upwards [hae] with z hz
  change F z.1 * (heatPullback μ t φ)
    (ouProductObservation hiddenOuTime z) = F z.1 * φ (reheatingObservation t z)
  rw [hz, reheatingObservation_eq]
  rfl

end AcceleratedLogConcave.Kinetic.Reheating
