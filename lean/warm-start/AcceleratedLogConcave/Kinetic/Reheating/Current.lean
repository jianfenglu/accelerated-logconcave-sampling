import AcceleratedLogConcave.Kinetic.Reheating.Corrector
import AcceleratedLogConcave.Kinetic.Reheating.EnergyAlgebra

/-! Correlated reheating current and energy algebra for the actual operators.
The `_of_ordinary_current` lemmas are intermediate: they explicitly expose the
ordinary heat-current obligation that the physical heat evolution must discharge. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace ContDiff
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [IsProbabilityMeasure μ]

/-- The genuine phase corrector uses only the hidden-coordinate average. -/
theorem gaussianCorrector_hiddenAverage
    (V : E → ℝ) (hV : ContDiff ℝ 2 V) (hI : Integrable (fun x => Real.exp (-V x)))
    (hμ : μ = volume.tilted (fun x => -V x))
    (m L : ℝ) (hm : 0 < m)
    (hl : ∀ x a, m*‖a‖^2 ≤ fderiv ℝ (fderiv ℝ V) x a a)
    (hu : ∀ x a, fderiv ℝ (fderiv ℝ V) x a a ≤ L*‖a‖^2)
    (F : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    gaussianCorrector μ V hV hI hμ m L hm hl hu F =
      Kinetic.hiddenEmbedding μ (visibleCorrector μ V hV hI hμ m L hm hl hu (hiddenAverage μ F)) := by
  have hj : gaussianMomentumAdjoint μ F =
      (momentumEmbedding μ).toContinuousLinearMap.adjoint (hiddenAverage μ F) := by
    apply ext_inner_left ℝ
    intro G
    rw [gaussianMomentumAdjoint, ContinuousLinearMap.adjoint_inner_right,
      ContinuousLinearMap.adjoint_inner_right]
    change inner ℝ (Kinetic.hiddenEmbedding μ (momentumEmbedding μ G)) F =
      inner ℝ (momentumEmbedding μ G) ((Kinetic.hiddenEmbedding μ).toContinuousLinearMap.adjoint F)
    exact ((Kinetic.hiddenEmbedding μ).toContinuousLinearMap.adjoint_inner_right _ _).symm
  rw [gaussianCorrector_apply, hj]
  rfl

/-- Hidden averaging preserves precisely the input corrector quadratic. -/
theorem gaussianCorrector_current_hiddenAverage
    (V : E → ℝ) (hV : ContDiff ℝ 2 V) (hI : Integrable (fun x => Real.exp (-V x)))
    (hμ : μ = volume.tilted (fun x => -V x))
    (m L : ℝ) (hm : 0 < m)
    (hl : ∀ x a, m*‖a‖^2 ≤ fderiv ℝ (fderiv ℝ V) x a a)
    (hu : ∀ x a, fderiv ℝ (fderiv ℝ V) x a a ≤ L*‖a‖^2)
    (F : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    inner ℝ (gaussianCorrector μ V hV hI hμ m L hm hl hu F) F =
      inner ℝ (visibleCorrector μ V hV hI hμ m L hm hl hu (hiddenAverage μ F)) (hiddenAverage μ F) := by
  rw [gaussianCorrector_hiddenAverage]
  exact ((Kinetic.hiddenEmbedding μ).toContinuousLinearMap.adjoint_inner_right _ _).symm

/-- The actual OU hidden perturbation remains centered and its squared norm is
at most three times the true correlated reheating loss. -/
theorem reheatingHiddenPart_properties (t : ℝ) (F : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    hiddenAverage μ (reheatingHiddenPart μ F) = 0 ∧
    ‖reheatingHiddenPart μ F‖^2 ≤ 3*(‖F‖^2-‖reheatingDensity μ t F‖^2) ∧
    reheatingDensity μ t F = heatDensity μ t (hiddenEmbedding μ (hiddenAverage μ F)) +
      heatDensity μ t (reheatingHiddenPart μ F) := by
  let z := F-hiddenEmbedding μ (hiddenAverage μ F)
  have hz : hiddenAverage μ z = 0 := by
    change hiddenAverage μ (F-hiddenEmbedding μ (hiddenAverage μ F)) = 0
    rw [map_sub]
    have he : hiddenAverage μ (hiddenEmbedding μ (hiddenAverage μ F)) = hiddenAverage μ F :=
      productAverage_embedding _ _ _
    rw [he, sub_self]
  have ha : hiddenAverage μ (reheatingHiddenPart μ F) = hiddenAverage μ z :=
    productAverage_ouProduct _ _ _ z
  have hw := ouProduct_variance (μ.prod (stdGaussian E)) hiddenOuTime hiddenOuTime_nonneg z
  change ‖reheatingHiddenPart μ F‖^2 - ‖hiddenAverage μ z‖^2 ≤
    Real.exp (-2*hiddenOuTime)*(‖z‖^2-‖hiddenAverage μ z‖^2) at hw
  rw [hz, hiddenOuTime_decay] at hw
  have hl := reheating_hidden_loss μ t F
  change (1/4:ℝ)*‖z‖^2 ≤ _ at hl
  refine ⟨ha.trans hz, by simp only [norm_zero, zero_pow (by norm_num : 2≠0), sub_zero] at hw; linarith, ?_⟩
  have hg : hiddenOU μ (hiddenEmbedding μ (hiddenAverage μ F)) =
      hiddenEmbedding μ (hiddenAverage μ F) := ouProduct_embedding _ _ _ _
  change heatDensity μ t (hiddenOU μ F) = _
  rw [← map_add]
  congr 1
  change hiddenOU μ F = hiddenEmbedding μ (hiddenAverage μ F) +
    hiddenOU μ (F-hiddenEmbedding μ (hiddenAverage μ F))
  rw [map_sub, hg]
  abel

variable (t : ℝ) (ht : 0 ≤ t)
  (V₀ Vₜ : E → ℝ) (hV₀ : ContDiff ℝ 2 V₀) (hVₜ : ContDiff ℝ 2 Vₜ)
  (hI₀ : Integrable (fun x => Real.exp (-V₀ x))) (hIₜ : Integrable (fun x => Real.exp (-Vₜ x)))
  (hμ₀ : μ = volume.tilted (fun x => -V₀ x))
  (hμₜ : heatedLaw μ t = volume.tilted (fun x => -Vₜ x))
  (m₀ mₜ L : ℝ) (hm₀ : 0 < m₀) (hmₜ : 0 < mₜ)
  (hl₀ : ∀ x a, m₀*‖a‖^2 ≤ fderiv ℝ (fderiv ℝ V₀) x a a)
  (hu₀ : ∀ x a, fderiv ℝ (fderiv ℝ V₀) x a a ≤ L*‖a‖^2)
  (hlₜ : ∀ x a, mₜ*‖a‖^2 ≤ fderiv ℝ (fderiv ℝ Vₜ) x a a)
  (huₜ : ∀ x a, fderiv ℝ (fderiv ℝ Vₜ) x a a ≤ L*‖a‖^2)
include ht

/-- The complete correlated-current reduction, with only ordinary heat current
left explicit. All hidden Gaussian losses and corrector residuals are proved. -/
theorem reheating_current_le_of_ordinary_current
    (hcurrent : ∀ g : Lp ℝ 2 (μ.prod (stdGaussian E)),
      let v₀ := heatDensity μ t (hiddenEmbedding μ g)
      |inner ℝ (visibleCorrector (heatedLaw μ t) Vₜ hVₜ hIₜ hμₜ mₜ L hmₜ hlₜ huₜ v₀) v₀ -
        inner ℝ (visibleCorrector μ V₀ hV₀ hI₀ hμ₀ m₀ L hm₀ hl₀ hu₀ g) g| ≤
      (t/4)*‖g‖^2+Real.sqrt (t*(‖g‖^2-‖v₀‖^2))*‖g‖)
    (F : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    let v := reheatingDensity μ t F
    let D := ‖F‖^2-‖v‖^2
    |inner ℝ (visibleCorrector (heatedLaw μ t) Vₜ hVₜ hIₜ hμₜ mₜ L hmₜ hlₜ huₜ v) v -
      inner ℝ (gaussianCorrector μ V₀ hV₀ hI₀ hμ₀ m₀ L hm₀ hl₀ hu₀ F) F| ≤
      (t/4)*‖F‖^2+7*Real.sqrt (t*D)*‖F‖+3*Real.sqrt t*D := by
  let g := hiddenAverage μ F
  let v₀ := heatDensity μ t (hiddenEmbedding μ g)
  let w := reheatingHiddenPart μ F
  let A := visibleCorrector (heatedLaw μ t) Vₜ hVₜ hIₜ hμₜ mₜ L hmₜ hlₜ huₜ
  let D := ‖F‖^2-‖reheatingDensity μ t F‖^2
  have hproperties := reheatingHiddenPart_properties μ t F
  have hb := centered_observation_current_bound (hiddenEmbedding μ) (heatPullback μ t)
    A (Real.sqrt t) (Real.sqrt_nonneg t)
    (fun x => phaseHeatCentered_visibleCorrector_norm Vₜ hVₜ hIₜ mₜ L hmₜ hlₜ huₜ μ t ht hμₜ x)
    (fun x => phaseHeatCentered_visibleCorrector_adjoint_norm Vₜ hVₜ hIₜ mₜ L hmₜ hlₜ huₜ μ t ht hμₜ x)
    w hproperties.1 v₀
  have hG : ‖g‖ ≤ ‖F‖ := by
    have hnorm : ‖hiddenAverage μ‖ ≤ 1 := productAverage_norm_le (μ.prod (stdGaussian E)) (stdGaussian E)
    have hh := ContinuousLinearMap.le_of_opNorm_le (hiddenAverage μ) hnorm F
    simpa only [one_mul] using hh
  have hv : ‖v₀‖ ≤ ‖g‖ := by
    have hh := ContinuousLinearMap.le_of_opNorm_le _ (heatDensity_norm_le μ t) (hiddenEmbedding μ g)
    simpa only [one_mul, (hiddenEmbedding μ).norm_map] using hh
  have hD : 0 ≤ D := by
    have hn := ContinuousLinearMap.le_of_opNorm_le _ (reheatingDensity_norm_le μ t) F
    simp only [one_mul] at hn
    dsimp [D]
    nlinarith [norm_nonneg F, norm_nonneg (reheatingDensity μ t F)]
  have hDg : 0 ≤ ‖g‖^2-‖v₀‖^2 := by nlinarith [norm_nonneg g, norm_nonneg v₀]
  have hloss : ‖g‖^2-‖v₀‖^2 ≤ 8*D := by
    simpa only [(hiddenEmbedding μ).norm_map] using reheating_ordinary_loss_le μ t F
  have hc := hcurrent g
  dsimp only at hc hb ⊢
  rw [gaussianCorrector_current_hiddenAverage]
  apply reheating_current_scalar ht hD hDg (norm_nonneg F) (norm_nonneg g) hG
    (norm_nonneg w) (norm_nonneg v₀) (hv.trans hG) hloss hproperties.2.1
  calc
    _ ≤ |inner ℝ (A (reheatingDensity μ t F)) (reheatingDensity μ t F) - inner ℝ (A v₀) v₀| +
        |inner ℝ (A v₀) v₀ - inner ℝ (visibleCorrector μ V₀ hV₀ hI₀ hμ₀ m₀ L hm₀ hl₀ hu₀ g) g| :=
      abs_sub_le _ _ _
    _ ≤ _ := by
      have he : reheatingDensity μ t F = v₀+heatDensity μ t w := hproperties.2.2
      rw [he]
      change |inner ℝ (A (v₀+(heatPullback μ t).toContinuousLinearMap.adjoint w))
        (v₀+(heatPullback μ t).toContinuousLinearMap.adjoint w) - inner ℝ (A v₀) v₀| + _ ≤ _
      linarith

/-- Source energy absorption for the actual correlated channel, conditional
only on the separately identified ordinary heat-current theorem. -/
theorem reheating_energy_le_of_ordinary_current
    (hcurrent : ∀ g : Lp ℝ 2 (μ.prod (stdGaussian E)),
      let v₀ := heatDensity μ t (hiddenEmbedding μ g)
      |inner ℝ (visibleCorrector (heatedLaw μ t) Vₜ hVₜ hIₜ hμₜ mₜ L hmₜ hlₜ huₜ v₀) v₀ -
        inner ℝ (visibleCorrector μ V₀ hV₀ hI₀ hμ₀ m₀ L hm₀ hl₀ hu₀ g) g| ≤
      (t/4)*‖g‖^2+Real.sqrt (t*(‖g‖^2-‖v₀‖^2))*‖g‖)
    (ε : ℝ) (hε : 0 ≤ ε) (hsmall : ε*Real.sqrt t ≤ 1/24)
    (F : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    quadraticEnergy (visibleCorrector (heatedLaw μ t) Vₜ hVₜ hIₜ hμₜ mₜ L hmₜ hlₜ huₜ) ε
      (reheatingDensity μ t F) ≤
    gaussianCorrectedEnergy μ V₀ hV₀ hI₀ hμ₀ m₀ L hm₀ hl₀ hu₀ ε F -
      (‖F‖^2-‖reheatingDensity μ t F‖^2)/4 + 100*(ε+ε^2)*t*‖F‖^2 := by
  have hc := reheating_current_le_of_ordinary_current μ t ht V₀ Vₜ hV₀ hVₜ hI₀ hIₜ
    hμ₀ hμₜ m₀ mₜ L hm₀ hmₜ hl₀ hu₀ hlₜ huₜ hcurrent F
  have hD : 0 ≤ ‖F‖^2-‖reheatingDensity μ t F‖^2 := by
    have hn := ContinuousLinearMap.le_of_opNorm_le _ (reheatingDensity_norm_le μ t) F
    simp only [one_mul] at hn
    nlinarith [norm_nonneg F, norm_nonneg (reheatingDensity μ t F)]
  have he := reheating_energy_scalar hε ht hD (norm_nonneg F) hsmall hc
  unfold quadraticEnergy gaussianCorrectedEnergy
  convert he using 1
  ring

end AcceleratedLogConcave.Kinetic.Reheating
