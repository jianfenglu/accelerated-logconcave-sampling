import AcceleratedLogConcave.Kinetic.GaussianEmbedding

/-! The actual visible heat marginal and its composition isometry. The input
retains its hidden Gaussian coordinate; no independence of an input density is
assumed. The density operator is the ordinary L2 adjoint. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating

section Geometry
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Exact loss under the adjoint of an isometric observation pullback. -/
theorem isometry_adjoint_loss (B : K →ₗᵢ[ℝ] H) (f : H) :
    ‖f‖ ^ 2 - ‖B.toContinuousLinearMap.adjoint f‖ ^ 2 =
      ‖f - B (B.toContinuousLinearMap.adjoint f)‖ ^ 2 := by
  have hi := B.toContinuousLinearMap.adjoint_inner_left (B.toContinuousLinearMap.adjoint f) f
  change inner ℝ (B.toContinuousLinearMap.adjoint f) (B.toContinuousLinearMap.adjoint f) =
    inner ℝ f (B (B.toContinuousLinearMap.adjoint f)) at hi
  rw [norm_sub_sq_real, B.norm_map, ← hi, real_inner_self_eq_norm_sq]
  ring

/-- The observation projection is an actual orthogonal projection. -/
theorem isometry_observation_idempotent (B : K →ₗᵢ[ℝ] H) (f : H) :
    B (B.toContinuousLinearMap.adjoint (B (B.toContinuousLinearMap.adjoint f))) =
      B (B.toContinuousLinearMap.adjoint f) := by
  have h := congrArg (fun T : K →L[ℝ] K => T (B.toContinuousLinearMap.adjoint f)) B.adjoint_comp_self
  exact congrArg B h
end Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual Gaussian convolution marginal, defined by the independent draw. -/
def heatedLaw (μ : Measure E) (t : ℝ) : Measure E :=
  (μ.prod (stdGaussian E)).map (fun z => z.1 + Real.sqrt t • z.2)

instance heatedLaw_probability (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ) :
    IsProbabilityMeasure (heatedLaw μ t) := by
  unfold heatedLaw
  exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance

/-- The deterministic last stage of correlated reheating. -/
def heatObservation (t : ℝ) (z : GaussianPhase E) : E × E :=
  (z.1.1 + Real.sqrt t • z.2, z.1.2)

theorem heatObservation_measurePreserving (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ) :
    MeasurePreserving (heatObservation t) (gaussianPhaseMeasure μ)
      ((heatedLaw μ t).prod (stdGaussian E)) := by
  have ha := measurePreserving_prodAssoc μ (stdGaussian E) (stdGaussian E)
  have hb := (MeasurePreserving.id μ).prod
    (Measure.measurePreserving_swap (μ := stdGaussian E) (ν := stdGaussian E))
  have hc := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc μ (stdGaussian E) (stdGaussian E))
  have hs : MeasurePreserving (fun z : GaussianPhase E => ((z.1.1, z.2), z.1.2))
      (gaussianPhaseMeasure μ) ((μ.prod (stdGaussian E)).prod (stdGaussian E)) :=
    hc.comp (hb.comp ha)
  have hd : MeasurePreserving (fun z : E × E => z.1 + Real.sqrt t • z.2)
      (μ.prod (stdGaussian E)) (heatedLaw μ t) :=
    (by fun_prop : Measurable (fun z : E × E => z.1 + Real.sqrt t • z.2)).measurePreserving _
  exact (hd.prod (MeasurePreserving.id (stdGaussian E))).comp hs

/-- Actual isometric pullback of output test functions. -/
def heatPullback (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ) :
    Lp ℝ 2 ((heatedLaw μ t).prod (stdGaussian E)) →ₗᵢ[ℝ] Lp ℝ 2 (gaussianPhaseMeasure μ) :=
  Lp.compMeasurePreservingₗᵢ ℝ (heatObservation t) (heatObservation_measurePreserving μ t)

theorem heatPullback_coe (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ)
    (φ : Lp ℝ 2 ((heatedLaw μ t).prod (stdGaussian E))) :
    heatPullback μ t φ =ᵐ[gaussianPhaseMeasure μ] fun z => φ (heatObservation t z) :=
  Lp.coeFn_compMeasurePreserving _ _

/-- Actual density pushforward; this is the ordinary L2 adjoint. -/
def heatDensity (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ) :
    Lp ℝ 2 (gaussianPhaseMeasure μ) →L[ℝ] Lp ℝ 2 ((heatedLaw μ t).prod (stdGaussian E)) :=
  (heatPullback μ t).toContinuousLinearMap.adjoint

/-- The true squared-L2 loss is the squared orthogonal residual. -/
theorem heatDensity_loss (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ)
    (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    ‖f‖ ^ 2 - ‖heatDensity μ t f‖ ^ 2 =
      ‖f - heatPullback μ t (heatDensity μ t f)‖ ^ 2 :=
  isometry_adjoint_loss (heatPullback μ t) f

theorem heatDensity_norm_le (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ) :
    ‖heatDensity μ t‖ ≤ 1 := by
  rw [heatDensity, ContinuousLinearMap.adjoint.norm_map]
  exact (heatPullback μ t).norm_toContinuousLinearMap_le

/-- The density operator agrees with the physical heat observation in every
L2 test pairing. This applies also when f depends on the retained hidden input. -/
theorem heatDensity_pairing (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ)
    (f : Lp ℝ 2 (gaussianPhaseMeasure μ))
    (φ : Lp ℝ 2 ((heatedLaw μ t).prod (stdGaussian E))) :
    inner ℝ (heatDensity μ t f) φ =
      ∫ z, f z * φ (heatObservation t z) ∂gaussianPhaseMeasure μ := by
  rw [heatDensity, ContinuousLinearMap.adjoint_inner_left, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [heatPullback_coe μ t φ] with z hz
  change inner ℝ (f z) ((heatPullback μ t φ) z) = _
  rw [hz]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

end AcceleratedLogConcave.Kinetic.Reheating
