import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.PhasePairing
import AcceleratedLogConcave.Kinetic.ReferenceCorrector

/-! The two actual generator--corrector bounds required for the heat current.
The position bound uses the Poisson graph; the adjoint bound uses weak Bochner rows. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson Analysis.WeightedGradient
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The actual visible weighted Poisson corrector at a physical time. -/
def phaseVisibleCorrector {a b : ℝ} (F : ReferencePoissonFamily E a b)
    (t : ℝ) (ht : t ∈ Icc a b) :
    Lp ℝ 2 ((F.law t).prod (stdGaussian E)) →L[ℝ] Lp ℝ 2 ((F.law t).prod (stdGaussian E)) :=
  visibleCorrector (F.law t) (F.potential t) (F.potential_C2 t) (F.integrable t ht)
    (F.gibbs_law t ht) (F.lower t) 1 (F.lower_pos t ht) (F.hessian_lower t ht)
    (by simpa only [one_mul] using F.hessian_upper t ht)

/-- Actual position-gradient contraction bounds the first heat-current pairing. -/
theorem phaseHeat_corrector_pairing_bound {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
    (t : ℝ) (ht : t ∈ Icc a b) (v : Lp ℝ 2 ((F.law t).prod (stdGaussian E))) :
    |inner ℝ (phaseHeatGeneratorLp F hf hc hheat t ht) (phaseVisibleCorrector F t ht v)| ≤
      ‖phaseHeatGradientLp F hf hc hheat t ht‖ * ‖v‖ := by
  have hupper : ∀ x w, fderiv ℝ (fderiv ℝ (F.potential t)) x w w ≤ 1*‖w‖^2 := by
    simpa only [one_mul] using F.hessian_upper t ht
  have hg := gaussianCorrectorPositionGradient_graph (F.law t) (F.potential t) (F.potential_C2 t)
    (F.integrable t ht) (F.gibbs_law t ht) (F.lower t) 1 (F.lower_pos t ht)
    (F.hessian_lower t ht) hupper (Kinetic.hiddenEmbedding (F.law t) v)
  obtain ⟨u,hu,hDu⟩ := (LinearPMap.mem_graph_iff _).mp hg
  have hu' : productEmbedding (F.law t) (stdGaussian E) (u : Lp ℝ 2 (F.law t)) =
      phaseVisibleCorrector F t ht v := by
    rw [hu]
    change productEmbedding (F.law t) (stdGaussian E)
      (vectorPoissonInverse (F.law t) (F.potential t) (F.potential_C2 t)
        (F.integrable t ht) (F.gibbs_law t ht) (F.lower t) 1 (F.lower_pos t ht)
        (F.hessian_lower t ht) hupper
        (gaussianMomentumAdjoint (F.law t) (Kinetic.hiddenEmbedding (F.law t) v))) = _
    rw [gaussianMomentumAdjoint_hiddenEmbedding]
    rfl
  have hn : ‖closedGradient (F.law t) (F.potential t) ((F.potential_C2 t).of_le (by norm_num))
      (F.integrable t ht) (F.gibbs_law t ht) u‖ ≤ ‖v‖ := by
    rw [hDu]
    have hh := ContinuousLinearMap.le_of_opNorm_le _
      (gaussianCorrectorPositionGradient_norm_le (F.law t) (F.potential t) (F.potential_C2 t)
        (F.integrable t ht) (F.gibbs_law t ht) (F.lower t) 1 (F.lower_pos t ht)
        (F.hessian_lower t ht) hupper) (Kinetic.hiddenEmbedding (F.law t) v)
    simpa only [one_mul, (Kinetic.hiddenEmbedding (F.law t)).norm_map] using hh
  have hb := phaseHeat_green_position_bound F hf hc hheat t ht u
  rw [hu'] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left hn (norm_nonneg _))

/-- Actual weak Bochner rows bound the adjoint heat-current pairing with constant one. -/
theorem phaseHeat_corrector_adjoint_pairing_bound {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
    (t : ℝ) (ht : t ∈ Icc a b) (v : Lp ℝ 2 ((F.law t).prod (stdGaussian E))) :
    |inner ℝ (phaseHeatGeneratorLp F hf hc hheat t ht) ((phaseVisibleCorrector F t ht).adjoint v)| ≤
      ‖phaseHeatGradientLp F hf hc hheat t ht‖ * ‖v‖ := by
  have hupper : ∀ x w, fderiv ℝ (fderiv ℝ (F.potential t)) x w w ≤ 1*‖w‖^2 := by
    simpa only [one_mul] using F.hessian_upper t ht
  obtain ⟨R,hR,hbound⟩ := gaussianCorrectorAdjoint_spatial_rows (F.law t) (F.potential t)
    (F.potential_C2 t) (F.integrable t ht) (F.gibbs_law t ht) (F.lower t) 1
    (F.lower_pos t ht) (F.hessian_lower t ht) hupper (Kinetic.hiddenEmbedding (F.law t) v)
  simp only [gaussianAverage_hiddenEmbedding] at hR
  have hb := phaseHeat_green_rows_bound F hf hc hheat t ht
    (gradientPoissonInverse (F.law t) (F.potential t) (F.potential_C2 t)
      (F.integrable t ht) (F.gibbs_law t ht) (F.lower t) 1 (F.lower_pos t ht)
      (F.hessian_lower t ht) hupper (productAverage (F.law t) (stdGaussian E) v)) R hR
  have hn : Real.sqrt (∑ j, ‖R j‖^2) ≤ ‖v‖ := by
    have hh : (∑ j, ‖R j‖^2) ≤ ‖v‖^2 := by
      simpa only [(Kinetic.hiddenEmbedding (F.law t)).norm_map] using hbound
    exact (Real.sqrt_le_sqrt hh).trans_eq (Real.sqrt_sq (norm_nonneg _))
  unfold phaseVisibleCorrector
  rw [visibleCorrector_adjoint]
  exact hb.trans (mul_le_mul_of_nonneg_left hn (norm_nonneg _))

/-- The material derivative contributes the source constant one quarter, using
macro/micro orthogonality rather than only its operator norm. -/
theorem phaseHeat_materialCorrector_pairing_bound {a b : ℝ} (F : ReferencePoissonFamily E a b)
    (t : ℝ) (ht : t ∈ Ioo a b) (hscale : F.scale t = -(1/2:ℝ))
    (v : Lp ℝ 2 (gaussianPhaseMeasure (F.law a))) :
    |inner ℝ v (F.materialCorrector t ht v)| ≤ ‖v‖^2/4 := by
  have h := F.materialCorrector_macro_micro_bound t ht v v
  rw [hscale] at h
  norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)] at h
  have hp := gaussianPositionProjection_norm_sq (F.law a) v
  nlinarith [sq_nonneg (‖gaussianPositionProjection (F.law a) v‖ -
    ‖v-gaussianPositionProjection (F.law a) v‖)]

end AcceleratedLogConcave.Kinetic.Reheating
