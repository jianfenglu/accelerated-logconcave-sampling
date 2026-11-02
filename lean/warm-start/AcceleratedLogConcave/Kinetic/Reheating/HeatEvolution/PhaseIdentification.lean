import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.PhaseCore
import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.PhaseMeasure
import AcceleratedLogConcave.Kinetic.Reheating.ProductAverage

/-! The joint position-momentum compact heat quotient is identified with the
actual density adjoint of the physical visible heat channel. Momentum is retained
and may be arbitrarily coupled to position in the input test. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped RealInnerProductSpace ENNReal
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson

section Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Ordinary visible heat: embed a fresh hidden Gaussian, then use its actual observation. -/
def ordinaryHeatDensity (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ) :
    Lp ℝ 2 (μ.prod (stdGaussian E)) →L[ℝ] Lp ℝ 2 ((heatedLaw μ t).prod (stdGaussian E)) :=
  (heatDensity μ t).comp (Kinetic.hiddenEmbedding μ).toContinuousLinearMap

theorem ordinaryHeatDensity_eq_referenceChannel_adjoint
    (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ) :
    ordinaryHeatDensity μ t = (referenceChannel
      (measurePreserving_fst (μ := μ.prod (stdGaussian E)) (ν := stdGaussian E))
      (heatObservation_measurePreserving μ t)).adjoint := by
  unfold referenceChannel
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
  rfl

theorem ordinaryHeatDensity_norm_le (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ) :
    ‖ordinaryHeatDensity μ t‖ ≤ 1 := by
  rw [ordinaryHeatDensity_eq_referenceChannel_adjoint, ContinuousLinearMap.adjoint.norm_map]
  exact referenceChannel_norm_le _ _

theorem ordinaryHeatDensity_one (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ) :
    ordinaryHeatDensity μ t (oneL2 (μ.prod (stdGaussian E))) =
      oneL2 ((heatedLaw μ t).prod (stdGaussian E)) := by
  rw [ordinaryHeatDensity_eq_referenceChannel_adjoint]
  have hp : MeasurePreserving (Prod.fst : GaussianPhase E → E×E)
      (gaussianPhaseMeasure μ) (μ.prod (stdGaussian E)) := measurePreserving_fst
  have he := referenceChannel_adjoint hp (heatObservation_measurePreserving μ t)
  exact (congrArg (fun T => T (oneL2 (μ.prod (stdGaussian E)))) he).trans
    (referenceChannel_one (heatObservation_measurePreserving μ t) hp)
end Operator

variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Positive perturbations of a joint compact input have the claimed actual output law. -/
theorem compactPhaseHeatQuotient_weighted_law {a b : ℝ}
    (F : ReferencePoissonFamily E a b) {f : E×E → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) {C : ℝ}
    (hC : ∀ z, ‖f z‖ ≤ C) (t : ℝ) (ht : t ∈ Icc a b)
    (hheat : F.law t = heatedLaw (F.law a) (t-a)) :
    ((gaussianPhaseMeasure (F.law a)).withDensity (fun z => ENNReal.ofReal (f z.1+C))).map
      (heatObservation (t-a)) =
    ((heatedLaw (F.law a) (t-a)).prod (stdGaussian E)).withDensity
      (fun z => ENNReal.ofReal (compactPhaseHeatQuotient F f t z+C)) := by
  apply weighted_observation_retained_parameter (F.law a) (heatedLaw (F.law a) (t-a))
    (stdGaussian E) (stdGaussian E) (scalarHeatObservation (t-a)) (by unfold scalarHeatObservation; fun_prop)
    (fun z => ENNReal.ofReal (f z+C))
    (fun z => ENNReal.ofReal (compactPhaseHeatQuotient F f t z+C))
    (hf.continuous.add_const C).measurable.ennreal_ofReal
    ((compactPhaseHeatQuotient_continuous F hf.continuous hc t ht).add_const C).measurable.ennreal_ofReal
  intro p
  have he := prod_withDensity_left (μ := F.law a) (ν := stdGaussian E)
    (f := fun x => ENNReal.ofReal (f (x,p)+C))
    (((phase_position_slice_C2 hf p).continuous.add_const C).measurable.ennreal_ofReal)
  rw [← he]
  change heatedLaw ((F.law a).withDensity (fun x => ENNReal.ofReal (f (x,p)+C))) (t-a) = _
  rw [compactHeatQuotient_weighted_law F (phase_position_slice_C2 hf p)
    (phase_position_slice_compact hc p) (fun x => hC (x,p)) t ht hheat, hheat]
  rfl

private theorem phase_toLp_add_constant {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {f : X → ℝ} (hf : MemLp f 2 μ) (C : ℝ) :
    (hf.add (memLp_const C)).toLp (fun x => f x+C) = hf.toLp f + C • oneL2 μ := by
  apply Lp.ext
  filter_upwards [(hf.add (memLp_const C)).coeFn_toLp,
    Lp.coeFn_add (hf.toLp f) (C • oneL2 μ), Lp.coeFn_smul C (oneL2 μ),
    hf.coeFn_toLp, (memLp_const (1:ℝ) (μ := μ) (p := 2)).coeFn_toLp] with x h1 h2 h3 h4 h5
  change (oneL2 μ) x = 1 at h5
  change ((hf.add (memLp_const C)).toLp (f + fun _ => C)) x = _
  rw [h1, h2]
  change f x+C = (hf.toLp f) x + (C • oneL2 μ) x
  rw [h3, h4]
  change f x+C = f x+C*(oneL2 μ) x
  rw [h5, mul_one]

/-- The actual phase heat channel equals the classical phase quotient on the
joint compact C2 core, with no independence restriction on the input. -/
theorem compactPhaseHeatQuotient_eq_ordinaryHeatDensity {a b : ℝ}
    (F : ReferencePoissonFamily E a b) {f : E×E → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (t : ℝ) (ht : t ∈ Icc a b)
    (hheat : F.law t = heatedLaw (F.law a) (t-a)) :
    ordinaryHeatDensity (F.law a) (t-a)
      (compactTestL2 ((F.law a).prod (stdGaussian E)) f hf.continuous hc)
      =ᵐ[(heatedLaw (F.law a) (t-a)).prod (stdGaussian E)] compactPhaseHeatQuotient F f t := by
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous hf.continuous
  have hq := compactPhaseHeatQuotient_continuous F hf.continuous hc t ht
  have hqC := compactPhaseHeatQuotient_norm_le F hf hc hC t ht hheat
  let hfL := compactTest_memLp ((F.law a).prod (stdGaussian E)) f hf.continuous hc
  have hqL : MemLp (compactPhaseHeatQuotient F f t) 2
      ((heatedLaw (F.law a) (t-a)).prod (stdGaussian E)) :=
    MemLp.of_bound hq.aestronglyMeasurable C (Eventually.of_forall hqC)
  have hpos (r : E×E → ℝ) (hr : ∀ x, ‖r x‖ ≤ C) (x : E×E) : 0 ≤ r x+C := by
    have h := neg_le_abs (r x)
    rw [← Real.norm_eq_abs] at h
    linarith [hr x]
  have he := referenceChannel_adjoint_toLp_of_weighted_map
    (measurePreserving_fst (μ := (F.law a).prod (stdGaussian E)) (ν := stdGaussian E))
    (heatObservation_measurePreserving (F.law a) (t-a))
    (hf.continuous.add_const C).measurable (hq.add_const C).measurable
    (hpos f hC) (hpos _ hqC) (hfL.add (memLp_const C)) (hqL.add (memLp_const C))
    (compactPhaseHeatQuotient_weighted_law F hf hc hC t ht hheat)
  rw [← ordinaryHeatDensity_eq_referenceChannel_adjoint,
    phase_toLp_add_constant, phase_toLp_add_constant, map_add, map_smul, ordinaryHeatDensity_one] at he
  have he' := add_right_cancel he
  change ordinaryHeatDensity (F.law a) (t-a)
    (compactTestL2 ((F.law a).prod (stdGaussian E)) f hf.continuous hc) = hqL.toLp _ at he'
  rw [he']
  exact hqL.coeFn_toLp

end AcceleratedLogConcave.Kinetic.Reheating
