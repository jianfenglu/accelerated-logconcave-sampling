import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.Bounds
import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.WeightedIdentification

/-! Measure-level identification of the classical signed quotient with the
actual heat transition. Positive perturbations of the reference law encode
signed inputs without treating signed measures as probability laws. -/
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

private theorem density_mul (p r : E → ℝ) (hp : Continuous p) (hr : Continuous r)
    (hpos : ∀ x, 0 ≤ p x) :
    (volume.withDensity (fun x => ENNReal.ofReal (p x))).withDensity
      (fun x => ENNReal.ofReal (r x)) =
      volume.withDensity (fun x => ENNReal.ofReal (r x * p x)) := by
  rw [← withDensity_mul volume hp.measurable.ennreal_ofReal hr.measurable.ennreal_ofReal]
  congr 1
  funext x
  rw [Pi.mul_apply, ← ENNReal.ofReal_mul (hpos x), mul_comm]

/-- The true heat channel pushes the positive reference perturbation to the
positive perturbation represented by the classical quotient. -/
theorem compactHeatQuotient_weighted_law {a b : ℝ}
    (F : ReferencePoissonFamily E a b) {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) (t : ℝ) (ht : t ∈ Icc a b)
    (hheat : F.law t = heatedLaw (F.law a) (t-a)) :
    heatedLaw ((F.law a).withDensity (fun x => ENNReal.ofReal (f x + C))) (t-a) =
      (F.law t).withDensity (fun x => ENNReal.ofReal (compactHeatQuotient F f t x + C)) := by
  have ha : a ∈ Icc a b := ⟨le_rfl,F.ordered⟩
  have hC0 : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
  have hp := (reference_density_C2 F a ha).continuous
  have hpt := (reference_density_C2 F t ht).continuous
  have hq := (compactHeatQuotient_C2 F hf hc t ht).continuous
  obtain ⟨B,hB⟩ := reference_density_bounded F a ha
  have hB0 : 0 ≤ B := (norm_nonneg (F.density a 0)).trans (hB 0)
  have hplus : ∀ x, 0 ≤ (f x + C) * F.density a x := fun x =>
    mul_nonneg (by have h := neg_le_abs (f x); rw [← Real.norm_eq_abs] at h; linarith [hC x])
      (F.density_nonneg a ha x)
  have hbound : ∀ x, ‖(f x + C) * F.density a x‖ ≤ (2*C)*B := by
    intro x
    rw [norm_mul]
    apply mul_le_mul _ (hB x) (norm_nonneg _) (by positivity)
    have h := norm_add_le (f x) C
    rw [Real.norm_of_nonneg hC0] at h
    linarith [hC x]
  rw [F.density_law a ha, density_mul _ _ hp (hf.continuous.add_const C)
    (F.density_nonneg a ha),
    heatedLaw_withDensity (fun x => (f x+C)*F.density a x) ((hf.continuous.add_const C).mul hp) hplus hbound,
    F.density_law t ht, density_mul _ _ hpt (hq.add_const C) (F.density_nonneg t ht)]
  congr 1
  funext x
  congr 1
  have hpI : Integrable (fun g => F.density a (x + Real.sqrt (t-a) • g)) (stdGaussian E) :=
    (integrable_const B).mono' (by fun_prop : Continuous (fun g : E =>
      F.density a (x + Real.sqrt (t-a) • g))).aestronglyMeasurable
      (Eventually.of_forall fun g => hB _)
  obtain ⟨A,hA⟩ := (hc.mul_right (f' := F.density a)).exists_bound_of_continuous (hf.continuous.mul hp)
  have hnI : Integrable (fun g => f (x + Real.sqrt (t-a) • g) *
      F.density a (x + Real.sqrt (t-a) • g)) (stdGaussian E) :=
    (integrable_const A).mono' (by fun_prop : Continuous (fun g : E =>
      f (x + Real.sqrt (t-a) • g) * F.density a (x + Real.sqrt (t-a) • g))).aestronglyMeasurable
      (Eventually.of_forall fun g => hA _)
  have he : heatAverage (fun y => (f y+C)*F.density a y) (t-a) x =
      compactHeatNumerator F f t x + C * heatAverage (F.density a) (t-a) x := by
    simp only [heatAverage, compactHeatNumerator, add_mul]
    rw [integral_add hnI (hpI.const_mul C), integral_const_mul]
  rw [he, ← reference_density_eq_heatAverage F t ht hheat]
  dsimp [compactHeatQuotient]
  field_simp [(reference_density_pos F t ht x).ne']

private theorem toLp_add_constant {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {f : X → ℝ} (hf : MemLp f 2 μ) (C : ℝ) :
    (hf.add (memLp_const C)).toLp (fun x => f x+C) = hf.toLp f + C • oneL2 μ := by
  apply Lp.ext
  filter_upwards [(hf.add (memLp_const C)).coeFn_toLp,
    Lp.coeFn_add (hf.toLp f) (C • oneL2 μ), Lp.coeFn_smul C (oneL2 μ),
    hf.coeFn_toLp, (memLp_const (1:ℝ) (μ := μ) (p := 2)).coeFn_toLp] with x h1 h2 h3 h4 h5
  change (oneL2 μ) x = 1 at h5
  change ((hf.add (memLp_const C)).toLp (f + fun _ => C)) x = _
  rw [h1, h2]
  change f x + C = (hf.toLp f) x + (C • oneL2 μ) x
  rw [h3, h4]
  change f x + C = f x + C * (oneL2 μ) x
  rw [h5, mul_one]

/-- The classical quotient is the actual signed density adjoint, almost everywhere. -/
theorem compactHeatQuotient_eq_scalarHeatDensity {a b : ℝ}
    (F : ReferencePoissonFamily E a b) {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (t : ℝ) (ht : t ∈ Icc a b)
    (hheat : F.law t = heatedLaw (F.law a) (t-a)) :
    scalarHeatDensity (F.law a) (t-a)
      (compactTestL2 (F.law a) f hf.continuous hc) =ᵐ[heatedLaw (F.law a) (t-a)]
        compactHeatQuotient F f t := by
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous hf.continuous
  have hq := (compactHeatQuotient_C2 F hf hc t ht).continuous
  have hqC := compactHeatQuotient_norm_le_of_norm_le F hf hc hC t ht hheat
  have hqL : MemLp (compactHeatQuotient F f t) 2 (heatedLaw (F.law a) (t-a)) :=
    MemLp.of_bound hq.aestronglyMeasurable C (Eventually.of_forall hqC)
  let hfL := compactTest_memLp (F.law a) f hf.continuous hc
  let hp := measurePreserving_fst (μ := F.law a) (ν := stdGaussian E)
  let hobs := scalarHeatObservation_measurePreserving (F.law a) (t-a)
  have hw : (((F.law a).prod (stdGaussian E)).withDensity
      (fun z => ENNReal.ofReal (f z.1+C))).map (scalarHeatObservation (t-a)) =
      (heatedLaw (F.law a) (t-a)).withDensity
        (fun y => ENNReal.ofReal (compactHeatQuotient F f t y+C)) := by
    rw [← prod_withDensity_left (hf.continuous.add_const C).measurable.ennreal_ofReal]
    change heatedLaw ((F.law a).withDensity (fun x => ENNReal.ofReal (f x+C))) (t-a) = _
    rw [compactHeatQuotient_weighted_law F hf hc hC t ht hheat, hheat]
  have hpos (r : E → ℝ) (hr : ∀ x, ‖r x‖ ≤ C) (x : E) : 0 ≤ r x+C := by
    have h := neg_le_abs (r x)
    rw [← Real.norm_eq_abs] at h
    linarith [hr x]
  have he := referenceChannel_adjoint_toLp_of_weighted_map hp hobs
    (hf.continuous.add_const C).measurable (hq.add_const C).measurable
    (hpos f hC) (hpos _ hqC) (hfL.add (memLp_const C)) (hqL.add (memLp_const C)) hw
  rw [toLp_add_constant, toLp_add_constant, map_add, map_smul,
    referenceChannel_adjoint, referenceChannel_one] at he
  have he' := add_right_cancel he
  rw [← referenceChannel_adjoint hp hobs] at he'
  change scalarHeatDensity (F.law a) (t-a)
    (compactTestL2 (F.law a) f hf.continuous hc) = hqL.toLp _ at he'
  rw [he']
  exact hqL.coeFn_toLp

end AcceleratedLogConcave.Kinetic.Reheating
