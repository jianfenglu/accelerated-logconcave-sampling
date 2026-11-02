import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.Quotient
import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.Density

/-! Compact numerator derivatives have bounds relative to the positive initial
reference density. Gaussian averaging preserves these bounds uniformly through
zero variance; no inverse-time regularity loss is introduced. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson AcceleratedLogConcave.HeatCalculus
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

omit [Fintype ι] in
/-- Compact support and positivity yield relative bounds for actual derivatives. -/
theorem compact_norm_le_density {K : Type*} [NormedAddCommGroup K]
    {h : E → K} (hh : Continuous h) (hc : HasCompactSupport h)
    {p : E → ℝ} (hp : Continuous p) (hpos : ∀ x, 0 < p x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖h x‖ ≤ C * p x := by
  have hs : HasCompactSupport (fun x => ‖h x‖ / p x) := by
    have hn : HasCompactSupport (fun x => ‖h x‖) := hc.comp_left (g := fun z : K => ‖z‖) norm_zero
    simp only [div_eq_mul_inv]
    change HasCompactSupport ((fun x => ‖h x‖) * (fun x => (p x)⁻¹))
    exact hn.mul_right
  obtain ⟨C,hC⟩ := hs.exists_bound_of_continuous (hh.norm.div hp (fun x => (hpos x).ne'))
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  apply (div_le_iff₀ (hpos x)).mp
  exact (le_abs_self _).trans ((hC x).trans (le_max_left _ _))

/-- Relative numerator bounds survive the actual Gaussian averaging. -/
theorem gaussianAverage_norm_le_density {K : Type*} [NormedAddCommGroup K]
    [NormedSpace ℝ K] {h : E → K} (hh : Continuous h) (hc : HasCompactSupport h)
    {p : E → ℝ} (hp : Continuous p) {B C : ℝ} (hB : ∀ x, ‖p x‖ ≤ B)
    (hC : ∀ x, ‖h x‖ ≤ C * p x) (t : ℝ) (x : E) :
    ‖∫ g, h (x + Real.sqrt t • g) ∂stdGaussian E‖ ≤ C * heatAverage p t x := by
  obtain ⟨A,hA⟩ := hc.exists_bound_of_continuous hh
  have hi : Integrable (fun g => h (x + Real.sqrt t • g)) (stdGaussian E) :=
    (integrable_const A).mono' (by fun_prop : Continuous (fun g : E =>
      h (x + Real.sqrt t • g))).aestronglyMeasurable (Eventually.of_forall fun g => hA _)
  have hpI : Integrable (fun g => p (x + Real.sqrt t • g)) (stdGaussian E) :=
    (integrable_const B).mono' (by fun_prop : Continuous (fun g : E =>
      p (x + Real.sqrt t • g))).aestronglyMeasurable (Eventually.of_forall fun g => hB _)
  calc
    _ ≤ ∫ g, ‖h (x + Real.sqrt t • g)‖ ∂stdGaussian E := norm_integral_le_integral_norm _
    _ ≤ ∫ g, C * p (x + Real.sqrt t • g) ∂stdGaussian E :=
      integral_mono hi.norm (hpI.const_mul C) (fun g => hC _)
    _ = _ := integral_const_mul _ _

/-- The compact signed quotient is bounded uniformly over the actual heat family. -/
theorem compactHeatQuotient_bound {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, ∀ x, ‖compactHeatQuotient F f t x‖ ≤ C := by
  have ha : a ∈ Icc a b := ⟨le_rfl,F.ordered⟩
  have hp := (reference_density_C2 F a ha).continuous
  have hh := hf.continuous.mul hp
  have hhc : HasCompactSupport (fun y => f y * F.density a y) := hc.mul_right
  obtain ⟨C,hC,hbound⟩ := compact_norm_le_density hh hhc hp (reference_density_pos F a ha)
  obtain ⟨B,hB⟩ := reference_density_bounded F a ha
  refine ⟨C,hC,fun t ht x => ?_⟩
  have hn := gaussianAverage_norm_le_density hh hhc hp hB hbound (t-a) x
  rw [← reference_density_eq_heatAverage F t ht (hheat t ht)] at hn
  change ‖compactHeatNumerator F f t x‖ ≤ C * F.density t x at hn
  rw [compactHeatQuotient, norm_div, Real.norm_of_nonneg (reference_density_pos F t ht x).le]
  exact (div_le_iff₀ (reference_density_pos F t ht x)).mpr hn

/-- The exact input supremum bound passes to the actual heat quotient. -/
theorem compactHeatQuotient_norm_le_of_norm_le {a b : ℝ}
    (F : ReferencePoissonFamily E a b) {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) (t : ℝ) (ht : t ∈ Icc a b)
    (hheat : F.law t = heatedLaw (F.law a) (t-a)) (x : E) :
    ‖compactHeatQuotient F f t x‖ ≤ C := by
  have ha : a ∈ Icc a b := ⟨le_rfl,F.ordered⟩
  have hp := (reference_density_C2 F a ha).continuous
  obtain ⟨B,hB⟩ := reference_density_bounded F a ha
  have hn := gaussianAverage_norm_le_density (hf.continuous.mul hp)
    (show HasCompactSupport (fun y => f y * F.density a y) from hc.mul_right)
    hp hB (C := C) (fun y => by
      rw [Pi.mul_apply, norm_mul, Real.norm_of_nonneg (F.density_nonneg a ha y)]
      exact mul_le_mul_of_nonneg_right (hC y) (F.density_nonneg a ha y)) (t-a) x
  rw [← reference_density_eq_heatAverage F t ht hheat] at hn
  change ‖compactHeatNumerator F f t x‖ ≤ C * F.density t x at hn
  rw [compactHeatQuotient, norm_div, Real.norm_of_nonneg (reference_density_pos F t ht x).le]
  exact (div_le_iff₀ (reference_density_pos F t ht x)).mpr hn

end AcceleratedLogConcave.Kinetic.Reheating
