import AcceleratedLogConcave.Kinetic.Reheating.HeatChannel
import AcceleratedLogConcave.Kinetic.ReferenceChannel

/-! Signed relative densities of the actual Gaussian heat channel. These
operators are constructed from its physical coupling, and their test pairings
are identified with the actual Gaussian averages. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual observation with independent standard Gaussian noise. -/
def scalarHeatObservation (t : ℝ) (z : E × E) : E := z.1 + Real.sqrt t • z.2

theorem scalarHeatObservation_measurePreserving (μ : Measure E) (t : ℝ) :
    MeasurePreserving (scalarHeatObservation t) (μ.prod (stdGaussian E)) (heatedLaw μ t) :=
  (by unfold scalarHeatObservation; fun_prop : Measurable (scalarHeatObservation (E := E) t)).measurePreserving _

/-- Actual signed relative-density evolution, as the adjoint of the physical
heat test channel. No sign or centering condition is imposed on the input. -/
def scalarHeatDensity (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 (heatedLaw μ t) :=
  (referenceChannel (measurePreserving_fst (μ := μ) (ν := stdGaussian E))
    (scalarHeatObservation_measurePreserving μ t)).adjoint

theorem scalarHeatDensity_norm_le (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ) :
    ‖scalarHeatDensity μ t‖ ≤ 1 := by
  rw [scalarHeatDensity, ContinuousLinearMap.adjoint.norm_map]
  exact referenceChannel_norm_le _ _

theorem scalarHeatDensity_pairing (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ)
    (f : Lp ℝ 2 μ) (φ : Lp ℝ 2 (heatedLaw μ t)) :
    inner ℝ (scalarHeatDensity μ t f) φ =
      ∫ z, f z.1 * φ (scalarHeatObservation t z) ∂μ.prod (stdGaussian E) := by
  rw [scalarHeatDensity, ContinuousLinearMap.adjoint_inner_left]
  exact referenceChannel_pairing _ _ _ _

/-- Integral characterization for every actual L2 test representative. -/
theorem scalarHeatDensity_integral_test (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ)
    (f : Lp ℝ 2 μ) (φ : E → ℝ) (hφ : MemLp φ 2 (heatedLaw μ t)) :
    (∫ x, scalarHeatDensity μ t f x * φ x ∂heatedLaw μ t) =
      ∫ x, f x * (∫ g, φ (x + Real.sqrt t • g) ∂stdGaussian E) ∂μ := by
  have hl : inner ℝ (scalarHeatDensity μ t f) (hφ.toLp φ) =
      ∫ x, scalarHeatDensity μ t f x * φ x ∂heatedLaw μ t := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hφ.coeFn_toLp] with x hx
    simp only [hx, RCLike.inner_apply, conj_trivial]
    ring
  rw [← hl, scalarHeatDensity_pairing]
  have hcoe := (scalarHeatObservation_measurePreserving μ t).quasiMeasurePreserving.ae hφ.coeFn_toLp
  have heq : (fun z : E × E => f z.1 * hφ.toLp φ (scalarHeatObservation t z))
      =ᵐ[μ.prod (stdGaussian E)] fun z => f z.1 * φ (scalarHeatObservation t z) := by
    filter_upwards [hcoe] with z hz
    rw [hz]
  rw [integral_congr_ae heq]
  have hI : Integrable (fun z : E × E => f z.1 * φ (scalarHeatObservation t z))
      (μ.prod (stdGaussian E)) :=
    ((Lp.memLp f).comp_fst (stdGaussian E)).integrable_mul
      (hφ.comp_measurePreserving (scalarHeatObservation_measurePreserving μ t))
  rw [integral_prod _ hI]
  apply integral_congr_ae
  filter_upwards [] with x
  exact integral_const_mul _ _

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A bounded continuous compact test belongs to every probability L2 space. -/
theorem compactTest_memLp (μ : Measure E) [IsProbabilityMeasure μ]
    (φ : E → ℝ) (hφ : Continuous φ) (hc : HasCompactSupport φ) : MemLp φ 2 μ := by
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous hφ
  exact MemLp.of_bound hφ.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

/-- The actual L2 class of a compact continuous test. -/
def compactTestL2 (μ : Measure E) [IsProbabilityMeasure μ]
    (φ : E → ℝ) (hφ : Continuous φ) (hc : HasCompactSupport φ) : Lp ℝ 2 μ :=
  (compactTest_memLp μ φ hφ hc).toLp φ

/-- The physical signed test pairing is the iterated Gaussian average. -/
theorem scalarHeatDensity_compactTest (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ)
    (f : Lp ℝ 2 μ) (φ : E → ℝ) (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    inner ℝ (scalarHeatDensity μ t f) (compactTestL2 (heatedLaw μ t) φ hφ hc) =
      ∫ x, f x * (∫ g, φ (x + Real.sqrt t • g) ∂stdGaussian E) ∂μ := by
  rw [scalarHeatDensity_pairing]
  have hcoe := (scalarHeatObservation_measurePreserving μ t).quasiMeasurePreserving.ae
    (compactTest_memLp (heatedLaw μ t) φ hφ hc).coeFn_toLp
  have heq : (fun z : E × E => f z.1 * compactTestL2 (heatedLaw μ t) φ hφ hc
      (scalarHeatObservation t z)) =ᵐ[μ.prod (stdGaussian E)]
      fun z => f z.1 * φ (scalarHeatObservation t z) := by
    filter_upwards [hcoe] with z hz
    rw [compactTestL2, hz]
  rw [integral_congr_ae heq]
  have hI : Integrable (fun z : E × E => f z.1 * φ (scalarHeatObservation t z))
      (μ.prod (stdGaussian E)) :=
    ((Lp.memLp f).comp_fst (stdGaussian E)).integrable_mul
      ((compactTest_memLp (heatedLaw μ t) φ hφ hc).comp_measurePreserving
        (scalarHeatObservation_measurePreserving μ t))
  rw [integral_prod _ hI]
  apply integral_congr_ae
  filter_upwards [] with x
  exact integral_const_mul _ _

end AcceleratedLogConcave.Kinetic.Reheating
