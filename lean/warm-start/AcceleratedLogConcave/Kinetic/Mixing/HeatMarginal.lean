import AcceleratedLogConcave.Channels.GaussianForward
import AcceleratedLogConcave.Kinetic.Reheating.HeatChannel

/-! Exact identification of the physical reheating marginal with W03's
Gaussian forward channel. The parameter is variance, with no factor of two. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace AcceleratedLogConcave.Kinetic.Reheating
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem heatedLaw_eq_forward (μ : Measure (EuclideanSpace ℝ ι)) [SFinite μ] (t : ℝ≥0) :
    heatedLaw μ t = Channels.forward μ t := by
  rw [Channels.forward, Channels.noise_eq_scaled_stdGaussian]
  change _ = (μ.prod ((stdGaussian (EuclideanSpace ℝ ι)).map
    (fun x => Real.sqrt (t : ℝ) • x))).map (fun z => z.1 + z.2)
  have hp := Measure.map_prod_map μ (stdGaussian (EuclideanSpace ℝ ι))
    measurable_id (show Measurable (fun x : EuclideanSpace ℝ ι => Real.sqrt (t : ℝ) • x) by fun_prop)
  rw [Measure.map_id] at hp
  rw [hp, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem heatedLaw_add (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (s t : ℝ≥0) : heatedLaw (heatedLaw μ s) t = heatedLaw μ (s+t : ℝ≥0) := by
  rw [heatedLaw_eq_forward, heatedLaw_eq_forward, heatedLaw_eq_forward, Channels.forward_add]

/-- The exact return identity used after a reverse-heat clock segment. -/
theorem heatedLaw_forward_return (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (s t a : ℝ≥0) (hst : s+t=a) :
    heatedLaw (Channels.forward μ s) t = Channels.forward μ a := by
  let : IsProbabilityMeasure (Channels.forward μ s) := by unfold Channels.forward; infer_instance
  rw [heatedLaw_eq_forward, Channels.forward_add, hst]

end AcceleratedLogConcave.Kinetic.Reheating
