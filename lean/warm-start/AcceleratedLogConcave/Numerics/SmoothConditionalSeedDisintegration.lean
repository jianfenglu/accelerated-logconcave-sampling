import AcceleratedLogConcave.Numerics.SmoothConditionalJetNorm
import Mathlib.MeasureTheory.Integral.Pi

/-!
Exact disintegration of conditional state-jet moments on the literal common
seed. The random center remains the actual function of the original phase.
This module does not supply a quantitative material second-moment estimate.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace AcceleratedLogConcave.Numerics.MeanResidualBridge
open MeanFlowLp AffineGraph ConditionalSmoothing Conditional
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι
variable (d : MeanFlowLp.Data ι m) (j : Fin m) (ρ : d.G.Kernel)

/-- The original center as a function of the original phase, with the unused
noise coordinates set to zero. No new center law is chosen. -/
def conditionalPhaseCenter (p : Centering.Phase E) : E :=
  conditionalCenter d j ρ (p, 0)

theorem conditionalCenter_eq_phaseCenter (w : Seed d) :
    conditionalCenter d j ρ w = conditionalPhaseCenter d j ρ w.1 := rfl

theorem continuous_conditionalPhaseCenter : Continuous (conditionalPhaseCenter d j ρ) :=
  (continuous_seedCenter d j ρ).comp (continuous_id.prodMk continuous_const)

omit [DecidableEq ι] in
/-- The local radius inherits the original small-curvature hypothesis. -/
theorem conditionalData_small : (conditionalData d ρ).r^2*d.ell ≤ 1/2 := by
  have hv : d.G.variance ρ ≤ 1 := by
    unfold AffineGraph.MeanGeometry.variance
    nlinarith [sq_nonneg (d.G.rho ρ)]
  change (d.r*Real.sqrt (d.G.variance ρ))^2*d.ell ≤ _
  rw [mul_pow, Real.sq_sqrt (d.G.variance_pos ρ).le]
  calc
    _ = (d.r^2*d.ell)*d.G.variance ρ := by ring
    _ ≤ d.r^2*d.ell := mul_le_of_le_one_right (mul_nonneg (sq_nonneg _) d.hell) hv
    _ ≤ _ := d.hsmall

/-- Fubini and the two actual finite-product Gaussian projections. This is an
identity for every jet order and every time, without a fixed-center estimate. -/
theorem integral_conditionalJet_sq_eq_phase_gaussian (k : ℕ) (t : ℝ) :
    (∫ w, ‖conditionalJet d j ρ k t w‖^2 ∂seedMeasure d) =
      ∫ p, ∫ z : E,
        ‖(jet (conditionalData d ρ) k t (conditionalPhaseCenter d j ρ p,z)).2‖^2
          ∂stdGaussian E ∂KernelFlowLp.seedMeasure (kernelData d) := by
  rw [seedMeasure, integral_prod _ (conditionalJet_memLp d j ρ k t).norm.integrable_sq]
  apply integral_congr_ae
  filter_upwards [] with p
  let f : E → ℝ := fun z =>
    ‖(jet (conditionalData d ρ) k t (conditionalPhaseCenter d j ρ p,z)).2‖^2
  have hf : Continuous f :=
    (((continuous_jet (conditionalData d ρ) k).comp
      (continuous_const.prodMk (continuous_const.prodMk continuous_id))).snd.norm).pow 2
  change (∫ w : Fin m → d.G.Kernel → E, f (w j ρ)
    ∂Measure.pi (fun _ : Fin m => Measure.pi (fun _ : d.G.Kernel => stdGaussian E))) = _
  rw [integral_comp_eval (μ := fun _ : Fin m => Measure.pi (fun _ : d.G.Kernel => stdGaussian E)) (i := j) (show AEStronglyMeasurable (fun z : d.G.Kernel → E => f (z ρ))
    (Measure.pi (fun _ : d.G.Kernel => stdGaussian E)) from
      (hf.comp (continuous_apply ρ)).aestronglyMeasurable)]
  exact integral_comp_eval (μ := fun _ : d.G.Kernel => stdGaussian E) (i := ρ) hf.aestronglyMeasurable

/-- The phase-dependent Gaussian moment is integrable under the original
phase law, derived from the already proved actual-seed L2 membership. -/
theorem integrable_phase_gaussian_jet_sq (k : ℕ) (t : ℝ) :
    Integrable (fun p => ∫ z : E,
      ‖(jet (conditionalData d ρ) k t (conditionalPhaseCenter d j ρ p,z)).2‖^2
        ∂stdGaussian E) (KernelFlowLp.seedMeasure (kernelData d)) := by
  have hi := (conditionalJet_memLp d j ρ k t).norm.integrable_sq.integral_prod_left
  apply hi.congr
  filter_upwards [] with p
  let f : E → ℝ := fun z =>
    ‖(jet (conditionalData d ρ) k t (conditionalPhaseCenter d j ρ p,z)).2‖^2
  have hf : Continuous f :=
    (((continuous_jet (conditionalData d ρ) k).comp
      (continuous_const.prodMk (continuous_const.prodMk continuous_id))).snd.norm).pow 2
  change (∫ w : Fin m → d.G.Kernel → E, f (w j ρ)
    ∂Measure.pi (fun _ : Fin m => Measure.pi (fun _ : d.G.Kernel => stdGaussian E))) = _
  rw [integral_comp_eval (μ := fun _ : Fin m => Measure.pi (fun _ : d.G.Kernel => stdGaussian E)) (i := j) (show AEStronglyMeasurable (fun z : d.G.Kernel → E => f (z ρ))
    (Measure.pi (fun _ : d.G.Kernel => stdGaussian E)) from
      (hf.comp (continuous_apply ρ)).aestronglyMeasurable)]
  exact integral_comp_eval (μ := fun _ : d.G.Kernel => stdGaussian E) (i := ρ) hf.aestronglyMeasurable

/-- Exact receiver moment on the phase/Gaussian disintegration. The missing
uniform bound must have amplitude ell * localRadius^2 before cancellation. -/
theorem norm_sq_iteratedDeriv_conditionalMean_eq_phase_gaussian
    (U : H d → ℝ → H d) (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U)
    (k : ℕ) {t : ℝ} (ht : t ∈ Icc 0 conditionalEnd) :
    ‖iteratedDeriv k ((curvesWithConditional d).conditionalMean d.G U 0 d.r j ρ) t‖^2 =
      (d.r*Real.sqrt (d.G.variance ρ))⁻¹^2 *
        ∫ p, ∫ z : E,
          ‖(jet (conditionalData d ρ) (k+1) t (conditionalPhaseCenter d j ρ p,z)).2‖^2
            ∂stdGaussian E ∂KernelFlowLp.seedMeasure (kernelData d) := by
  rw [norm_sq_iteratedDeriv_replacement_conditionalMean d j ρ U hu k
    (Analysis.PositiveVarianceSlab.source_subset conditionalEnd_pos.le conditionalEnd_lt_one ht),
    integral_conditionalJet_sq_eq_phase_gaussian]

end AcceleratedLogConcave.Numerics.MeanResidualBridge
