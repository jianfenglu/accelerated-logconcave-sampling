import DirectW12.OriginalFamilyAdapter
import AcceleratedLogConcave.Kinetic.Mixing.OriginalHeatMixing

/-! Exact-reference bridge between the constructed recursive clock kernel,
its original-C² dormant W12 estimate, and physical heat-phase mixing.
No executed recursive program or tape law is identified here. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Kinetic.OriginalReferenceMixing
open AcceleratedLogConcave.Root
open AcceleratedLogConcave.Root.RecursiveInnovation
open AcceleratedLogConcave.Root.RecursiveRadiusFamily
open AcceleratedLogConcave.Root.ClockBackwardKernel
open AcceleratedLogConcave.Numerics.AffineGraph
open AcceleratedLogConcave.Kinetic
open AcceleratedLogConcave.Kinetic.Reheating
open AcceleratedLogConcave.Kinetic.ConditionalContraction
open AcceleratedLogConcave.Gibbs
open AcceleratedLogConcave.Analysis.Poisson

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι

def referenceKernel {V : E → ℝ} {κ h : ℝ} {m : ℕ}
    (hV : ContDiff ℝ 2 V) (hκ : 0 < κ) (hh : 0 < h) (hhalf : h ≤ 1 / 2)
    (hlo : ∀ z v, κ⁻¹ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) z v v)
    (hup : ∀ z v, fderiv ℝ (fderiv ℝ V) z v v ≤ ‖v‖ ^ 2)
    (G : MeanGeometry m) (hm : 0 < m) (t : ℝ) (ht : 0 < t) (K : ℕ) :
    Kernel (ClockLaw.Clock × GaussianPhase E) E :=
  sourceKernelFromRadiusFamily (originalPhysicalReference hV hκ hh hlo hup) h hh K
    (physicalRadiusChildren hh hhalf hV
      (fun z v => (mul_nonneg (inv_pos.mpr hκ).le (sq_nonneg ‖v‖)).trans (hlo z v))
      hup G hm t ht K)

instance referenceKernel_markov {V : E → ℝ} {κ h : ℝ} {m : ℕ}
    (hV : ContDiff ℝ 2 V) (hκ : 0 < κ) (hh : 0 < h) (hhalf : h ≤ 1 / 2)
    (hlo : ∀ z v, κ⁻¹ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) z v v)
    (hup : ∀ z v, fderiv ℝ (fderiv ℝ V) z v v ≤ ‖v‖ ^ 2)
    (G : MeanGeometry m) (hm : 0 < m) (t : ℝ) (ht : 0 < t) (K : ℕ) :
    IsMarkovKernel (referenceKernel hV hκ hh hhalf hlo hup G hm t ht K) := by
  unfold referenceKernel
  infer_instance

theorem referenceKernel_section {V : E → ℝ} {κ h : ℝ} {m : ℕ}
    (hV : ContDiff ℝ 2 V) (hκ : 0 < κ) (hh : 0 < h) (hhalf : h ≤ 1 / 2)
    (hlo : ∀ z v, κ⁻¹ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) z v v)
    (hup : ∀ z v, fderiv ℝ (fderiv ℝ V) z v v ≤ ‖v‖ ^ 2)
    (G : MeanGeometry m) (hm : 0 < m) (t : ℝ) (ht : 0 < t) (K : ℕ)
    (clock : ClockLaw.Clock) :
    clockSection (referenceKernel hV hκ hh hhalf hlo hup G hm t ht K) clock =
      physicalSourceSection hh hhalf hV
        (fun z v => (mul_nonneg (inv_pos.mpr hκ).le (sq_nonneg ‖v‖)).trans (hlo z v))
        hup G hm t ht K (originalPhysicalReference hV hκ hh hlo hup) clock := by
  rfl

/-- With the prescribed public order and radius, this is literally the
already constructed recursive reference root kernel. -/
theorem referenceKernel_eq_sourceRootKernel {V : E → ℝ} {κ h : ℝ}
    (hV : ContDiff ℝ 2 V) (hκ : 0 < κ) (hh : 0 < h) (hhalf : h ≤ 1 / 2)
    (hlo : ∀ z v, κ⁻¹ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) z v v)
    (hup : ∀ z v, fderiv ℝ (fderiv ℝ V) z v v ≤ ‖v‖ ^ 2)
    (Csch w : ℝ) (hC : 0 < Csch) (hw : 0 < w)
    (t : ℝ) (ht : 0 < t) (K : ℕ)
    (G : MeanGeometry (meanOrder Csch K w)) (hR : G.R = h ^ t) :
    referenceKernel hV hκ hh hhalf hlo hup G (meanOrder_pos hC hw K) t ht K =
      sourceRootKernel hh hhalf hV
        (fun z v => (mul_nonneg (inv_pos.mpr hκ).le (sq_nonneg ‖v‖)).trans (hlo z v))
        hup Csch w hC hw t ht K G hR
        (originalPhysicalReference hV hκ hh hlo hup) := by
  rfl

theorem referenceKernel_invariant {V : E → ℝ} {κ h : ℝ} {m : ℕ}
    (hV : ContDiff ℝ 2 V) (hκ : 0 < κ) (hh : 0 < h) (hhalf : h ≤ 1 / 2)
    (hlo : ∀ z v, κ⁻¹ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) z v v)
    (hup : ∀ z v, fderiv ℝ (fderiv ℝ V) z v v ≤ ‖v‖ ^ 2)
    (G : MeanGeometry m) (hm : 0 < m) (t : ℝ) (ht : 0 < t) (K : ℕ)
    (clock : ClockLaw.Clock) :
    ConditionalContraction.ConditionallyInvariant (stdGaussian E)
      (clockSection (referenceKernel hV hκ hh hhalf hlo hup G hm t ht K) clock) := by
  rw [referenceKernel_section]
  exact physicalSourceSection_invariant hh hhalf hV
    (fun z v => (mul_nonneg (inv_pos.mpr hκ).le (sq_nonneg ‖v‖)).trans (hlo z v))
    hup G hm t ht K (originalPhysicalReference hV hκ hh hlo hup) clock

private theorem referenceR_gt {h : ℝ} (hh : 0 < h) :
    2 * h ^ 2 < 2 * (2 * h ^ 2) := by
  nlinarith [sq_pos_of_pos hh]

omit [DecidableEq ι] in
private theorem referenceFamily_eq {V : E → ℝ} {κ h : ℝ}
    (hV : ContDiff ℝ 2 V) (hκ : 0 < κ) (hh : 0 < h)
    (hlo : ∀ z v, κ⁻¹ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) z v v)
    (hup : ∀ z v, fderiv ℝ (fderiv ℝ V) z v v ≤ ‖v‖ ^ 2) :
    clockTransportFamily
      (originalHeatMixingFamily (R := 2 * (2 * h ^ 2)) hV hκ hh
        (referenceR_gt hh) hlo hup)
      (by positivity) (referenceR_gt hh) =
      originalPhysicalReference hV hκ hh hlo hup := by
  rfl

/-- The exact jointly measurable clock kernel has the original-C² physical
dormant W12 estimate at every clock. This does not concern an executed kernel. -/
theorem referenceKernel_W12 {V : E → ℝ} {κ h : ℝ} {m : ℕ}
    (hV : ContDiff ℝ 2 V) (hκ : 0 < κ) (hh : 0 < h) (hhalf : h ≤ 1 / 2)
    (hlo : ∀ z v, κ⁻¹ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) z v v)
    (hup : ∀ z v, fderiv ℝ (fderiv ℝ V) z v v ≤ ‖v‖ ^ 2)
    (G : MeanGeometry m) (hm : 0 < m) (t : ℝ) (ht : 0 < t) (K : ℕ)
    (clock : ClockLaw.Clock) :
    physicalDormantW12
      (clockTransportFamily
        (originalHeatMixingFamily (R := 2 * (2 * h ^ 2)) hV hκ hh
          (referenceR_gt hh) hlo hup)
        (by positivity) (referenceR_gt hh))
      clock (clockSection (referenceKernel hV hκ hh hhalf hlo hup G hm t ht K) clock)
      (referenceKernel_invariant hV hκ hh hhalf hlo hup G hm t ht K clock)
      1 (2 * h ^ 2) := by
  exact original_C2_physicalDormantW12 hV hκ hh hhalf hlo hup G hm t ht K clock

/-- Physical heat-phase density mixing for the constructed reference clock
kernel at every iteration count. The same exact kernel occurs in the W12 input
and in the phase operator. -/
theorem referenceHeatPhase_mixing {V : E → ℝ} {κ h : ℝ} {m : ℕ}
    (hV : ContDiff ℝ 2 V) (hκ : 0 < κ) (hh : 0 < h)
    (hlo : ∀ z v, κ⁻¹ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) z v v)
    (hup : ∀ z v, fderiv ℝ (fderiv ℝ V) z v v ≤ ‖v‖ ^ 2)
    (G : MeanGeometry m) (hm : 0 < m) (t : ℝ) (ht : 0 < t) (K : ℕ)
    {θ : ℝ} (hm1 : (κ + 2 * h ^ 2)⁻¹ ≤ 1) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ Real.sqrt 2 / 32 / 32)
    (hh14 : h ≤ 1 / 4)
    (hhC : h ≤ (Real.sqrt 2 / 32) / (8 * ((1 : ℝ) / 2 + 200))) :
    letI : IsProbabilityMeasure (volume.tilted (fun x => -V x)) :=
      originalGibbs_probability_of_hessian_lower hV hκ hlo
    let H := originalHeatMixingFamily (R := 2 * (2 * h ^ 2)) hV hκ hh
      (referenceR_gt hh) hlo hup
    let P := clockTransportFamily H (by positivity) (referenceR_gt hh)
    let Q := referenceKernel hV hκ hh (by linarith) hlo hup G hm t ht K
    let hQ := fun clock => referenceKernel_invariant hV hκ hh (by linarith)
      hlo hup G hm t ht K clock
    let T := sourceCenteredPhaseDensity H (by positivity) (referenceR_gt hh)
      (Real.sqrt 2 * h) (Real.sqrt ((κ + 2 * h ^ 2)⁻¹) * h)
      (mul_nonneg (Real.sqrt_nonneg _) hh.le) (clockSection Q) hQ
      (fun f => sourceClockChannel_integrable H (by positivity) (referenceR_gt hh)
        (Real.sqrt 2 * h) (Real.sqrt ((κ + 2 * h ^ 2)⁻¹) * h)
        (mul_nonneg (Real.sqrt_nonneg _) hh.le) Q hQ f)
    let S := sourceCenteredPhaseOperator H (by positivity) (referenceR_gt hh)
      (Real.sqrt 2 * h) (Real.sqrt ((κ + 2 * h ^ 2)⁻¹) * h)
      (mul_nonneg (Real.sqrt_nonneg _) hh.le) (clockSection Q) hQ
      (fun f => sourceClockChannel_integrable H (by positivity) (referenceR_gt hh)
        (Real.sqrt 2 * h) (Real.sqrt ((κ + 2 * h ^ 2)⁻¹) * h)
        (mul_nonneg (Real.sqrt_nonneg _) hh.le) Q hQ f)
    ∀ k : ℕ,
      (‖(T : centered ((P.law 0).prod (stdGaussian E)) →L[ℝ]
        centered ((P.law 0).prod (stdGaussian E))) ^ k‖ ≤
        Real.sqrt ((5 / 3 : ℝ) *
          (sourceContractionFactor θ ((κ + 2 * h ^ 2)⁻¹) h) ^ k)) ∧
      (‖(S : centered ((P.law 0).prod (stdGaussian E)) →L[ℝ]
        centered ((P.law 0).prod (stdGaussian E))) ^ k‖ ≤
        Real.sqrt ((5 / 3 : ℝ) *
          (sourceContractionFactor θ ((κ + 2 * h ^ 2)⁻¹) h) ^ k)) := by
  let hhalf : h ≤ 1 / 2 := by linarith
  let Q := referenceKernel hV hκ hh hhalf hlo hup G hm t ht K
  let hQ : ∀ clock, ConditionallyInvariant (stdGaussian E) (clockSection Q clock) :=
    referenceKernel_invariant hV hκ hh hhalf hlo hup G hm t ht K
  have hW : ∀ clock, physicalDormantW12
      (clockTransportFamily
        (originalHeatMixingFamily (R := 2 * (2 * h ^ 2)) hV hκ hh
          (referenceR_gt hh) hlo hup)
        (by positivity) (referenceR_gt hh))
      clock (clockSection Q clock) (hQ clock) 1 (2 * h ^ 2) := by
    intro clock
    exact referenceKernel_W12 hV hκ hh hhalf hlo hup G hm t ht K clock
  have hmix := originalHeatPhase_mixing_of_kernel hV hκ hh
    (referenceR_gt hh) hlo hup hm1 hθ0 hθ (by norm_num : (0 : ℝ) ≤ 1)
    hh14 hhC Q hQ hW
  dsimp only
  intro k
  exact hmix k

end AcceleratedLogConcave.Kinetic.OriginalReferenceMixing
