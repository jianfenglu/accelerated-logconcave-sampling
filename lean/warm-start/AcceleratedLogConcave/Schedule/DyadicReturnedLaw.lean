import AcceleratedLogConcave.Schedule.PhaseCoolingPath
import AcceleratedLogConcave.Channels.EqualWidthBridge

/-!
# Actual dyadic cooling specialization

The exact cooling transition is the existing normalized-posterior
`Channels.equalWidthBridge`, at variance `a / 2^j`; it is not an abstract
kernel with an assumed heat-pushforward law. Its law identification is
discharged by `equalWidthBridge_comp_forward`.

The phase and implemented kernels are still supplied. In particular this
module does not identify a supplied phase with an executable normalized root,
prove its local KL estimate, or turn a dormant-kernel premise into a producer.
-/

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

namespace AcceleratedLogConcave.Schedule.Dyadic

open AcceleratedLogConcave.Probability
open AcceleratedLogConcave.Channels
open AcceleratedLogConcave.Schedule.PhaseCooling

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι

def variance (a : ℝ≥0) (j : ℕ) : ℝ≥0 := a / 2 ^ j

@[simp] theorem variance_zero (a : ℝ≥0) : variance a 0 = a := by
  simp [variance]

theorem variance_succ (a : ℝ≥0) (j : ℕ) :
    variance a (j + 1) = variance a j / 2 := by
  simp [variance, pow_succ, div_mul_eq_div_div]

theorem variance_pos {a : ℝ≥0} (ha : 0 < a) (j : ℕ) : 0 < variance a j :=
  div_pos ha (pow_pos (by norm_num) j)

def targetLaw (F : E → ℝ) : Measure E := volume.tilted (fun x ↦ -F x)

def cooledLaw (F : E → ℝ) (a : ℝ≥0) (j : ℕ) : Measure E :=
  forward (targetLaw F) (variance a j)

def phaseReference (F : E → ℝ) (a : ℝ≥0) : Measure (E × E) :=
  (cooledLaw F a 0).prod (stdGaussian E)

def coolingKernel (F : E → ℝ) (hF : Measurable F)
    (_hI : Integrable (fun x ↦ Real.exp (-F x))) (a : ℝ≥0) (j : ℕ) :
    Kernel E E :=
  equalWidthBridge F hF (variance a j)

instance coolingKernel_isMarkov {F : E → ℝ} (hF : Measurable F)
    (hI : Integrable (fun x ↦ Real.exp (-F x))) (a : ℝ≥0) (j : ℕ) :
    IsMarkovKernel (coolingKernel F hF hI a j) :=
  equalWidthBridge_isMarkov hF hI _

/-- The actual Gaussian-reserve midpoint decoder halves the variance. -/
theorem coolingKernel_comp_cooledLaw {F : E → ℝ} (hF : Measurable F)
    (hI : Integrable (fun x ↦ Real.exp (-F x))) {a : ℝ≥0}
    (ha : 0 < a) (j : ℕ) :
    coolingKernel F hF hI a j ∘ₘ cooledLaw F a j = cooledLaw F a (j + 1) := by
  simpa only [coolingKernel, cooledLaw, targetLaw, variance_succ] using
    equalWidthBridge_comp_forward hF hI (variance a j) (variance_pos ha j)

/-- Momentum is genuinely discarded; the first center reference is identified. -/
theorem phaseReference_map_fst (F : E → ℝ) (a : ℝ≥0) :
    (phaseReference F a).map Prod.fst = cooledLaw F a 0 :=
  Measure.fst_prod

theorem cooledLaw_isProbabilityMeasure {F : E → ℝ}
    (hI : Integrable (fun x ↦ Real.exp (-F x))) (a : ℝ≥0) (j : ℕ) :
    IsProbabilityMeasure (cooledLaw F a j) := by
  have : IsProbabilityMeasure (targetLaw F) := isProbabilityMeasure_tilted hI
  unfold cooledLaw forward
  infer_instance

theorem phaseReference_isProbabilityMeasure {F : E → ℝ}
    (hI : Integrable (fun x ↦ Real.exp (-F x))) (a : ℝ≥0) :
    IsProbabilityMeasure (phaseReference F a) := by
  have := cooledLaw_isProbabilityMeasure hI a 0
  unfold phaseReference
  infer_instance

/-- The terminal exact reference is the original Gibbs law convolved with
Gaussian variance `a / 2^L`, independently of the number of invariant phases. -/
theorem exact_reference_returnedLaw {F : E → ℝ} (hF : Measurable F)
    (hI : Integrable (fun x ↦ Real.exp (-F x))) {a : ℝ≥0} (ha : 0 < a)
    (phase : Kernel (E × E) (E × E))
    (hphase : phase ∘ₘ phaseReference F a = phaseReference F a) (N L : ℕ) :
    returnedLaw (phaseReference F a) phase Prod.fst measurable_fst
      (coolingKernel F hF hI a) N L = forward (targetLaw F) (a / 2 ^ L) := by
  exact returnedLaw_reference (phaseReference F a) (cooledLaw F a) phase
    Prod.fst measurable_fst (coolingKernel F hF hI a) hphase
      (phaseReference_map_fst F a) (coolingKernel_comp_cooledLaw hF hI ha) N L

/-- Actual cooling specialization of the implemented returned-law comparison.
Unproved phase invariance and both exact-reference local KL suppliers are visible. -/
theorem implementation_error {F : E → ℝ} (hF : Measurable F)
    (hI : Integrable (fun x ↦ Real.exp (-F x))) {a : ℝ≥0} (ha : 0 < a)
    {ν : Measure (E × E)} [IsProbabilityMeasure ν] {B : ℝ}
    (hWarm : L2Warm (phaseReference F a) ν B)
    (phase implementedPhase : Kernel (E × E) (E × E))
    [IsMarkovKernel phase] [IsMarkovKernel implementedPhase]
    (implementedCool : ℕ → Kernel E E) [∀ j, IsMarkovKernel (implementedCool j)]
    (hphase : phase ∘ₘ phaseReference F a = phaseReference F a)
    {q Γ : ℝ} (hq : 0 ≤ q) (hΓ : 0 < Γ) (N L : ℕ)
    (hphaseKL : (∫⁻ z, klDiv (phase z) (implementedPhase z) ∂phaseReference F a) ≤
      ENNReal.ofReal (q / Γ))
    (hcoolKL : ∀ j < L,
      (∫⁻ x, klDiv (coolingKernel F hF hI a j x) (implementedCool j x) ∂cooledLaw F a j) ≤
        ENNReal.ofReal q) :
    totalVariationDistance
      (returnedLaw ν phase Prod.fst measurable_fst (coolingKernel F hF hI a) N L)
      (returnedLaw ν implementedPhase Prod.fst measurable_fst implementedCool N L) ≤
      Real.sqrt (B / 2 * q * ((N : ℝ) / Γ + (L : ℝ))) := by
  have := phaseReference_isProbabilityMeasure hI a
  exact totalVariationDistance_returnedLaw_le_budget hWarm (cooledLaw F a)
    phase implementedPhase Prod.fst measurable_fst (coolingKernel F hF hI a)
    implementedCool hphase (phaseReference_map_fst F a)
    (coolingKernel_comp_cooledLaw hF hI ha) hq hΓ N L hphaseKL hcoolKL

/-- The exact cooled output remains warm relative to the identified dyadic
heat law. Its budget is the original joint input budget, even when position
and momentum were correlated under that input. -/
theorem exact_output_warm {F : E → ℝ} (hF : Measurable F)
    (hI : Integrable (fun x ↦ Real.exp (-F x))) {a : ℝ≥0} (ha : 0 < a)
    {ν : Measure (E × E)} [IsProbabilityMeasure ν] {B : ℝ}
    (hWarm : L2Warm (phaseReference F a) ν B)
    (phase : Kernel (E × E) (E × E)) [IsMarkovKernel phase]
    (hphase : phase ∘ₘ phaseReference F a = phaseReference F a) (N L : ℕ) :
    L2Warm (cooledLaw F a L)
      (returnedLaw ν phase Prod.fst measurable_fst (coolingKernel F hF hI a) N L) B := by
  have := phaseReference_isProbabilityMeasure hI a
  exact warm_returnedLaw hWarm (cooledLaw F a) phase Prod.fst measurable_fst
    (coolingKernel F hF hI a) hphase (phaseReference_map_fst F a)
    (coolingKernel_comp_cooledLaw hF hI ha) N L

/-- The final target error is conditional on separate mixing and terminal heat
bias suppliers. Both local implementation KL suppliers remain explicit too. -/
theorem error_le_of_suppliers {F : E → ℝ} (hF : Measurable F)
    (hI : Integrable (fun x ↦ Real.exp (-F x))) {a : ℝ≥0} (ha : 0 < a)
    {ν : Measure (E × E)} [IsProbabilityMeasure ν] {B : ℝ}
    (hWarm : L2Warm (phaseReference F a) ν B)
    (target : Measure E) [IsProbabilityMeasure target]
    (phase implementedPhase : Kernel (E × E) (E × E))
    [IsMarkovKernel phase] [IsMarkovKernel implementedPhase]
    (implementedCool : ℕ → Kernel E E) [∀ j, IsMarkovKernel (implementedCool j)]
    (hphase : phase ∘ₘ phaseReference F a = phaseReference F a)
    {q Γ : ℝ} (hq : 0 ≤ q) (hΓ : 0 < Γ) (N L : ℕ)
    (hphaseKL : (∫⁻ z, klDiv (phase z) (implementedPhase z) ∂phaseReference F a) ≤
      ENNReal.ofReal (q / Γ))
    (hcoolKL : ∀ j < L,
      (∫⁻ x, klDiv (coolingKernel F hF hI a j x) (implementedCool j x) ∂cooledLaw F a j) ≤
        ENNReal.ofReal q)
    {mixing heatBias : ℝ}
    (hmixing : letI := cooledLaw_isProbabilityMeasure hI a L
      totalVariationDistance
        (returnedLaw ν phase Prod.fst measurable_fst (coolingKernel F hF hI a) N L)
        (cooledLaw F a L) ≤ mixing)
    (hheat : letI := cooledLaw_isProbabilityMeasure hI a L
      totalVariationDistance (cooledLaw F a L) target ≤ heatBias) :
    totalVariationDistance
      (returnedLaw ν implementedPhase Prod.fst measurable_fst implementedCool N L) target ≤
      mixing + heatBias + Real.sqrt (B / 2 * q * ((N : ℝ) / Γ + (L : ℝ))) := by
  have := phaseReference_isProbabilityMeasure hI a
  have (j : ℕ) := cooledLaw_isProbabilityMeasure hI a j
  exact returnedLaw_error_le hWarm (cooledLaw F a) target phase implementedPhase
    Prod.fst measurable_fst (coolingKernel F hF hI a) implementedCool hphase
    (phaseReference_map_fst F a) (coolingKernel_comp_cooledLaw hF hI ha)
    hq hΓ N L hphaseKL hcoolKL hmixing hheat

/-- Source parameters, with the physical variance (not its square root). -/
def sourceVariance (h : ℝ) : ℝ≥0 := ⟨2 * h ^ 2, by positivity⟩

def sourceRate (κ h : ℝ) : ℝ := h / Real.sqrt (κ + 2 * h ^ 2)

theorem sourceVariance_pos {h : ℝ} (hh : 0 < h) : 0 < sourceVariance h := by
  change (0 : ℝ) < 2 * h ^ 2
  positivity

theorem sourceRate_pos {κ h : ℝ} (hκ : 1 ≤ κ) (hh : 0 < h) :
    0 < sourceRate κ h := by
  unfold sourceRate
  apply div_pos hh
  apply Real.sqrt_pos.2
  nlinarith [sq_nonneg h]

/-- Exact `C d h^(2K-2) (N/Γ+L)` parameter insertion. This is not a local-KL
producer: the supplied inequalities must concern these actual kernels. -/
theorem source_implementation_error
    (d K N L : ℕ) {F : EuclideanSpace ℝ (Fin d) → ℝ} (hF : Measurable F)
    (hI : Integrable (fun x ↦ Real.exp (-F x)))
    {h κ C : ℝ} (hh : 0 < h) (hκ : 1 ≤ κ) (hC : 0 ≤ C)
    {ν : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))}
    [IsProbabilityMeasure ν] {B : ℝ}
    (hWarm : L2Warm (phaseReference F (sourceVariance h)) ν B)
    (phase implementedPhase :
      Kernel (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))
        (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)))
    [IsMarkovKernel phase] [IsMarkovKernel implementedPhase]
    (implementedCool : ℕ → Kernel (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    [∀ j, IsMarkovKernel (implementedCool j)]
    (hphase : phase ∘ₘ phaseReference F (sourceVariance h) =
      phaseReference F (sourceVariance h))
    (hphaseKL :
      (∫⁻ z, klDiv (phase z) (implementedPhase z) ∂phaseReference F (sourceVariance h)) ≤
        ENNReal.ofReal (C * d * h ^ (2 * K - 2) / sourceRate κ h))
    (hcoolKL : ∀ j < L,
      (∫⁻ x, klDiv (coolingKernel F hF hI (sourceVariance h) j x)
        (implementedCool j x) ∂cooledLaw F (sourceVariance h) j) ≤
          ENNReal.ofReal (C * d * h ^ (2 * K - 2))) :
    totalVariationDistance
      (returnedLaw ν phase Prod.fst measurable_fst
        (coolingKernel F hF hI (sourceVariance h)) N L)
      (returnedLaw ν implementedPhase Prod.fst measurable_fst implementedCool N L) ≤
        Real.sqrt (B / 2 * (C * d * h ^ (2 * K - 2)) *
          ((N : ℝ) / (h / Real.sqrt (κ + 2 * h ^ 2)) + (L : ℝ))) :=
  implementation_error hF hI (sourceVariance_pos hh) hWarm phase implementedPhase
    implementedCool hphase (by positivity) (sourceRate_pos hκ hh) N L hphaseKL hcoolKL

end AcceleratedLogConcave.Schedule.Dyadic
