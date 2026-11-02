import AcceleratedLogConcave.Probability.HeterogeneousPath
import AcceleratedLogConcave.Probability.WarmnessKernel

/-!
# Phase, momentum-discard, and cooling path composition

The visible states are a phase state for the first `N` transitions, followed
by a center state after one common deterministic discard, followed by `L`
cooling transitions. This is the actual order in `warm-start.tex` lines
164–205 and 242–260, not a homogeneous mixing theorem.

All local exact-to-implemented KL suppliers remain explicit. The exact
reference laws are proved from phase invariance, the discard pushforward,
and the changing cooling references. Only the initial input is required
to be L2 warm. No approximate stationarity, root construction, or W12
estimate is assumed or concluded here.
-/

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace AcceleratedLogConcave.Schedule.PhaseCooling

open AcceleratedLogConcave.Probability
open AcceleratedLogConcave.Probability.Heterogeneous

universe u
variable {Phase Center : Type u}
  [MeasurableSpace Phase] [MeasurableSpace Center]

/-- Time zero is the supplied joint phase state. After `N` phase transitions
the next transition discards momentum; no dummy state or tape is inserted. -/
@[reducible] def State (Phase Center : Type u) : ℕ → ℕ → Type u
  | _, 0 => Phase
  | 0, _ + 1 => Center
  | N + 1, j + 1 => State Phase Center N j
termination_by structural _ j => j

@[reducible] instance stateMeasurableSpace :
    (N j : ℕ) → MeasurableSpace (State Phase Center N j)
  | _, 0 => inferInstanceAs (MeasurableSpace Phase)
  | 0, _ + 1 => inferInstanceAs (MeasurableSpace Center)
  | N + 1, j + 1 => stateMeasurableSpace N j
termination_by structural _ j => j

instance stateCountablyGenerated
    [MeasurableSpace.CountablyGenerated Phase]
    [MeasurableSpace.CountablyGenerated Center] :
    (N j : ℕ) → MeasurableSpace.CountablyGenerated (State Phase Center N j)
  | _, 0 => inferInstanceAs (MeasurableSpace.CountablyGenerated Phase)
  | 0, _ + 1 => inferInstanceAs (MeasurableSpace.CountablyGenerated Center)
  | N + 1, j + 1 => stateCountablyGenerated N j
termination_by structural _ j => j

/-- Recursive order makes every transition's actual domain and codomain
definitionally visible, including the phase-to-center boundary. -/
def step (phase : Kernel Phase Phase) (drop : Phase → Center)
    (hdrop : Measurable drop) (cool : ℕ → Kernel Center Center) :
    (N j : ℕ) → Kernel (State Phase Center N j) (State Phase Center N (j + 1))
  | 0, 0 => Kernel.deterministic drop hdrop
  | 0, j + 1 => cool j
  | _ + 1, 0 => phase
  | N + 1, j + 1 => step phase drop hdrop cool N j
termination_by structural _ j => j

instance step_isMarkovKernel
    (phase : Kernel Phase Phase) [IsMarkovKernel phase]
    (drop : Phase → Center) (hdrop : Measurable drop)
    (cool : ℕ → Kernel Center Center) [∀ j, IsMarkovKernel (cool j)] :
    (N j : ℕ) → IsMarkovKernel (step phase drop hdrop cool N j)
  | 0, 0 => inferInstanceAs (IsMarkovKernel (Kernel.deterministic drop hdrop))
  | 0, j + 1 => inferInstanceAs (IsMarkovKernel (cool j))
  | _ + 1, 0 => inferInstanceAs (IsMarkovKernel phase)
  | N + 1, j + 1 => step_isMarkovKernel phase drop hdrop cool N j
termination_by structural _ j => j

/-- The extra transition is a deterministic projection, not another oracle call. -/
def length (N L : ℕ) : ℕ := L + 1 + N

theorem length_eq (N L : ℕ) : length N L = N + 1 + L := by
  simp only [length]
  omega

/-- At the actual horizon the state is a center. This is only the type-level
identification, not a random decoder or another stochastic transition. -/
def returnCenter : (N L : ℕ) → State Phase Center N (length N L) → Center
  | 0, _ => id
  | N + 1, L => returnCenter N L

theorem measurable_returnCenter (N L : ℕ) :
    Measurable (returnCenter (Phase := Phase) (Center := Center) N L) := by
  induction N with
  | zero => exact measurable_id
  | succ N ih => exact ih

/-- The returned law is the terminal marginal of the actual scheduled path. -/
def returnedLaw (ν : Measure Phase) (phase : Kernel Phase Phase)
    (drop : Phase → Center) (hdrop : Measurable drop)
    (cool : ℕ → Kernel Center Center) (N L : ℕ) : Measure Center :=
  (referenceLaw ν (step phase drop hdrop cool N) (length N L)).map
    (returnCenter N L)

instance returnedLaw_isProbabilityMeasure
    (ν : Measure Phase) [IsProbabilityMeasure ν]
    (phase : Kernel Phase Phase) [IsMarkovKernel phase]
    (drop : Phase → Center) (hdrop : Measurable drop)
    (cool : ℕ → Kernel Center Center) [∀ j, IsMarkovKernel (cool j)] (N L : ℕ) :
    IsProbabilityMeasure (returnedLaw ν phase drop hdrop cool N L) := by
  unfold returnedLaw
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_returnCenter N L).aemeasurable).2 inferInstance

/-- The intended reference at every scheduled visible state. -/
def scheduledReference (μ : Measure Phase) (π : ℕ → Measure Center) :
    (N j : ℕ) → Measure (State Phase Center N j)
  | _, 0 => μ
  | 0, j + 1 => π j
  | N + 1, j + 1 => scheduledReference μ π N j
termination_by structural _ j => j

theorem scheduledReference_step
    (μ : Measure Phase) (π : ℕ → Measure Center)
    (phase : Kernel Phase Phase) (drop : Phase → Center)
    (hdrop : Measurable drop) (cool : ℕ → Kernel Center Center)
    (hphase : phase ∘ₘ μ = μ) (hfirst : μ.map drop = π 0)
    (hcool : ∀ j, cool j ∘ₘ π j = π (j + 1)) (N j : ℕ) :
    step phase drop hdrop cool N j ∘ₘ scheduledReference μ π N j =
      scheduledReference μ π N (j + 1) := by
  induction N generalizing j with
  | zero =>
    cases j with
    | zero => simpa [step, scheduledReference, Measure.deterministic_comp_eq_map] using hfirst
    | succ j => exact hcool j
  | succ N ih =>
    cases j with
    | zero => exact hphase
    | succ j => exact ih j

/-- Every exact prefix has the asserted reference law, proved rather than
assumed as an independent family of marginal assertions. -/
theorem referenceLaw_eq_scheduledReference
    (μ : Measure Phase) (π : ℕ → Measure Center)
    (phase : Kernel Phase Phase) (drop : Phase → Center)
    (hdrop : Measurable drop) (cool : ℕ → Kernel Center Center)
    (hphase : phase ∘ₘ μ = μ) (hfirst : μ.map drop = π 0)
    (hcool : ∀ j, cool j ∘ₘ π j = π (j + 1)) (N j : ℕ) :
    referenceLaw μ (step phase drop hdrop cool N) j =
      scheduledReference μ π N j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Heterogeneous.referenceLaw, ih]
    exact scheduledReference_step μ π phase drop hdrop cool hphase hfirst hcool N j

theorem map_scheduledReference_returnCenter
    (μ : Measure Phase) (π : ℕ → Measure Center) (N L : ℕ) :
    (scheduledReference μ π N (length N L)).map (returnCenter N L) = π L := by
  induction N with
  | zero => exact Measure.map_id
  | succ N ih => exact ih

/-- Under the stationary phase input, cooling reaches exactly its `L`th
changing reference. This does not assert mixing for a warm nonstationary input. -/
theorem returnedLaw_reference
    (μ : Measure Phase) (π : ℕ → Measure Center)
    (phase : Kernel Phase Phase) (drop : Phase → Center)
    (hdrop : Measurable drop) (cool : ℕ → Kernel Center Center)
    (hphase : phase ∘ₘ μ = μ) (hfirst : μ.map drop = π 0)
    (hcool : ∀ j, cool j ∘ₘ π j = π (j + 1)) (N L : ℕ) :
    returnedLaw μ phase drop hdrop cool N L = π L := by
  unfold returnedLaw
  rw [referenceLaw_eq_scheduledReference μ π phase drop hdrop cool hphase hfirst hcool]
  exact map_scheduledReference_returnCenter μ π N L

/-- Per-step KL radii in the exact execution order. The common discard costs zero. -/
def radius (phaseRadius coolingRadius : ℝ) : ℕ → ℕ → ℝ
  | 0, 0 => 0
  | 0, _ + 1 => coolingRadius
  | _ + 1, 0 => phaseRadius
  | N + 1, j + 1 => radius phaseRadius coolingRadius N j

/-- Scalar deterministic per-call accounting in the same execution order.
The discard contributes zero, so it is absent from the oracle-call total. -/
theorem sum_stage_cost (phaseCost coolingCost : ℝ) (N L : ℕ) :
    ∑ j ∈ Finset.range (length N L), radius phaseCost coolingCost N j =
      (N : ℝ) * phaseCost + (L : ℝ) * coolingCost := by
  induction N with
  | zero => simp [length, Finset.sum_range_succ', radius]
  | succ N ih =>
    rw [show length (N + 1) L = length N L + 1 from rfl, Finset.sum_range_succ']
    simp only [radius, ih, Nat.cast_add, Nat.cast_one]
    ring

theorem sum_stage_cost_le {phaseCost coolingCost cap : ℝ}
    (hphase : phaseCost ≤ cap) (hcool : coolingCost ≤ cap) (N L : ℕ) :
    ∑ j ∈ Finset.range (length N L), radius phaseCost coolingCost N j ≤
      ((N : ℝ) + (L : ℝ)) * cap := by
  rw [sum_stage_cost, add_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left hphase (Nat.cast_nonneg N))
    (mul_le_mul_of_nonneg_left hcool (Nat.cast_nonneg L))

theorem sum_radius_sq (phaseRadius coolingRadius : ℝ) (N L : ℕ) :
    ∑ j ∈ Finset.range (length N L), radius phaseRadius coolingRadius N j ^ 2 =
      (N : ℝ) * phaseRadius ^ 2 + (L : ℝ) * coolingRadius ^ 2 := by
  induction N with
  | zero => simp [length, Finset.sum_range_succ', radius]
  | succ N ih =>
    rw [show length (N + 1) L = length N L + 1 from rfl, Finset.sum_range_succ']
    simp only [radius, ih, Nat.cast_add, Nat.cast_one]
    ring

theorem local_kl_le
    (μ : Measure Phase) (π : ℕ → Measure Center)
    (phase implementedPhase : Kernel Phase Phase)
    (drop : Phase → Center) (hdrop : Measurable drop)
    (cool implementedCool : ℕ → Kernel Center Center)
    (phaseRadius coolingRadius : ℝ) (L : ℕ)
    (hphaseKL : (∫⁻ z, klDiv (phase z) (implementedPhase z) ∂μ) ≤
      ENNReal.ofReal (phaseRadius ^ 2))
    (hcoolKL : ∀ j < L, (∫⁻ x, klDiv (cool j x) (implementedCool j x) ∂π j) ≤
      ENNReal.ofReal (coolingRadius ^ 2)) (N j : ℕ) (hj : j < length N L) :
    (∫⁻ x, klDiv (step phase drop hdrop cool N j x)
      (step implementedPhase drop hdrop implementedCool N j x)
      ∂scheduledReference μ π N j) ≤
        ENNReal.ofReal (radius phaseRadius coolingRadius N j ^ 2) := by
  induction N generalizing j with
  | zero =>
    cases j with
    | zero => simp [step, scheduledReference, radius]
    | succ j =>
      exact hcoolKL j (by dsimp [length] at hj; omega)
  | succ N ih =>
    cases j with
    | zero => exact hphaseKL
    | succ j => exact ih j (by dsimp [length] at hj ⊢; omega)

variable [MeasurableSpace.CountablyGenerated Phase]
  [MeasurableSpace.CountablyGenerated Center]

/-- Only the two local KL suppliers are analytic implementation obligations.
The zero-cost common discard and the complete finite sum are proved here. -/
theorem totalVariationDistance_returnedLaw_le_sqrt
    {μ ν : Measure Phase} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B : ℝ} (hWarm : L2Warm μ ν B)
    (π : ℕ → Measure Center)
    (phase implementedPhase : Kernel Phase Phase)
    [IsMarkovKernel phase] [IsMarkovKernel implementedPhase]
    (drop : Phase → Center) (hdrop : Measurable drop)
    (cool implementedCool : ℕ → Kernel Center Center)
    [∀ j, IsMarkovKernel (cool j)] [∀ j, IsMarkovKernel (implementedCool j)]
    (hphase : phase ∘ₘ μ = μ) (hfirst : μ.map drop = π 0)
    (hcool : ∀ j, cool j ∘ₘ π j = π (j + 1))
    (phaseRadius coolingRadius : ℝ) (N L : ℕ)
    (hphaseKL : (∫⁻ z, klDiv (phase z) (implementedPhase z) ∂μ) ≤
      ENNReal.ofReal (phaseRadius ^ 2))
    (hcoolKL : ∀ j < L, (∫⁻ x, klDiv (cool j x) (implementedCool j x) ∂π j) ≤
      ENNReal.ofReal (coolingRadius ^ 2)) :
    totalVariationDistance
      (returnedLaw ν phase drop hdrop cool N L)
      (returnedLaw ν implementedPhase drop hdrop implementedCool N L) ≤
      Real.sqrt (B / 2 * ((N : ℝ) * phaseRadius ^ 2 +
        (L : ℝ) * coolingRadius ^ 2)) := by
  have hlocal (j : ℕ) (hj : j < length N L) :
      (∫⁻ x, klDiv (step phase drop hdrop cool N j x)
        (step implementedPhase drop hdrop implementedCool N j x)
        ∂Heterogeneous.referenceLaw μ (step phase drop hdrop cool N) j) ≤
          ENNReal.ofReal (radius phaseRadius coolingRadius N j ^ 2) := by
    rw [referenceLaw_eq_scheduledReference μ π phase drop hdrop cool hphase hfirst hcool]
    exact local_kl_le μ π phase implementedPhase drop hdrop cool implementedCool
      phaseRadius coolingRadius L hphaseKL hcoolKL N j hj
  have hpath := Heterogeneous.totalVariationDistance_referenceLaw_le_sqrt_sum
    hWarm (step phase drop hdrop cool N)
      (step implementedPhase drop hdrop implementedCool N)
      (length N L) (radius phaseRadius coolingRadius N) hlocal
  rw [sum_radius_sq] at hpath
  exact (totalVariationDistance_map_le _ _ (returnCenter N L)
    (measurable_returnCenter N L)).trans hpath

omit [MeasurableSpace.CountablyGenerated Phase]
  [MeasurableSpace.CountablyGenerated Center] in
/-- Warmness propagates only through the exact kernels, with the same initial
budget. No analogous claim about the implemented chain is made. -/
theorem warm_referenceLaw
    {μ ν : Measure Phase} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B : ℝ} (hWarm : L2Warm μ ν B)
    (phase : Kernel Phase Phase) [IsMarkovKernel phase]
    (drop : Phase → Center) (hdrop : Measurable drop)
    (cool : ℕ → Kernel Center Center) [∀ j, IsMarkovKernel (cool j)]
    (N j : ℕ) :
    L2Warm (Heterogeneous.referenceLaw μ (step phase drop hdrop cool N) j)
      (Heterogeneous.referenceLaw ν (step phase drop hdrop cool N) j) B := by
  induction j with
  | zero => exact hWarm
  | succ j ih => exact ih.kernel (step phase drop hdrop cool N j)

omit [MeasurableSpace.CountablyGenerated Phase]
  [MeasurableSpace.CountablyGenerated Center] in
theorem warm_returnedLaw
    {μ ν : Measure Phase} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B : ℝ} (hWarm : L2Warm μ ν B)
    (π : ℕ → Measure Center)
    (phase : Kernel Phase Phase) [IsMarkovKernel phase]
    (drop : Phase → Center) (hdrop : Measurable drop)
    (cool : ℕ → Kernel Center Center) [∀ j, IsMarkovKernel (cool j)]
    (hphase : phase ∘ₘ μ = μ) (hfirst : μ.map drop = π 0)
    (hcool : ∀ j, cool j ∘ₘ π j = π (j + 1)) (N L : ℕ) :
    L2Warm (π L) (returnedLaw ν phase drop hdrop cool N L) B := by
  have hw := (warm_referenceLaw hWarm phase drop hdrop cool N (length N L)).map
    (measurable_returnCenter N L)
  change L2Warm (returnedLaw μ phase drop hdrop cool N L)
    (returnedLaw ν phase drop hdrop cool N L) B at hw
  rwa [returnedLaw_reference μ π phase drop hdrop cool hphase hfirst hcool] at hw

/-- Insert the source's two different local entropy scales; no entropy is
averaged under an approximate-chain marginal. -/
theorem totalVariationDistance_returnedLaw_le_budget
    {μ ν : Measure Phase} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B : ℝ} (hWarm : L2Warm μ ν B)
    (π : ℕ → Measure Center)
    (phase implementedPhase : Kernel Phase Phase)
    [IsMarkovKernel phase] [IsMarkovKernel implementedPhase]
    (drop : Phase → Center) (hdrop : Measurable drop)
    (cool implementedCool : ℕ → Kernel Center Center)
    [∀ j, IsMarkovKernel (cool j)] [∀ j, IsMarkovKernel (implementedCool j)]
    (hphase : phase ∘ₘ μ = μ) (hfirst : μ.map drop = π 0)
    (hcool : ∀ j, cool j ∘ₘ π j = π (j + 1))
    {q Γ : ℝ} (hq : 0 ≤ q) (hΓ : 0 < Γ) (N L : ℕ)
    (hphaseKL : (∫⁻ z, klDiv (phase z) (implementedPhase z) ∂μ) ≤
      ENNReal.ofReal (q / Γ))
    (hcoolKL : ∀ j < L, (∫⁻ x, klDiv (cool j x) (implementedCool j x) ∂π j) ≤
      ENNReal.ofReal q) :
    totalVariationDistance
      (returnedLaw ν phase drop hdrop cool N L)
      (returnedLaw ν implementedPhase drop hdrop implementedCool N L) ≤
      Real.sqrt (B / 2 * q * ((N : ℝ) / Γ + (L : ℝ))) := by
  have hp : Real.sqrt (q / Γ) ^ 2 = q / Γ := Real.sq_sqrt (div_nonneg hq hΓ.le)
  have hc : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq
  have h := totalVariationDistance_returnedLaw_le_sqrt hWarm π phase implementedPhase
    drop hdrop cool implementedCool hphase hfirst hcool (Real.sqrt (q / Γ))
    (Real.sqrt q) N L (by simpa only [hp] using hphaseKL)
    (by simpa only [hc] using hcoolKL)
  rw [hp, hc] at h
  convert h using 1
  congr 1
  ring

/-- Assemble separately supplied exact mixing and one-time heat bias with the
proved implementation comparison. This is conditional assembly, not a proof
of either analytic supplier or of the public sampler theorem. -/
theorem returnedLaw_error_le
    {μ ν : Measure Phase} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B : ℝ} (hWarm : L2Warm μ ν B)
    (π : ℕ → Measure Center) [∀ j, IsProbabilityMeasure (π j)]
    (target : Measure Center) [IsProbabilityMeasure target]
    (phase implementedPhase : Kernel Phase Phase)
    [IsMarkovKernel phase] [IsMarkovKernel implementedPhase]
    (drop : Phase → Center) (hdrop : Measurable drop)
    (cool implementedCool : ℕ → Kernel Center Center)
    [∀ j, IsMarkovKernel (cool j)] [∀ j, IsMarkovKernel (implementedCool j)]
    (hphase : phase ∘ₘ μ = μ) (hfirst : μ.map drop = π 0)
    (hcool : ∀ j, cool j ∘ₘ π j = π (j + 1))
    {q Γ : ℝ} (hq : 0 ≤ q) (hΓ : 0 < Γ) (N L : ℕ)
    (hphaseKL : (∫⁻ z, klDiv (phase z) (implementedPhase z) ∂μ) ≤
      ENNReal.ofReal (q / Γ))
    (hcoolKL : ∀ j < L, (∫⁻ x, klDiv (cool j x) (implementedCool j x) ∂π j) ≤
      ENNReal.ofReal q)
    {mixing heatBias : ℝ}
    (hmixing : totalVariationDistance
      (returnedLaw ν phase drop hdrop cool N L) (π L) ≤ mixing)
    (hheat : totalVariationDistance (π L) target ≤ heatBias) :
    totalVariationDistance
      (returnedLaw ν implementedPhase drop hdrop implementedCool N L) target ≤
      mixing + heatBias + Real.sqrt (B / 2 * q * ((N : ℝ) / Γ + (L : ℝ))) := by
  have hi := totalVariationDistance_returnedLaw_le_budget hWarm π phase implementedPhase
    drop hdrop cool implementedCool hphase hfirst hcool hq hΓ N L hphaseKL hcoolKL
  rw [totalVariationDistance_comm] at hi
  have he := (totalVariationDistance_triangle
    (returnedLaw ν phase drop hdrop cool N L) (π L) target).trans
      (add_le_add hmixing hheat)
  have ht := (totalVariationDistance_triangle
    (returnedLaw ν implementedPhase drop hdrop implementedCool N L)
    (returnedLaw ν phase drop hdrop cool N L) target).trans (add_le_add hi he)
  linarith

end AcceleratedLogConcave.Schedule.PhaseCooling
