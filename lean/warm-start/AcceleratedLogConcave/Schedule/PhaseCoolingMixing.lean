import AcceleratedLogConcave.Schedule.PhaseCoolingPath
import AcceleratedLogConcave.Probability.CommonKernelTV

/-! Literal homogeneous phase prefix followed by the actual discard/cooling
suffix. A proved phase mixing estimate contracts through that same suffix. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Schedule.PhaseCooling
open AcceleratedLogConcave.Probability
universe u
variable {Phase Center : Type u} [MeasurableSpace Phase] [MeasurableSpace Center]

/-- Composition of the actual first L cooling transitions, in execution order. -/
def coolingKernel (cool : ℕ→Kernel Center Center) : ℕ→Kernel Center Center
  | 0 => Kernel.id
  | L+1 => (cool L) ∘ₖ coolingKernel cool L
instance coolingKernel_markov (cool : ℕ→Kernel Center Center) [∀ j,IsMarkovKernel (cool j)] :
    ∀ L,IsMarkovKernel (coolingKernel cool L)
  | 0 => inferInstanceAs (IsMarkovKernel (Kernel.id : Kernel Center Center))
  | L+1 => by
    have := coolingKernel_markov cool L
    change IsMarkovKernel (cool L ∘ₖ coolingKernel cool L)
    infer_instance

/-- Momentum is discarded once, before the actual finite cooling suffix. -/
def suffixKernel (drop : Phase→Center) (hdrop : Measurable drop)
    (cool : ℕ→Kernel Center Center) (L : ℕ) : Kernel Phase Center :=
  coolingKernel cool L ∘ₖ Kernel.deterministic drop hdrop
instance suffixKernel_markov (drop : Phase→Center) (hdrop : Measurable drop)
    (cool : ℕ→Kernel Center Center) [∀ j,IsMarkovKernel (cool j)] (L : ℕ) :
    IsMarkovKernel (suffixKernel drop hdrop cool L) := by
  unfold suffixKernel
  infer_instance

private theorem referenceLaw_leading_phase (ν : Measure Phase) (phase : Kernel Phase Phase)
    (drop : Phase→Center) (hdrop : Measurable drop) (cool : ℕ→Kernel Center Center)
    (N j : ℕ) :
    Heterogeneous.referenceLaw ν (step phase drop hdrop cool (N+1)) (j+1)=
      Heterogeneous.referenceLaw (phase ∘ₘ ν) (step phase drop hdrop cool N) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change step phase drop hdrop cool (N+1) (j+1) ∘ₘ
      Heterogeneous.referenceLaw ν (step phase drop hdrop cool (N+1)) (j+1) =
      step phase drop hdrop cool N j ∘ₘ Heterogeneous.referenceLaw (phase ∘ₘ ν) (step phase drop hdrop cool N) j
    rw [ih]
    rfl

private theorem returnedLaw_leading_phase (ν : Measure Phase) (phase : Kernel Phase Phase)
    (drop : Phase→Center) (hdrop : Measurable drop) (cool : ℕ→Kernel Center Center)
    (N L : ℕ) :
    returnedLaw ν phase drop hdrop cool (N+1) L=returnedLaw (phase ∘ₘ ν) phase drop hdrop cool N L := by
  unfold returnedLaw
  change (Heterogeneous.referenceLaw ν (step phase drop hdrop cool (N+1)) (length N L+1)).map
      (returnCenter N L)=_
  rw [referenceLaw_leading_phase]

private theorem homogeneous_start (ν : Measure Phase) (phase : Kernel Phase Phase) (N : ℕ) :
    Probability.referenceLaw (phase ∘ₘ ν) (fun _=>phase) N=
      Probability.referenceLaw ν (fun _=>phase) (N+1) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [Probability.referenceLaw,Probability.referenceLaw,ih]

private theorem returnedLaw_zero (ν : Measure Phase) (phase : Kernel Phase Phase)
    (drop : Phase→Center) (hdrop : Measurable drop) (cool : ℕ→Kernel Center Center) (L : ℕ) :
    returnedLaw ν phase drop hdrop cool 0 L=suffixKernel drop hdrop cool L ∘ₘ ν := by
  induction L with
  | zero =>
    change (Kernel.deterministic drop hdrop ∘ₘ ν).map id =
      (Kernel.id ∘ₖ Kernel.deterministic drop hdrop) ∘ₘ ν
    rw [Measure.map_id,Kernel.id_comp]
  | succ L ih =>
    have he : returnedLaw ν phase drop hdrop cool 0 (L+1)=cool L ∘ₘ returnedLaw ν phase drop hdrop cool 0 L := by
      change (cool L ∘ₘ Heterogeneous.referenceLaw ν (step phase drop hdrop cool 0) (L+1)).map id =
        cool L ∘ₘ (Heterogeneous.referenceLaw ν (step phase drop hdrop cool 0) (L+1)).map id
      rw [Measure.map_id,Measure.map_id]
    calc
      _ = cool L ∘ₘ returnedLaw ν phase drop hdrop cool 0 L := he
      _ = cool L ∘ₘ (suffixKernel drop hdrop cool L ∘ₘ ν) := congrArg (fun ρ=>cool L ∘ₘ ρ) ih
      _ = (cool L ∘ₖ suffixKernel drop hdrop cool L) ∘ₘ ν := Measure.comp_assoc
      _ = _ := congrArg (fun K : Kernel Phase Center=>K ∘ₘ ν)
        (Kernel.comp_assoc (cool L) (coolingKernel cool L) (Kernel.deterministic drop hdrop)).symm

/-- Exact law identity for the existing heterogeneous scheduled path. -/
theorem returnedLaw_eq_suffix (ν : Measure Phase) (phase : Kernel Phase Phase)
    (drop : Phase→Center) (hdrop : Measurable drop) (cool : ℕ→Kernel Center Center) (N L : ℕ) :
    returnedLaw ν phase drop hdrop cool N L=
      suffixKernel drop hdrop cool L ∘ₘ Probability.referenceLaw ν (fun _=>phase) N := by
  induction N generalizing ν with
  | zero => exact returnedLaw_zero ν phase drop hdrop cool L
  | succ N ih =>
    rw [returnedLaw_leading_phase,ih,homogeneous_start]

/-- Changing cooling references are exact laws of the same finite suffix. -/
theorem suffixKernel_reference (μ : Measure Phase) (π : ℕ→Measure Center)
    (drop : Phase→Center) (hdrop : Measurable drop) (cool : ℕ→Kernel Center Center)
    (hfirst : μ.map drop=π 0) (hcool : ∀ j,cool j ∘ₘ π j=π (j+1)) (L : ℕ) :
    suffixKernel drop hdrop cool L ∘ₘ μ=π L := by
  induction L with
  | zero =>
    simpa only [suffixKernel,coolingKernel,Kernel.id_comp,Measure.deterministic_comp_eq_map] using hfirst
  | succ L ih =>
    change (cool L ∘ₖ coolingKernel cool L ∘ₖ Kernel.deterministic drop hdrop) ∘ₘ μ=π (L+1)
    rw [Kernel.comp_assoc,← Measure.comp_assoc]
    exact (congrArg (fun ν=>cool L ∘ₘ ν) ih).trans (hcool L)

/-- A common actual discard/cooling suffix cannot enlarge phase total variation. -/
theorem totalVariationDistance_returnedLaw_suffix_le
    (ν μ : Measure Phase) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (phase : Kernel Phase Phase) [IsMarkovKernel phase]
    (drop : Phase→Center) (hdrop : Measurable drop)
    (cool : ℕ→Kernel Center Center) [∀ j,IsMarkovKernel (cool j)] (N L : ℕ) :
    totalVariationDistance (returnedLaw ν phase drop hdrop cool N L)
      (suffixKernel drop hdrop cool L ∘ₘ μ)≤
      totalVariationDistance (Probability.referenceLaw ν (fun _=>phase) N) μ := by
  simpa only [returnedLaw_eq_suffix] using
    totalVariationDistance_common_kernel (Probability.referenceLaw ν (fun _=>phase) N) μ
      (suffixKernel drop hdrop cool L)

/-- Consume the proved homogeneous phase mixing bound at the exact boundary;
no mixing hypothesis about an already-cooled or approximate law is introduced. -/
theorem returnedLaw_mixing_le
    (ν μ : Measure Phase) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (π : ℕ→Measure Center) [∀ j,IsProbabilityMeasure (π j)] (phase : Kernel Phase Phase) [IsMarkovKernel phase]
    (drop : Phase→Center) (hdrop : Measurable drop)
    (cool : ℕ→Kernel Center Center) [∀ j,IsMarkovKernel (cool j)]
    (hfirst : μ.map drop=π 0) (hcool : ∀ j,cool j ∘ₘ π j=π (j+1))
    (N L : ℕ) {mixing : ℝ}
    (hmixing : totalVariationDistance (Probability.referenceLaw ν (fun _=>phase) N) μ≤mixing) :
    totalVariationDistance (returnedLaw ν phase drop hdrop cool N L) (π L)≤mixing := by
  have h := totalVariationDistance_returnedLaw_suffix_le ν μ phase drop hdrop cool N L
  have h' : totalVariationDistance (returnedLaw ν phase drop hdrop cool N L) (π L)≤
      totalVariationDistance (Probability.referenceLaw ν (fun _=>phase) N) μ := by
    simpa only [suffixKernel_reference μ π drop hdrop cool hfirst hcool L] using h
  exact h'.trans hmixing
end AcceleratedLogConcave.Schedule.PhaseCooling
