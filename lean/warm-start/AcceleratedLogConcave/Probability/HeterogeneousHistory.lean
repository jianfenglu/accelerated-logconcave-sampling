import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.CompMap

/-!
# Finite paths with changing state spaces

Paths are nested products `X 0 × ⋯ × X n`: time zero is the supplied
initial state, and each step appends the next visible state. The measurable
state space may change with time. This generalizes the local fixed-space
`Probability.FiniteHistory` construction using the same Mathlib kernels.
No dummy state, oracle transcript, or random tape is included.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace AcceleratedLogConcave.Probability.Heterogeneous

/-- A finite visible-state history, including time zero. -/
@[reducible] def FiniteHistory (X : ℕ → Type*) : ℕ → Type _
  | 0 => X 0
  | n + 1 => FiniteHistory X n × X (n + 1)

@[reducible] instance finiteHistoryMeasurableSpace (X : ℕ → Type*) [∀ n, MeasurableSpace (X n)] :
    (n : ℕ) → MeasurableSpace (FiniteHistory X n)
  | 0 => inferInstanceAs (MeasurableSpace (X 0))
  | n + 1 => @Prod.instMeasurableSpace (FiniteHistory X n) (X (n + 1))
      (finiteHistoryMeasurableSpace X n) inferInstance

instance finiteHistoryCountablyGenerated (X : ℕ → Type*) [∀ n, MeasurableSpace (X n)]
    [∀ n, MeasurableSpace.CountablyGenerated (X n)] :
    (n : ℕ) → MeasurableSpace.CountablyGenerated (FiniteHistory X n)
  | 0 => inferInstanceAs (MeasurableSpace.CountablyGenerated (X 0))
  | n + 1 => by
    change MeasurableSpace.CountablyGenerated (FiniteHistory X n × X (n + 1))
    have := finiteHistoryCountablyGenerated X n
    infer_instance

/-- The last visible state. -/
def historyLast {X : ℕ → Type*} : (n : ℕ) → FiniteHistory X n → X n
  | 0 => id
  | _ + 1 => Prod.snd

/-- The retained initial state. -/
def historyInitial {X : ℕ → Type*} : (n : ℕ) → FiniteHistory X n → X 0
  | 0 => id
  | n + 1 => fun h => historyInitial n h.1

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]

theorem measurable_historyLast (n : ℕ) : Measurable (historyLast (X := X) n) := by
  cases n with
  | zero => exact measurable_id
  | succ n => exact measurable_snd

theorem measurable_historyInitial (n : ℕ) : Measurable (historyInitial (X := X) n) := by
  induction n with
  | zero => exact measurable_id
  | succ n ih => exact ih.comp measurable_fst

/-- Lift a state transition to the last state of a history. -/
noncomputable def historyStep {n : ℕ} (P : Kernel (X n) (X (n + 1))) : Kernel (FiniteHistory X n) (X (n + 1)) :=
  P.comap (historyLast n) (measurable_historyLast n)

instance historyStep_isMarkovKernel {n : ℕ} (P : Kernel (X n) (X (n + 1))) [IsMarkovKernel P] :
    IsMarkovKernel (historyStep P) := by
  unfold historyStep
  infer_instance

@[simp] theorem historyStep_apply {n : ℕ} (P : Kernel (X n) (X (n + 1))) (h : FiniteHistory X n) :
    historyStep P h = P (historyLast n h) := rfl

/-- The conditional law of the entire visible history given its initial state. -/
noncomputable def finiteHistoryKernel (P : (n : ℕ) → Kernel (X n) (X (n + 1))) :
    (n : ℕ) → Kernel (X 0) (FiniteHistory X n)
  | 0 => Kernel.id
  | n + 1 => finiteHistoryKernel P n ⊗ₖ
      (historyStep (P n)).comap Prod.snd measurable_snd

instance finiteHistoryKernel_isMarkovKernel (P : (n : ℕ) → Kernel (X n) (X (n + 1)))
    [∀ j, IsMarkovKernel (P j)] : (n : ℕ) → IsMarkovKernel (finiteHistoryKernel P n)
  | 0 => inferInstanceAs (IsMarkovKernel (Kernel.id : Kernel (X 0) (X 0)))
  | n + 1 => by
    have := finiteHistoryKernel_isMarkovKernel P n
    change IsMarkovKernel (finiteHistoryKernel P n ⊗ₖ
      (historyStep (P n)).comap Prod.snd measurable_snd)
    infer_instance

@[simp] theorem finiteHistoryKernel_zero (P : (n : ℕ) → Kernel (X n) (X (n + 1))) :
    finiteHistoryKernel P 0 = Kernel.id := rfl

/-- Appending a state is a genuine composition-product of the previous path law. -/
theorem finiteHistoryKernel_succ_apply (P : (n : ℕ) → Kernel (X n) (X (n + 1)))
    [∀ j, IsMarkovKernel (P j)] (n : ℕ) (x : X 0) :
    finiteHistoryKernel P (n + 1) x =
      (finiteHistoryKernel P n x) ⊗ₘ historyStep (P n) := by
  change (finiteHistoryKernel P n ⊗ₖ
    (historyStep (P n)).comap Prod.snd measurable_snd) x = _
  rw [Kernel.compProd_apply_eq_compProd_sectR]
  congr 1

/-- Projecting a conditional path to its retained initial state gives the supplied input. -/
theorem finiteHistoryKernel_map_historyInitial (P : (n : ℕ) → Kernel (X n) (X (n + 1)))
    [∀ j, IsMarkovKernel (P j)] (n : ℕ) (x : X 0) :
    (finiteHistoryKernel P n x).map (historyInitial n) = Measure.dirac x := by
  induction n with
  | zero => simp [finiteHistoryKernel, historyInitial, Kernel.id_apply]
  | succ n ih =>
    rw [finiteHistoryKernel_succ_apply]
    change ((finiteHistoryKernel P n x) ⊗ₘ historyStep (P n)).map
      (historyInitial n ∘ Prod.fst) = _
    rw [← Measure.map_map (measurable_historyInitial n) measurable_fst]
    change (((finiteHistoryKernel P n x) ⊗ₘ historyStep (P n)).fst).map
      (historyInitial n) = _
    rw [Measure.fst_compProd, ih]

/-- The unconditional path law from an arbitrary input law. -/
noncomputable def finiteHistoryLaw (μ : Measure (X 0)) (P : (n : ℕ) → Kernel (X n) (X (n + 1))) (n : ℕ) :
    Measure (FiniteHistory X n) := finiteHistoryKernel P n ∘ₘ μ

instance finiteHistoryLaw_isProbabilityMeasure (μ : Measure (X 0)) [IsProbabilityMeasure μ]
    (P : (n : ℕ) → Kernel (X n) (X (n + 1))) [∀ j, IsMarkovKernel (P j)] (n : ℕ) :
    IsProbabilityMeasure (finiteHistoryLaw μ P n) := by
  unfold finiteHistoryLaw
  infer_instance

instance finiteHistoryLaw_sfinite (μ : Measure (X 0)) [SFinite μ]
    (P : (n : ℕ) → Kernel (X n) (X (n + 1))) [∀ j, IsMarkovKernel (P j)] (n : ℕ) :
    SFinite (finiteHistoryLaw μ P n) := by
  unfold finiteHistoryLaw
  infer_instance

/-- The unconditional path law appends a state by a genuine composition-product. -/
theorem finiteHistoryLaw_succ (μ : Measure (X 0)) [SFinite μ]
    (P : (n : ℕ) → Kernel (X n) (X (n + 1))) [∀ j, IsMarkovKernel (P j)] (n : ℕ) :
    finiteHistoryLaw μ P (n + 1) = finiteHistoryLaw μ P n ⊗ₘ historyStep (P n) := by
  apply Measure.ext_of_lintegral
  intro f hf
  change (∫⁻ z, f z ∂(finiteHistoryKernel P (n + 1) ∘ₘ μ)) = _
  rw [Measure.lintegral_bind (finiteHistoryKernel P (n + 1)).aemeasurable hf.aemeasurable]
  simp_rw [finiteHistoryKernel_succ_apply P n]
  simp_rw [Measure.lintegral_compProd hf]
  change _ = ∫⁻ h, (∫⁻ y, f (h, y) ∂historyStep (P n) h) ∂(finiteHistoryKernel P n ∘ₘ μ)
  rw [Measure.lintegral_bind (finiteHistoryKernel P n).aemeasurable
    hf.lintegral_kernel_prod_right'.aemeasurable]

/-- The exact reference laws can change at each step. -/
noncomputable def referenceLaw (μ : Measure (X 0)) (P : (n : ℕ) → Kernel (X n) (X (n + 1))) : (n : ℕ) → Measure (X n)
  | 0 => μ
  | n + 1 => P n ∘ₘ referenceLaw μ P n

instance referenceLaw_isProbabilityMeasure (μ : Measure (X 0)) [IsProbabilityMeasure μ]
    (P : (n : ℕ) → Kernel (X n) (X (n + 1))) [∀ j, IsMarkovKernel (P j)] :
    (n : ℕ) → IsProbabilityMeasure (referenceLaw μ P n)
  | 0 => inferInstanceAs (IsProbabilityMeasure μ)
  | n + 1 => by
    have := referenceLaw_isProbabilityMeasure μ P n
    change IsProbabilityMeasure (P n ∘ₘ referenceLaw μ P n)
    infer_instance

/-- Integrating a terminal-state test against the conditional path gives the
corresponding exact reference marginal. -/
theorem lintegral_finiteHistoryKernel_historyLast (μ : Measure (X 0))
    (P : (n : ℕ) → Kernel (X n) (X (n + 1))) [∀ j, IsMarkovKernel (P j)]
    (n : ℕ) (f : X n → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, ∫⁻ h, f (historyLast n h) ∂finiteHistoryKernel P n x ∂μ) =
      ∫⁻ y, f y ∂referenceLaw μ P n := by
  induction n with
  | zero =>
    simp only [finiteHistoryKernel, historyLast, referenceLaw, Kernel.id_apply,
      id_eq, lintegral_dirac' _ hf]
  | succ n ih =>
    have hinner (x : X 0) :
        (∫⁻ h, f (historyLast (n + 1) h) ∂finiteHistoryKernel P (n + 1) x) =
          ∫⁻ h, ∫⁻ y, f y ∂P n (historyLast n h) ∂finiteHistoryKernel P n x := by
      rw [finiteHistoryKernel_succ_apply, Measure.lintegral_compProd]
      · rfl
      · exact hf.comp measurable_snd
    simp_rw [hinner]
    rw [ih (fun z => ∫⁻ y, f y ∂P n z) hf.lintegral_kernel]
    change _ = ∫⁻ y, f y ∂((P n) ∘ₘ referenceLaw μ P n)
    exact (Measure.lintegral_bind (P n).aemeasurable hf.aemeasurable).symm

/-- The last-state marginal of a path is exactly the iterated transition law. -/
theorem finiteHistoryLaw_map_historyLast (μ : Measure (X 0))
    (P : (n : ℕ) → Kernel (X n) (X (n + 1))) [∀ j, IsMarkovKernel (P j)] (n : ℕ) :
    (finiteHistoryLaw μ P n).map (historyLast n) = referenceLaw μ P n := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_historyLast n)]
  change (∫⁻ h, f (historyLast n h) ∂(finiteHistoryKernel P n ∘ₘ μ)) = _
  calc
    _ = ∫⁻ x, ∫⁻ h, f (historyLast n h) ∂finiteHistoryKernel P n x ∂μ :=
      Measure.lintegral_bind (finiteHistoryKernel P n).aemeasurable
        (hf.comp (measurable_historyLast n)).aemeasurable
    _ = _ := lintegral_finiteHistoryKernel_historyLast μ P n f hf

/-- Projecting the unconditional path to time zero recovers the supplied input law. -/
theorem finiteHistoryLaw_map_historyInitial (μ : Measure (X 0))
    (P : (n : ℕ) → Kernel (X n) (X (n + 1))) [∀ j, IsMarkovKernel (P j)] (n : ℕ) :
    (finiteHistoryLaw μ P n).map (historyInitial n) = μ := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_historyInitial n)]
  change (∫⁻ h, f (historyInitial n h) ∂(finiteHistoryKernel P n ∘ₘ μ)) = _
  have hx (x : X 0) :
      (∫⁻ h, f (historyInitial n h) ∂finiteHistoryKernel P n x) = f x := by
    rw [← lintegral_map hf (measurable_historyInitial n),
      finiteHistoryKernel_map_historyInitial, lintegral_dirac' _ hf]
  calc
    _ = ∫⁻ x, ∫⁻ h, f (historyInitial n h) ∂finiteHistoryKernel P n x ∂μ :=
      Measure.lintegral_bind (finiteHistoryKernel P n).aemeasurable
        (hf.comp (measurable_historyInitial n)).aemeasurable
    _ = _ := by simp_rw [hx]

end AcceleratedLogConcave.Probability.Heterogeneous
