import AcceleratedLogConcave.Probability.HeterogeneousHistory
import AcceleratedLogConcave.Probability.PathEntropy
import AcceleratedLogConcave.Probability.WarmTransfer
import AcceleratedLogConcave.Probability.Warmness

/-!
# Warm path comparison with time-dependent state spaces

Each transition may have a different measurable domain and codomain. The path
retains its initial state; entropy costs use only exact-reference marginals.
The conditional KL and warm-transfer results are reused without strengthening
their hypotheses.
-/

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace AcceleratedLogConcave.Probability.Heterogeneous

universe u

variable {X : ℕ → Type u} [∀ n, MeasurableSpace (X n)]
  [∀ n, MeasurableSpace.CountablyGenerated (X n)]

/-- The extended-valued conditional path KL is exactly the sum of the local
KL costs averaged under the changing exact-reference laws. -/
theorem lintegral_klDiv_finiteHistoryKernel_eq_sum
    (μ : Measure (X 0)) (P Q : (j : ℕ) → Kernel (X j) (X (j + 1)))
    [∀ j, IsMarkovKernel (P j)] [∀ j, IsMarkovKernel (Q j)] (n : ℕ) :
    (∫⁻ x, klDiv (finiteHistoryKernel P n x) (finiteHistoryKernel Q n x) ∂μ) =
      ∑ j ∈ Finset.range n, ∫⁻ z, klDiv (P j z) (Q j z) ∂referenceLaw μ P j := by
  induction n with
  | zero => simp [finiteHistoryKernel]
  | succ n ih =>
    have hlocal := measurable_klDiv_kernel (P n) (Q n)
    have hstep (x : X 0) :
        klDiv (finiteHistoryKernel P (n + 1) x) (finiteHistoryKernel Q (n + 1) x) =
          klDiv (finiteHistoryKernel P n x) (finiteHistoryKernel Q n x) +
            ∫⁻ h, klDiv (P n (historyLast n h)) (Q n (historyLast n h))
              ∂finiteHistoryKernel P n x := by
      rw [finiteHistoryKernel_succ_apply, finiteHistoryKernel_succ_apply,
        klDiv_compProd_eq_add_lintegral]
      rfl
    simp_rw [hstep]
    rw [lintegral_add_left (measurable_klDiv_kernel
      (finiteHistoryKernel P n) (finiteHistoryKernel Q n))]
    rw [lintegral_finiteHistoryKernel_historyLast μ P n
      (fun z => klDiv (P n z) (Q n z)) hlocal]
    rw [ih, Finset.sum_range_succ]

/-- Conditional Pinsker and the supplied squared-L2 warmness bound control the
entire visible history, even when the state space changes at every step. -/
theorem totalVariationDistance_finiteHistoryLaw_le_sqrt_sum
    {μ ν : Measure (X 0)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B : ℝ} (hWarm : L2Warm μ ν B)
    (P Q : (j : ℕ) → Kernel (X j) (X (j + 1)))
    [∀ j, IsMarkovKernel (P j)] [∀ j, IsMarkovKernel (Q j)]
    (n : ℕ) (δ : ℕ → ℝ)
    (hδ : ∀ j < n, (∫⁻ x, klDiv (P j x) (Q j x) ∂referenceLaw μ P j) ≤
      ENNReal.ofReal (δ j ^ 2)) :
    totalVariationDistance (finiteHistoryLaw ν P n) (finiteHistoryLaw ν Q n) ≤
      Real.sqrt (B / 2 * ∑ j ∈ Finset.range n, δ j ^ 2) := by
  have hpath : (∫⁻ x, klDiv (finiteHistoryKernel P n x) (finiteHistoryKernel Q n x) ∂μ) ≤
      ENNReal.ofReal (∑ j ∈ Finset.range n, δ j ^ 2) := by
    rw [lintegral_klDiv_finiteHistoryKernel_eq_sum]
    calc
      _ ≤ ∑ j ∈ Finset.range n, ENNReal.ofReal (δ j ^ 2) :=
        Finset.sum_le_sum fun j hj => hδ j (Finset.mem_range.mp hj)
      _ = ENNReal.ofReal (∑ j ∈ Finset.range n, δ j ^ 2) :=
        (ENNReal.ofReal_sum_of_nonneg fun j _ => sq_nonneg (δ j)).symm
  exact totalVariationDistance_comp_le_sqrt_of_lintegral_kl μ ν
    (finiteHistoryKernel P n) (finiteHistoryKernel Q n) hWarm.1 B
    (∑ j ∈ Finset.range n, δ j ^ 2) (Finset.sum_nonneg fun j _ => sq_nonneg (δ j))
    hWarm.2.1 hWarm.2.2 (measurable_klDiv_kernel _ _).aemeasurable hpath

/-- The final-state comparison follows by the measurable last-state projection. -/
theorem totalVariationDistance_referenceLaw_le_sqrt_sum
    {μ ν : Measure (X 0)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B : ℝ} (hWarm : L2Warm μ ν B)
    (P Q : (j : ℕ) → Kernel (X j) (X (j + 1)))
    [∀ j, IsMarkovKernel (P j)] [∀ j, IsMarkovKernel (Q j)]
    (n : ℕ) (δ : ℕ → ℝ)
    (hδ : ∀ j < n, (∫⁻ x, klDiv (P j x) (Q j x) ∂referenceLaw μ P j) ≤
      ENNReal.ofReal (δ j ^ 2)) :
    totalVariationDistance (referenceLaw ν P n) (referenceLaw ν Q n) ≤
      Real.sqrt (B / 2 * ∑ j ∈ Finset.range n, δ j ^ 2) := by
  have h := (totalVariationDistance_map_le (finiteHistoryLaw ν P n)
    (finiteHistoryLaw ν Q n) (historyLast n) (measurable_historyLast n)).trans
      (totalVariationDistance_finiteHistoryLaw_le_sqrt_sum hWarm P Q n δ hδ)
  simpa only [finiteHistoryLaw_map_historyLast] using h

end AcceleratedLogConcave.Probability.Heterogeneous
