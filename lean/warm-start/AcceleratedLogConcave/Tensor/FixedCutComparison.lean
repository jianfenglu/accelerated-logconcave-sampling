import AcceleratedLogConcave.Analysis.BackwardComparison
import AcceleratedLogConcave.Tensor.SplitNorm

/-!

-/
noncomputable section
open Set MeasureTheory
namespace AcceleratedLogConcave.Tensor.FixedCut
open AcceleratedLogConcave.Analysis.FixedCut
variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot] {D : ℕ}

/-- Finite dimensionality is used only for continuity of a fixed linear map.
Its operator norm is NEVER inserted into a quantitative estimate. -/
def unfoldCLM (S : Finset Slot) :
    Coeff Slot D →L[ℝ] (RightHilbert D S →L[ℝ] LeftHilbert D S) :=
  (splitOperatorEquiv D S).toLinearMap.toContinuousLinearMap

 theorem fixed_cut_linear_time_bound (S : Finset Slot)
    {T T' : ℝ → Coeff Slot D} {f : ℝ → ℝ} {α b δ : ℝ}
    (hα : 0 ≤ α) (hf : Continuous f)
    (hT : ContinuousOn T (Icc 0 b))
    (hT' : ∀ s ∈ Icc 0 b, HasDerivWithinAt T (T' s) (Icc 0 b) s)
    (hb : splitNorm D S (T b) ≤ δ)
    (hbound : ∀ s ∈ Icc 0 b,
      splitNorm D S (T' s) ≤ α*s*splitNorm D S (T s) + f s)
    {t : ℝ} (ht : t ∈ Icc 0 b) :
    splitNorm D S (T t) ≤ envelope α b δ f t := by
  exact backward_linear_time_bound hα hf
    ((unfoldCLM S).continuous.comp_continuousOn hT)
    (fun s hs => (unfoldCLM S).hasFDerivAt.comp_hasDerivWithinAt s (hT' s hs))
    hb hbound ht

/-- Genuine integral-input version. Continuity supplies integrability and FTC;
there is no integrability assumption obtained from the desired norm bound.
A globally continuous representative Q suffices; T need only agree on the slab. -/
theorem fixed_cut_volterra_bound (S : Finset Slot)
    {T Q : ℝ → Coeff Slot D} {f : ℝ → ℝ} {α b δ : ℝ}
    (hα : 0 ≤ α) (hf : Continuous f) (hQ : Continuous Q)
    (hvol : ∀ s ∈ Icc 0 b, T s = T b - ∫ u in s..b, Q u)
    (hb : splitNorm D S (T b) ≤ δ)
    (hbound : ∀ s ∈ Icc 0 b,
      splitNorm D S (Q s) ≤ α*s*splitNorm D S (T s) + f s)
    {t : ℝ} (ht : t ∈ Icc 0 b) :
    splitNorm D S (T t) ≤ envelope α b δ f t := by
  have hd (s : ℝ) : HasDerivAt (fun v => T b - ∫ u in v..b, Q u) (Q s) s := by
    have hi := intervalIntegral.integral_hasDerivAt_left (hQ.intervalIntegrable s b)
      hQ.aestronglyMeasurable.stronglyMeasurableAtFilter hQ.continuousAt
    convert (hasDerivAt_const s (T b)).sub hi using 1
    simp
  have hT' (s : ℝ) (hs : s ∈ Icc 0 b) :
      HasDerivWithinAt T (Q s) (Icc 0 b) s :=
    (hd s).hasDerivWithinAt.congr_of_mem (fun u hu => hvol u hu) hs
  exact fixed_cut_linear_time_bound S hα hf
    (fun s hs => (hT' s hs).continuousWithinAt) hT' hb hbound ht

/-- Output in row: top-order multiplication is on the left. -/
theorem left_top_bound {R C : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    (L : R →L[ℝ] R) (X F : C →L[ℝ] R) {a f : ℝ}
    (hL : ‖L‖ ≤ a) (hF : ‖F‖ ≤ f) : ‖L.comp X + F‖ ≤ a*‖X‖ + f := by
  exact (norm_add_le _ _).trans (add_le_add
    ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right hL (norm_nonneg _))) hF)

/-- Output in column: the transpose-lifted output map acts on the right.
No dimension/nonzero-space hypothesis is needed for this operator inequality. -/
theorem right_top_bound {R C : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    (L : C →L[ℝ] C) (X F : C →L[ℝ] R) {a f : ℝ}
    (hL : ‖L‖ ≤ a) (hF : ‖F‖ ≤ f) : ‖X.comp L + F‖ ≤ a*‖X‖ + f := by
  apply (norm_add_le _ _).trans
  apply add_le_add _ hF
  calc ‖X.comp L‖ ≤ ‖X‖*‖L‖ := ContinuousLinearMap.opNorm_comp_le _ _
       _ ≤ ‖X‖*a := mul_le_mul_of_nonneg_left hL (norm_nonneg _)
       _ = a*‖X‖ := mul_comm _ _

end AcceleratedLogConcave.Tensor.FixedCut
