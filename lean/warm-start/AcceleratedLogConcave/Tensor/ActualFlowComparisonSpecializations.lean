import AcceleratedLogConcave.Tensor.ActualCutComparison

/-!

-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped BigOperators Classical
namespace AcceleratedLogConcave.Tensor.ActualCoefficient
open Conditional Conditional.Transport.SpatialFlow
open AcceleratedLogConcave.Analysis.SpatialPartition
open AcceleratedLogConcave.Analysis.FixedCut
open OutputLift
variable {D : ℕ}

 theorem actual_unfolded_dynamics
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (n : ℕ) (hn : 0 < n) (y : Space D) (S : Finset (Fin n ⊕ Unit))
    {α : ℝ} (hDv : ∀ s ∈ Icc 0 d.b, ‖actualTopDerivative d y s‖ ≤ α*s) :
    ∃ Q : ℝ → (RightHilbert D S →L[ℝ] LeftHilbert D S),
      ContinuousOn (fun s => splitOperatorEquiv D S (actualJetCoeff d n y s)) (Icc 0 d.b) ∧
      (∀ s ∈ Icc 0 d.b, HasDerivWithinAt
        (fun u => splitOperatorEquiv D S (actualJetCoeff d n y u)) (Q s) (Icc 0 d.b) s) ∧
      (∀ s ∈ Icc 0 d.b, ‖Q s‖ ≤
        α*s*splitNorm D S (actualJetCoeff d n y s) +
          splitNorm D S (actualForcingCoeff d n hn y s)) := by
  obtain ⟨R,hR,he,hvol⟩ := exists_actual_coefficient_volterra d hsmall n y
  have hd (s : ℝ) : HasDerivAt
      (fun v => actualJetCoeff d n y d.b - ∫ u in v..d.b, R u) (R s) s := by
    have hi := intervalIntegral.integral_hasDerivAt_left (hR.intervalIntegrable s d.b)
      hR.aestronglyMeasurable.stronglyMeasurableAtFilter hR.continuousAt
    convert (hasDerivAt_const s (actualJetCoeff d n y d.b)).sub hi using 1
    simp
  have hT (s : ℝ) (hs : s ∈ Icc 0 d.b) :
      HasDerivWithinAt (actualJetCoeff d n y) (R s) (Icc 0 d.b) s :=
    (hd s).hasDerivWithinAt.congr_of_mem (fun u hu => hvol u hu) hs
  have hX (s : ℝ) (hs : s ∈ Icc 0 d.b) :
      HasDerivWithinAt (fun u => splitOperatorEquiv D S (actualJetCoeff d n y u))
        (FixedCut.unfoldCLM S (R s)) (Icc 0 d.b) s :=
    (FixedCut.unfoldCLM S).hasFDerivAt.comp_hasDerivWithinAt s (hT s hs)
  refine ⟨fun s => FixedCut.unfoldCLM S (R s),
    fun s hs => (hX s hs).continuousWithinAt,hX,?_⟩
  intro s hs
  change splitNorm D S (R s) ≤ _
  rw [he s hs, actualRHS_separated d hsmall n hn y hs]
  exact (splitNorm_add_le D S _ _).trans (add_le_add
    ((outputAction_splitNorm_le S (.inr ()) (actualTopDerivative d y s)
      (actualJetCoeff d n y s)).trans
      (mul_le_mul_of_nonneg_right (hDv s hs) (splitNorm_nonneg D S _))) le_rfl)

 theorem actual_first_cut_homogeneous
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (y : Space D) (S : Finset (Fin 1 ⊕ Unit)) {α : ℝ} (hα : 0 ≤ α)
    (hb : splitNorm D S (actualJetCoeff d 1 y d.b) ≤ 1)
    (hDv : ∀ s ∈ Icc 0 d.b, ‖actualTopDerivative d y s‖ ≤ α*s)
    {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    splitNorm D S (actualJetCoeff d 1 y t) ≤ Real.exp (α*(d.b^2-t^2)/2) := by
  obtain ⟨Q,hX,hX',hbound⟩ := actual_unfolded_dynamics d hsmall 1 (by omega) y S hDv
  have hf (s : ℝ) : actualForcingCoeff d 1 (by omega) y s = 0 := by
    ext a
    simp [actualForcingCoeff, ActualPartitionTree.spatialForcing_one, vectorCoeff, mapCoeff]
  have h := backward_homogeneous_bound hα hX hX' hb
    (fun s hs => by simpa [hf s, splitNorm] using hbound s hs) ht
  simpa only [one_mul, splitNorm] using h

 theorem actual_cut_proportional
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (n : ℕ) (hn : 0 < n) (y : Space D) (S : Finset (Fin n ⊕ Unit))
    {α C : ℝ} (hα : 0 ≤ α)
    (hb : splitNorm D S (actualJetCoeff d n y d.b) = 0)
    (hDv : ∀ s ∈ Icc 0 d.b, ‖actualTopDerivative d y s‖ ≤ α*s)
    (hforcing : ∀ s ∈ Icc 0 d.b,
      splitNorm D S (actualForcingCoeff d n hn y s) ≤ α*s*C)
    {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    splitNorm D S (actualJetCoeff d n y t) ≤ C*(Real.exp (α*(d.b^2-t^2)/2)-1) := by
  obtain ⟨Q,hX,hX',hbound⟩ := actual_unfolded_dynamics d hsmall n hn y S hDv
  apply backward_proportional_forcing hα hX hX'
    (norm_eq_zero.mp hb) ?_ ht
  intro s hs
  exact (hbound s hs).trans (add_le_add le_rfl (hforcing s hs))

end AcceleratedLogConcave.Tensor.ActualCoefficient
