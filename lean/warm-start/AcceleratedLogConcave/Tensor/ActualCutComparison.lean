import AcceleratedLogConcave.Tensor.ActualCoefficientAssembly
import AcceleratedLogConcave.Tensor.DistinguishedOutputLift
import AcceleratedLogConcave.Tensor.ActualForcingCuts

/-!

-/
noncomputable section
set_option autoImplicit false
open Set
open scoped ContDiff BigOperators Classical
namespace AcceleratedLogConcave.Tensor.ActualCoefficient
open Conditional Conditional.Transport.SpatialFlow
open AcceleratedLogConcave.Analysis.SpatialPartition
open OutputLift
variable {D n : ℕ}

abbrev actualTopDerivative (d : PositiveVarianceFlowData (Space D))
    (y : Space D) (s : ℝ) :=
  fderiv ℝ (probabilityVelocity d.F d.x d.r s) (actualY d s y)

abbrev actualForcingCoeff (d : PositiveVarianceFlowData (Space D))
    (n : ℕ) (hn : 0 < n) (y : Space D) (s : ℝ) :=
  vectorCoeff (spatialForcing (probabilityVelocity d.F d.x d.r s) (actualY d s) y n hn)

theorem vectorCoeff_add {I : Type*} [Fintype I] [DecidableEq I]
    (T U : ContinuousMultilinearMap ℝ (fun _ : I => Space D) (Space D)) :
    vectorCoeff (T + U) = vectorCoeff T + vectorCoeff U := by
  ext a
  simp [vectorCoeff,mapCoeff,inner_add_right]

/-- The actual chain rule is converted to the exact labeled output action.
Neither the top identification nor the partition equality is hypothesized. -/
theorem actualRHS_separated
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (n : ℕ) (hn : 0 < n) (y : Space D) {s : ℝ} (hs : s ∈ Icc 0 d.b) :
    actualRHSCoeff d n y s =
      outputAction (.inr ()) (derivativeMatrix (actualTopDerivative d y s))
        (actualJetCoeff d n y s) + actualForcingCoeff d n hn y s := by
  have he := iteratedFDeriv_comp_separated (x := y)
    (contDiff_probabilityVelocity_spatial d.hF d.hlo d.hhi d.x
      (r := d.r) (by linarith [hs.1]) (hs.2.trans_lt d.hb1)).contDiffAt
    (contDiff_backward_spatial d.hF d.hell d.hlo d.hhi d.x
      d.hr d.hb0 d.hb1 hsmall hs).contDiffAt n hn
  change vectorCoeff (iteratedFDeriv ℝ n
    ((probabilityVelocity d.F d.x d.r s) ∘ actualY d s) y) = _
  rw [he,vectorCoeff_add,← outputAction_vectorCoeff]

/-- Exact row-operator identity for the actual full RHS. -/
theorem actualRHS_row_operator
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (n : ℕ) (hn : 0 < n) (y : Space D) (S : Finset (Fin n ⊕ Unit))
    (ho : (.inr () : Fin n ⊕ Unit) ∈ S) {s : ℝ} (hs : s ∈ Icc 0 d.b) :
    splitOperatorEquiv D S (actualRHSCoeff d n y s) =
      (rowLift S (.inr ()) ho (derivativeMatrix (actualTopDerivative d y s))).comp
        (splitOperatorEquiv D S (actualJetCoeff d n y s)) +
      splitOperatorEquiv D S (actualForcingCoeff d n hn y s) := by
  rw [actualRHS_separated d hsmall n hn y hs,map_add,
    outputAction_row_operator S (.inr ()) ho]

/-- Exact column-operator identity: the transpose acts on the RIGHT. -/
theorem actualRHS_column_operator
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (n : ℕ) (hn : 0 < n) (y : Space D) (S : Finset (Fin n ⊕ Unit))
    (ho : (.inr () : Fin n ⊕ Unit) ∉ S) {s : ℝ} (hs : s ∈ Icc 0 d.b) :
    splitOperatorEquiv D S (actualRHSCoeff d n y s) =
      (splitOperatorEquiv D S (actualJetCoeff d n y s)).comp
        (columnLift S (.inr ()) ho (derivativeMatrix (actualTopDerivative d y s))) +
      splitOperatorEquiv D S (actualForcingCoeff d n hn y s) := by
  rw [actualRHS_separated d hsmall n hn y hs,map_add,
    outputAction_column_operator S (.inr ()) ho]

/-- Original-flow fixed-cut comparison with precisely the genuine remaining
quantitative suppliers. No continuity/Volterra/lift equality premise remains. -/
theorem actual_fixed_cut_bound_of_primitive_and_forcing
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (n : ℕ) (hn : 0 < n) (y : Space D) (S : Finset (Fin n ⊕ Unit))
    {α δ : ℝ} {f : ℝ → ℝ} (hα : 0 ≤ α) (hf : Continuous f)
    (hb : splitNorm D S (actualJetCoeff d n y d.b) ≤ δ)
    (hDv : ∀ s ∈ Icc 0 d.b, ‖actualTopDerivative d y s‖ ≤ α*s)
    (hforcing : ∀ s ∈ Icc 0 d.b, splitNorm D S (actualForcingCoeff d n hn y s) ≤ f s)
    {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    splitNorm D S (actualJetCoeff d n y t) ≤
      AcceleratedLogConcave.Analysis.FixedCut.envelope α d.b δ f t := by
  apply actual_fixed_cut_bound d hsmall n y S hα hf hb ?_ ht
  intro s hs
  rw [actualRHS_separated d hsmall n hn y hs]
  exact (splitNorm_add_le D S _ _).trans (add_le_add
    ((outputAction_splitNorm_le S (.inr ()) (actualTopDerivative d y s)
      (actualJetCoeff d n y s)).trans
      (mul_le_mul_of_nonneg_right (hDv s hs) (splitNorm_nonneg D S _)))
    (hforcing s hs))
end AcceleratedLogConcave.Tensor.ActualCoefficient
