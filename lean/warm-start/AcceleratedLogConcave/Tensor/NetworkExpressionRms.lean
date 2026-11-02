import AcceleratedLogConcave.Tensor.NetworkExpansionIntegralBound
import AcceleratedLogConcave.Tensor.NetworkMatrixSyntax
import AcceleratedLogConcave.Tensor.MaterialRmsBudget

noncomputable section
open MeasureTheory
open scoped Classical BigOperators
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction ReductionRecords ActualCoefficientIntegrability Conditional
open Analysis.PositiveVarianceSlab

/-- Original-data second moment for one whole material rank-two expression.
The proof retains its matrix-square circuit and the literal expansion-list multiplicity. -/
theorem expression_integral_norm_sq_le {D : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D))) (hsmall : d.r^2*d.ell ≤ 1/2)
    (e : Expr signature 2) (he : IsMaterialExpression e)
    {t : ℝ} (ht : t ∈ Set.Icc (left d.b) (right d.b)) :
    (∫ y, ‖Expr.evaluate (coefficientEnvironment d.F d.x d.ell d.r t)
      (interpolationPotential d.F d.x d.r t) e y‖^2 ∂interpolationLaw d.F d.x d.r t) ≤
      materialRmsNumeric D e.size * (Real.sqrt (conditionalVariance t))^(-2*(e.weight:ℝ)) := by
  let values : OriginValues Unit Unit := ⟨fun _ => (),fun _ => ()⟩
  let s := initialTwoFormulas e e 0 0
  have hs := initialTwoFormulas_support_nodup e e 0 0
  have hi := initialTwoFormulas_inventory_nodup e e 0 0
  let tree := ExpansionTree.build s hs hi
  have h := expansion_integral_abs_bound d hsmall values ht tree (matrixSyntaxState e) hs hi
    (initialTwoFormulas_isMaterial e e he he 0 0)
  have ht' := construction_subset d.hb0 d.hb1 ht
  have hv : 0 < conditionalVariance t := conditionalVariance_pos ht'.1 ht'.2
  have hR1 : Real.sqrt (conditionalVariance t) ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    simp only [conditionalVariance]
    nlinarith [sq_nonneg t]
  have hb := terminalBranches_budgetProduct_sum_le e 0 values
    (Real.sqrt (conditionalVariance t)) (Real.sqrt_pos.mpr hv) hR1
  have hm := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg D : (0:ℝ) ≤ D)
  have hcombined := h.trans hm
  have hvalue : (matrixSyntaxState e).actualIntegral d t =
      ∫ y, ‖Expr.evaluate (coefficientEnvironment d.F d.x d.ell d.r t)
        (interpolationPotential d.F d.x d.r t) e y‖^2 ∂interpolationLaw d.F d.x d.r t := by
    apply integral_congr_ae
    filter_upwards [] with y
    exact matrixSyntaxState_value _ _ e y
  rw [hvalue] at hcombined
  apply (le_abs_self _).trans
  convert hcombined using 1
  simp only [materialRmsNumeric,Nat.cast_zero,add_zero,neg_mul]
  ring

end AcceleratedLogConcave.Tensor.Ordered.Graph
