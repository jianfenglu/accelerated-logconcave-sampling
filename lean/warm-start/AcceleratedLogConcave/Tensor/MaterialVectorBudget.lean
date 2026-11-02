import AcceleratedLogConcave.Tensor.MaterialMeanLp
import AcceleratedLogConcave.Tensor.NetworkVectorRms

noncomputable section
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open Conditional Analysis Analysis.PositiveVarianceSlab MeasureTheory Set

/-- Exact original-data vector moments for all terms in the actual mean expansion. -/
theorem materialMean_expression_moment_variance {D : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (hsmall : d.r^2*d.ell ≤ 1/2) (k : ℕ) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    ∀ u ∈ materialIterate (d.ell*d.r^2) materialMeanExpr k,
      (∫ y, ‖Expr.evaluate (coefficientEnvironment d.F d.x d.ell d.r t)
        (interpolationPotential d.F d.x d.r t) u.expression y‖^2
        ∂interpolationLaw d.F d.x d.r t) ≤
      (Real.sqrt (materialRmsNumeric D (3+3*k)) / (1-t^2)^(k+1))^2 := by
  have hti := source_subset d.hb0 d.hb1 ht
  have hv : 0<conditionalVariance t := conditionalVariance_pos (by linarith [ht.1])
    (by linarith [ht.2,d.hb1])
  have hR1 : Real.sqrt (conditionalVariance t)≤1 := by
    apply Real.sqrt_le_one.mpr
    simp only [conditionalVariance]
    nlinarith [sq_nonneg t]
  intro u hu
  have he := materialIterate_isMaterial (d.ell*d.r^2) materialMeanExpr
    (by simp [materialMeanExpr,IsMaterialExpression]) k u hu
  have hs := (materialIterate_size_degree (d.ell*d.r^2) materialMeanExpr k u hu).1
  rw [materialMeanExpr_size] at hs
  have hw := materialIterate_weight (d.ell*d.r^2) materialMeanExpr k u hu
  rw [materialMeanExpr_weight] at hw
  have hw' : (u.expression.weight:ℝ)≤2*((k+1:ℕ):ℝ) := by
    have hh : (u.expression.weight:ℝ)≤1+2*(k:ℝ) := by exact_mod_cast hw
    push_cast
    linarith
  have hh := (Ordered.Graph.expression_vector_integral_norm_sq_le d hsmall u.expression he
    ⟨hti.1.le,hti.2.le⟩).trans
      (materialRmsBudget_mono D hs (by omega) hw' (Real.sqrt_pos.2 hv) hR1)
  have hexp : -2*(2*((k+1:ℕ):ℝ)) = -4*((k+1:ℕ):ℝ) := by ring
  rw [hexp,sqrtVariance_rpow_budget hv.le] at hh
  convert hh using 1
  rw [div_pow,Real.sq_sqrt (materialRmsNumeric_nonneg D (3+3*k))]
  simp [conditionalVariance,div_eq_mul_inv]

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
