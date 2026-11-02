import AcceleratedLogConcave.Tensor.MaterialVectorNorm

noncomputable section
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open Conditional Analysis Analysis.PositiveVarianceSlab MeasureTheory Set
variable {D : ℕ} (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))

/-- Actual position-jet L2 receiver; individual vector expression moments remain explicit. -/
theorem positionJetLp_norm_le_expressionRMS (k : ℕ) {t M : ℝ}
    (ht : t ∈ Icc 0 d.b) (hM0 : 0≤M)
    (hM : ∀ u ∈ materialIterate (d.ell*d.r^2) materialMeanExpr k,
      (∫ y, ‖Expr.evaluate (coefficientEnvironment d.F d.x d.ell d.r t)
        (interpolationPotential d.F d.x d.r t) u.expression y‖^2
        ∂interpolationLaw d.F d.x d.r t) ≤ M^2) :
    ‖d.positionJetLp (k+2) t‖ ≤ (d.ell*d.r^2) *
      (materialMass (materialIterate (d.ell*d.r^2) materialMeanExpr k)*M) := by
  have hti := source_subset d.hb0 d.hb1 ht
  have htabs : |t|≤1 := by rw [abs_of_nonneg ht.1]; linarith [ht.2,d.hb1]
  have hh := actualVectorTerms_integral_norm_sq_le d _ ⟨hti.1.le,hti.2.le⟩ htabs hM0 hM
  have hsq : ‖d.positionJetLp (k+2) t‖^2 ≤
      ((d.ell*d.r^2) * (materialMass (materialIterate (d.ell*d.r^2) materialMeanExpr k)*M))^2 := by
    rw [show ‖d.positionJetLp (k+2) t‖^2 =
      ∫ y, ‖d.positionJet (k+2) t y‖^2 ∂d.positionMeasure from
      DominatedLp.norm_sq_toLp (d.positionJet_memLp (k+2) t)]
    rw [positionJet_integral_norm_sq d k ht]
    calc
      _ ≤ (d.ell*d.r^2)^2 * (materialMass (materialIterate (d.ell*d.r^2) materialMeanExpr k)*M)^2 :=
        mul_le_mul_of_nonneg_left hh (sq_nonneg (d.ell*d.r^2))
      _ = _ := by ring
  have hc : 0≤d.ell*d.r^2 := mul_nonneg d.hell (sq_nonneg _)
  have hm := mul_nonneg (materialMass_nonneg (materialIterate (d.ell*d.r^2) materialMeanExpr k)) hM0
  nlinarith [norm_nonneg (d.positionJetLp (k+2) t),mul_nonneg hc hm]

 theorem positionJetLp_norm_le_massBudget (hsmall : d.r^2*d.ell ≤ 1/2)
    (k : ℕ) {t M : ℝ} (ht : t ∈ Icc 0 d.b) (hM0 : 0≤M)
    (hM : ∀ u ∈ materialIterate (d.ell*d.r^2) materialMeanExpr k,
      (∫ y, ‖Expr.evaluate (coefficientEnvironment d.F d.x d.ell d.r t)
        (interpolationPotential d.F d.x d.r t) u.expression y‖^2
        ∂interpolationLaw d.F d.x d.r t) ≤ M^2) :
    ‖d.positionJetLp (k+2) t‖ ≤ (d.ell*d.r^2) * ((3*(3+3*(k:ℝ)+1)^2)^k*M) := by
  apply (positionJetLp_norm_le_expressionRMS d k ht hM0 hM).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg d.hell (sq_nonneg _))
  apply mul_le_mul_of_nonneg_right _ hM0
  simpa only [materialMeanExpr_size,Nat.cast_ofNat] using
    actual_materialIterate_mass d hsmall materialMeanExpr k

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
