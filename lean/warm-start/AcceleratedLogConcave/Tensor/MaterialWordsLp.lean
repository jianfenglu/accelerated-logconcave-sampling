import AcceleratedLogConcave.Tensor.MaterialExpressionLp
import AcceleratedLogConcave.Tensor.MaterialTensorNorm
import AcceleratedLogConcave.Conditional.Flow.MaterialTrajectoryLaw

noncomputable section
open scoped BigOperators
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open Conditional Analysis Analysis.PositiveVarianceSlab Analysis.OrderedJacobianWords MeasureTheory Set
variable {D : ℕ} (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))

/-- All inherited words, with their original multiplicities and physical factor. -/
theorem actualWordsLp_norm_le (hsmall : d.r^2*d.ell ≤ 1/2)
    (m : ℕ) (hm : 0<m) {t M : ℝ}
    (ht : t ∈ Icc (left d.b) (right d.b)) (htabs : |t|≤1) (hM0 : 0≤M)
    (hM : ∀ u ∈ materialWordsTerms (d.ell*d.r^2) m,
      ‖actualExpressionLp d u.expression ht‖ ≤ M) :
    ‖actualTermsLp d (materialWordsTerms (d.ell*d.r^2) m) ht‖ ≤
      ((d.ell*d.r^2)*(m.factorial:ℝ)*(materialWordMassBase m)^m)*M := by
  exact (actualTermsLp_norm_le d _ ht htabs hM).trans
    (mul_le_mul_of_nonneg_right (actual_materialWordsTerms_mass d hsmall m hm) hM0)

/-- Exact inverse-law change of variables for the actual full C-word tensor. -/
theorem actual_wordSum_integral_norm_sq (m : ℕ) (hm : 0<m) {t : ℝ}
    (ht : t ∈ Icc 0 d.b) :
    (∫ y, ‖operatorTensor (evaluateSum (fun j u => d.jacobianCoefficientJet j u y)
      (words m) t)‖^2 ∂interpolationLaw d.F d.x d.r d.b) =
    ∫ y, ‖materialTermsTensor d (materialWordsTerms (d.ell*d.r^2) m) t y‖^2
      ∂interpolationLaw d.F d.x d.r t := by
  have hti := source_subset d.hb0 d.hb1 ht
  have hp := d.state_fst_measurePreserving ht
  have ha := (actualTerms_memLp d (materialWordsTerms (d.ell*d.r^2) m)
    ⟨hti.1.le,hti.2.le⟩).aestronglyMeasurable.norm.pow 2
  have hmap := integral_map hp.measurable.aemeasurable (hp.map_eq.symm ▸ ha)
  rw [hp.map_eq] at hmap
  calc
    _ = ∫ y, ‖materialTermsTensor d (materialWordsTerms (d.ell*d.r^2) m) t
        (d.state t y).fst‖^2 ∂interpolationLaw d.F d.x d.r d.b := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [actual_wordSum_tensor_expansion d m hm hti y]
    _ = _ := hmap.symm

/-- Quantitative word receiver with only the whole-expression moment supplier open. -/
theorem actual_wordSum_integral_norm_sq_le (hsmall : d.r^2*d.ell ≤ 1/2)
    (m : ℕ) (hm : 0<m) {t M : ℝ} (ht : t ∈ Icc 0 d.b) (hM0 : 0≤M)
    (hM : ∀ u ∈ materialWordsTerms (d.ell*d.r^2) m,
      (∫ y, ‖Expr.evaluate (coefficientEnvironment d.F d.x d.ell d.r t)
        (interpolationPotential d.F d.x d.r t) u.expression y‖^2
        ∂interpolationLaw d.F d.x d.r t) ≤ M^2) :
    (∫ y, ‖operatorTensor (evaluateSum (fun j u => d.jacobianCoefficientJet j u y)
      (words m) t)‖^2 ∂interpolationLaw d.F d.x d.r d.b) ≤
      (((d.ell*d.r^2)*(m.factorial:ℝ)*(materialWordMassBase m)^m)*M)^2 := by
  rw [actual_wordSum_integral_norm_sq d m hm ht]
  have hti := source_subset d.hb0 d.hb1 ht
  have htabs : |t|≤1 := by rw [abs_of_nonneg ht.1]; linarith [ht.2,d.hb1]
  have hh := actualTerms_integral_norm_sq_le d _ ⟨hti.1.le,hti.2.le⟩ htabs hM0 hM
  have hmass := mul_le_mul_of_nonneg_right (actual_materialWordsTerms_mass d hsmall m hm) hM0
  have hn := mul_nonneg (materialMass_nonneg (materialWordsTerms (d.ell*d.r^2) m)) hM0
  nlinarith

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
