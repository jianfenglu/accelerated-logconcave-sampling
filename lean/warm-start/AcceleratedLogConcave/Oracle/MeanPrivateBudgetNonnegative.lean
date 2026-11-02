import AcceleratedLogConcave.Oracle.MeanIncomingPrivateAccuracy

/-! Sign of the actual finite private RMS payment. No accuracy premise or
resolution restriction is needed: every initializer, residual, lower-error
norm and quadrature contribution is nonnegative. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
open scoped BigOperators NNReal
namespace AcceleratedLogConcave.Oracle.MeanPrivateBudgetNonnegative
open Numerics Numerics.AffineGraph
variable {d m n : ℕ} (M : MeanGeometry m)
  (mesh : IntervalMesh 0 (samplingEnd (M.R/backwardEnd M.R)))
  (e : Fin n ≃ (RecursiveExecutable.privateGeometry M mesh).Node)
  (r : ℝ) (hr : 0<r) (N : ℕ)
  {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0≤ell)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ F) z v v≤ell*‖v‖^2)

/-- The complete finite private budget is nonnegative for arbitrary LOWER
amplitudes, since they enter through their actual L2 payments. -/
theorem privateBudget_nonneg (base : Point d) (κ κf : ℝ≥0)
    (amplitude : ℕ → Fin n → ℝ) (amplitudeF : Fin n → ℝ) :
    0≤MeanIncomingPrivateAccuracy.privateBudget M mesh e r hr N hF hell hlo hup base κ κf amplitude amplitudeF := by
  let S := RecursiveExecutable.privateGeometry M mesh
  let flowData := PrivateSamplingOriginalBounds.data S r hF hell hlo hup hr
  have hcell : 0≤AffineResidual.cellBudget S.mesh m
      (SamplingGaussianJetLp.cellDerivativeBudget flowData S.mesh m) := by
    unfold AffineResidual.cellBudget
    apply Finset.sum_nonneg
    intro c _
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (S.mesh.length_pos c).le _))
      (SamplingGaussianJetLp.cellDerivativeBudget_nonneg flowData S.mesh m c)) (Nat.cast_nonneg _)
  unfold MeanIncomingPrivateAccuracy.privateBudget PrivateCompletedRms.mainBudget
    PrivateCompletedRms.initializerBudget PrivateCompletedRms.quadratureBudget Collocation.forcingSum
    SharedLayerRms.childRowBudget PrivateCompletedRms.childPayment
  positivity [hcell,S.samplingEnd_pos,PrivateSamplingOriginalBounds.replyBudget_nonneg flowData base,
    PrivateCompletedRms.residualBudget_nonneg S r hr hF hell hlo hup]

/-- The source's actual backward-end scaling keeps the payment nonnegative. -/
theorem scaled_privateBudget_nonneg (base : Point d) (κ κf : ℝ≥0)
    (amplitude : ℕ → Fin n → ℝ) (amplitudeF : Fin n → ℝ) :
    0≤backwardEnd M.R*MeanIncomingPrivateAccuracy.privateBudget M mesh e r hr N hF hell hlo hup base κ κf amplitude amplitudeF :=
  mul_nonneg M.backwardEnd_pos.le
    (privateBudget_nonneg M mesh e r hr N hF hell hlo hup base κ κf amplitude amplitudeF)

end AcceleratedLogConcave.Oracle.MeanPrivateBudgetNonnegative
