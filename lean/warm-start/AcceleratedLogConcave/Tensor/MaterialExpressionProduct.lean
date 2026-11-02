import AcceleratedLogConcave.Tensor.MaterialLeafExpansion

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff BigOperators
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open Conditional Analysis Analysis.CoupledVelocityPolynomial CoordinateReduction

/-- Literal space-time interpretation, with the original evolving law. -/
def materialExpressionValue {D r : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (e : Expr signature r) (a : Fin r → Fin D)
    (p : ℝ × EuclideanSpace ℝ (Fin D)) : ℝ :=
  Expr.evaluate (coefficientEnvironment d.F d.x d.ell d.r p.1)
    (interpolationPotential d.F d.x d.r p.1) e p.2 a

theorem contDiffOn_material_jet_coefficient {D : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D))) (n : ℕ)
    (a : Fin (n+2) → Fin D) :
    ContDiffOn ℝ ∞ (materialExpressionValue d (.coefficient (Sum.inl n)) a)
      (openDomain (EuclideanSpace ℝ (Fin D))) := by
  change ContDiffOn ℝ ∞ (fun p =>
    (d.ell*d.r*((n+1).factorial:ℝ))⁻¹ *
      d.scaledJetCoordinate (n+1) (coordinateDirection D (a 0))
        (fun i => coordinateDirection D (a i.succ)) p) _
  exact contDiffOn_const.mul (d.contDiffOn_scaledJetCoordinate _ _ _)

theorem material_expression_permute {D r : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (e : Expr signature r) (π : Equiv.Perm (Fin r)) (a : Fin r → Fin D)
    (p : ℝ × EuclideanSpace ℝ (Fin D)) :
    materialDerivative d.materialVelocity (materialExpressionValue d (.permute π e) a) p =
      materialDerivative d.materialVelocity (materialExpressionValue d e (a ∘ π)) p := rfl

/-- Ordinary product rule on the literal finite coordinate contraction.
Regularity premises are local induction hypotheses, not final data assumptions. -/
theorem material_expression_contract {D r s : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (e : Expr signature (r+2)) (f : Expr signature (s+2))
    (i : Fin (r+2)) (j : Fin (s+2)) (a : Fin (r+s+2) → Fin D)
    (p : ℝ × EuclideanSpace ℝ (Fin D))
    (he : ∀ b, DifferentiableAt ℝ (materialExpressionValue d e b) p)
    (hf : ∀ b, DifferentiableAt ℝ (materialExpressionValue d f b) p) :
    materialDerivative d.materialVelocity (materialExpressionValue d (.contract e f i j) a) p =
      ∑ k : Fin D,
        (materialDerivative d.materialVelocity
            (materialExpressionValue d e (leftAssignment i a k)) p *
          materialExpressionValue d f (rightAssignment j a k) p +
        materialExpressionValue d e (leftAssignment i a k) p *
          materialDerivative d.materialVelocity
            (materialExpressionValue d f (rightAssignment j a k)) p) := by
  have hh := HasFDerivAt.fun_sum (fun k (_ : k ∈ Finset.univ) =>
    (he (leftAssignment i a k)).hasFDerivAt.mul
      (hf (rightAssignment j a k)).hasFDerivAt)
  change HasFDerivAt (materialExpressionValue d (.contract e f i j) a) _ p at hh
  unfold materialDerivative
  rw [hh.fderiv]
  simp [smul_eq_mul, mul_comm, add_comm]

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
