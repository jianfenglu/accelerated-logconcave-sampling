import AcceleratedLogConcave.Tensor.NetworkVectorAdjointState
import AcceleratedLogConcave.Tensor.PhaseAnalyticEnvironment

noncomputable section
open MeasureTheory
open scoped Classical BigOperators ContDiff
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name}

def phaseVectorAdjointOperand {D : ℕ} (ρ : CoefficientEnvironment σ D)
    (H : EuclideanSpace ℝ (Fin D) → ℝ) (E : Expr σ 2) (i : Fin 2)
    (y : EuclideanSpace ℝ (Fin D)) (k : Fin D) : Coeff (vectorSquareGraph.Slot 0) D :=
  WithLp.toLp 2 (fun a => Expr.evaluate ρ H E y
    (Fin.insertNth i k (fun _ => a (vectorSquareSlot 0))))

/-- Exact original-law first IBP of a literal vector adjoint square. The right
side is the actual derivative-recipient family, not a supplied equality witness. -/
theorem phase_integral_vectorAdjoint_square {D : ℕ}
    (P : PhaseAnalyticEnvironment σ D)
    (E : Expr σ 2) (i : Fin 2) :
    let ρ := P.coefficients
    let H := P.potential
    let T := fun y => vectorSquareFamily (Expr.evaluate ρ H (.adjoint i E) y)
    let A := phaseVectorAdjointOperand ρ H E i
    (∫ y, ‖Expr.evaluate ρ H (.adjoint i E) y‖^2
      ∂P.toSmoothGibbsEnvironment.law) =
      ∑ q : {v : Fin 2 // v ≠ 0}, ∫ y,
        (vectorSquareGraph.recipientGraph 0 q.val (Ne.symm q.property)).coordinateEval D
          (vectorSquareGraph.principalRecipientFamily 0 q.val (Ne.symm q.property) T A y)
        ∂P.toSmoothGibbsEnvironment.law := by
  let ρ := P.coefficients
  let H := P.potential
  let T := fun y => vectorSquareFamily (Expr.evaluate ρ H (.adjoint i E) y)
  let A := phaseVectorAdjointOperand ρ H E i
  have hA : ∀ k a, ContDiff ℝ ∞ (fun y => A y k a) := by
    intro k a
    exact contDiff_section ρ H P.coefficient_smooth P.smooth E _
  have hAp : ∀ k a, PolynomialClosure.HasPolynomialJets (fun y => A y k a) := by
    intro k a
    exact P.toSmoothGibbsEnvironment.expression_polynomial_jets ρ
      P.coefficient_smooth P.coefficient_jets E _
  have hT : ∀ v, v ≠ 0 → ∀ a, ContDiff ℝ ∞ (fun y => T y v a) := by
    intro v _ a
    exact contDiff_section ρ H P.coefficient_smooth P.smooth (.adjoint i E) _
  have hTp : ∀ v, v ≠ 0 → ∀ a,
      PolynomialClosure.HasPolynomialJets (fun y => T y v a) := by
    intro v _ a
    exact P.toSmoothGibbsEnvironment.expression_polynomial_jets ρ
      P.coefficient_smooth P.coefficient_jets (.adjoint i E) _
  have hp : ∀ y, T y 0 = vectorSquareGraph.adjointCoordinateTensor 0 H A y := by
    intro y
    rfl
  have h := P.toSmoothGibbsEnvironment.integral_adjoint_network
    vectorSquareGraph 0 T A hA hAp hT hTp hp
  simpa only [T,coordinateEval_vectorSquareFamily] using h

theorem phase_vectorAdjointChildState_value {D : ℕ}
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (E : Expr σ 2) (i : Fin 2) (x : EuclideanSpace ℝ (Fin D)) :
    (vectorAdjointChildState E i).value ρ H x =
      (vectorSquareGraph.recipientGraph 0 1 (by decide)).coordinateEval D
        (vectorSquareGraph.principalRecipientFamily 0 1 (by decide)
          (fun y => vectorSquareFamily (Expr.evaluate ρ H (.adjoint i E) y))
          (phaseVectorAdjointOperand ρ H E i) x) := by
  have h := vectorSquareGraph.ibpSyntaxFamily_tensors 0 1 (by decide) ⟨0,[]⟩ E i []
    (vectorDecoratedPorts 0) (vectorPendingFamily (.adjoint i E)) ρ H x
  exact congrArg ((vectorSquareGraph.recipientGraph 0 1 (by decide)).coordinateEval D) h


theorem phase_integral_vectorAdjoint_eq_child {D : ℕ}
    (P : PhaseAnalyticEnvironment σ D)
    (E : Expr σ 2) (i : Fin 2) :
    (∫ y, ‖Expr.evaluate (P.coefficients)
      (P.potential) (.adjoint i E) y‖^2
      ∂P.toSmoothGibbsEnvironment.law) =
    ∫ y, (vectorAdjointChildState E i).value
      (P.coefficients)
      (P.potential) y ∂P.toSmoothGibbsEnvironment.law := by
  rw [phase_integral_vectorAdjoint_square P E i]
  rw [Finset.sum_eq_single (⟨1,by decide⟩ : {v : Fin 2 // v ≠ 0})]
  · apply integral_congr_ae
    filter_upwards [] with y
    exact (phase_vectorAdjointChildState_value _ _ E i y).symm
  · intro q _ hq
    exfalso
    apply hq
    apply Subtype.ext
    have hp := q.property
    have hv := q.val.isLt
    apply Fin.ext
    have hn : q.val.val ≠ 0 := by
      intro hz
      exact hp (Fin.ext hz)
    change q.val.val = 1
    omega
  · simp

end AcceleratedLogConcave.Tensor.Ordered.Graph
