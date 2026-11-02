import AcceleratedLogConcave.Tensor.NetworkSyntaxState
import AcceleratedLogConcave.Tensor.NetworkMatrixSquare

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name} {D : ℕ}

def matrixDecoratedPorts (v : Fin 2) : matrixSquareGraph.Slot v ≃ (Fin 0 ⊕ Fin 2) where
  toFun a := .inr (matrixSlotEquiv v a)
  invFun a := a.elim Fin.elim0 (matrixSlotEquiv v).symm
  left_inv a := (matrixSlotEquiv v).symm_apply_apply a
  right_inv a := by cases a with
    | inl i => exact Fin.elim0 i
    | inr i => exact congrArg Sum.inr ((matrixSlotEquiv v).apply_symm_apply i)

def matrixSyntaxState (e : Expr σ 2) : SyntaxState (initialTwoFormulas e e 0 0) where
  n := 1
  Edge := Unit
  edgeFintype := inferInstance
  graph := matrixSquareGraph
  admissible := matrixSquareGraph_admissible
  pending v := .formula ⟨v.val, []⟩ e []
  occurrence := Equiv.refl _
  occurrence_spec := by intro i; fin_cases i <;> rfl
  ports v := matrixDecoratedPorts v
  originWire _ := none
  origin_spec := by
    intro v u o h
    cases u with
    | inl i => exact Fin.elim0 i
    | inr i => cases h

 theorem matrixSquareFamily_reindex (A : FinCoeff 2 D) (v : Fin 2)
    (a : matrixSquareGraph.Slot v → Fin D) :
    matrixSquareFamily A v a = A (fun i => a ((matrixSlotEquiv v).symm i)) := by
  unfold matrixSquareFamily
  apply congrArg (fun b => A b)
  funext i
  apply congrArg a
  apply (matrixSlotEquiv v).injective
  rw [Equiv.apply_symm_apply]
  fin_cases v <;> fin_cases i <;> rfl

 theorem matrixSyntaxState_value (ρ : CoefficientEnvironment σ D)
    (H : EuclideanSpace ℝ (Fin D) → ℝ) (e : Expr σ 2)
    (x : EuclideanSpace ℝ (Fin D)) :
    (matrixSyntaxState e).value ρ H x = ‖Expr.evaluate ρ H e x‖^2 := by
  have hf : (matrixSyntaxState e).tensors ρ H x =
      matrixSquareFamily (Expr.evaluate ρ H e x) := by
    funext v
    change Fin 2 at v
    ext a
    change (matrixSquareGraph.Slot v → Fin D) at a
    change matrixSquareGraph.decoratedSectionTensor v ρ H e (matrixDecoratedPorts v) x a = _
    rw [matrixSquareFamily_reindex]
    rfl
  change matrixSquareGraph.coordinateEval D ((matrixSyntaxState e).tensors ρ H x) = _
  rw [hf]
  exact coordinateEval_matrixSquareFamily _
end AcceleratedLogConcave.Tensor.Ordered.Graph
