import AcceleratedLogConcave.Tensor.NetworkVectorSquare
import AcceleratedLogConcave.Tensor.NetworkIBPFamilyValue

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction ReductionRecords ActualCoefficientIntegrability
variable {Name : Type*} {σ : CoefficientSignature Name}

def vectorDecoratedPorts (v : Fin 2) : vectorSquareGraph.Slot v ≃ (Fin 0 ⊕ Fin 1) where
  toFun u := .inr (vectorSlotEquiv v u)
  invFun u := u.elim Fin.elim0 (vectorSlotEquiv v).symm
  left_inv u := (vectorSlotEquiv v).symm_apply_apply u
  right_inv u := by cases u with
    | inl u => exact Fin.elim0 u
    | inr u => exact congrArg Sum.inr ((vectorSlotEquiv v).apply_symm_apply u)

def vectorPendingFamily (e : Expr σ 1) (v : Fin 2) : vectorSquareGraph.SyntaxAt (σ := σ) v :=
  ⟨.formula ⟨v.val,[]⟩ e [], vectorDecoratedPorts v⟩

def vectorAdjointChildForest (E : Expr σ 2) (i : Fin 2) : List (TaggedPending σ) :=
  [.formula ((⟨0,[]⟩ : NodeAddress).child false) E [],
   .formula ⟨1,[]⟩ (.adjoint i E) [.ibp ⟨0,[]⟩]]

def vectorAdjointChildFamily (E : Expr σ 2) (i : Fin 2) :=
  vectorSquareGraph.ibpSyntaxFamily 0 1 (by decide)
    (vectorPendingFamily (.adjoint i E))
    (vectorSquareGraph.ibpOperandSyntax 0 1 (by decide) ⟨0,[]⟩ E i [] (vectorDecoratedPorts 0))
    (vectorSquareGraph.ibpRecipientSyntax 0 1 (by decide) (.ibp ⟨0,[]⟩)
      (.formula ⟨1,[]⟩ (.adjoint i E) []) (vectorDecoratedPorts 1))

/-- First vector IBP already has an admissible, literal two-occurrence state.
No artificial tensor factor or norm witness is introduced. -/
def vectorAdjointChildState (E : Expr σ 2) (i : Fin 2) :
    SyntaxState (vectorAdjointChildForest E i) where
  n := 1
  Edge := Option Empty
  edgeFintype := inferInstance
  graph := vectorSquareGraph.recipientGraph 0 1 (by decide)
  admissible := vectorSquare_recipient_admissible
  pending v := (vectorAdjointChildFamily E i v).1
  occurrence := Equiv.refl _
  occurrence_spec := by
    intro v
    fin_cases v
    · change (vectorSquareGraph.ibpSyntaxFamily 0 1 _ _ _ _ 0).1 = _
      rw [ibpSyntaxFamily_source]
      rfl
    · change (vectorSquareGraph.ibpSyntaxFamily 0 1 _ _ _ _ 1).1 = _
      rw [ibpSyntaxFamily_target]
      rfl
  ports v := (vectorAdjointChildFamily E i v).2
  originWire _ := some none
  origin_spec := by
    apply vectorSquareGraph.ibpSyntaxFamily_origin
    · intro v u o hu
      change (Fin 0 ⊕ Fin 1) at u
      cases u with
      | inl u => exact Fin.elim0 u
      | inr u => cases hu
    · apply vectorSquareGraph.ibpOperandSyntax_origin
      intro u
      exact Fin.elim0 u
    · apply vectorSquareGraph.ibpRecipientSyntax_origin
      · rfl
      · intro u o hu
        change (Fin 0 ⊕ Fin 1) at u
        cases u with
        | inl u => exact Fin.elim0 u
        | inr u => cases hu


theorem vectorAdjointChildState_value {D : ℕ}
    (ρ : CoefficientEnvironment signature D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (E : Expr signature 2) (i : Fin 2) (x : EuclideanSpace ℝ (Fin D)) :
    (vectorAdjointChildState E i).value ρ H x =
      (vectorSquareGraph.recipientGraph 0 1 (by decide)).coordinateEval D
        (vectorSquareGraph.principalRecipientFamily 0 1 (by decide)
          (fun y => vectorSquareFamily (Expr.evaluate ρ H (.adjoint i E) y))
          (vectorAdjointOperand ρ H E i) x) := by
  have h := vectorSquareGraph.ibpSyntaxFamily_tensors 0 1 (by decide) ⟨0,[]⟩ E i []
    (vectorDecoratedPorts 0) (vectorPendingFamily (.adjoint i E)) ρ H x
  exact congrArg ((vectorSquareGraph.recipientGraph 0 1 (by decide)).coordinateEval D) h


theorem vectorAdjointChildState_step (E : Expr σ 2) (i : Fin 2) :
    TaggedStep (.ibp ⟨0,[]⟩ (.formula ⟨1,[]⟩))
      (vectorAdjointChildForest E i) (initialTwoFormulas (.adjoint i E) (.adjoint i E) 0 0) := by
  exact TaggedStep.ibpAfter ⟨0,[]⟩ E i [] (.formula ⟨1,[]⟩ (.adjoint i E) []) [] [] []

open MeasureTheory Conditional
open Analysis.PositiveVarianceSlab

theorem integral_vectorAdjoint_eq_child {D : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (E : Expr signature 2) (i : Fin 2) {t : ℝ}
    (ht : t ∈ Set.Icc (left d.b) (right d.b)) :
    (∫ y, ‖Expr.evaluate (coefficientEnvironment d.F d.x d.ell d.r t)
      (interpolationPotential d.F d.x d.r t) (.adjoint i E) y‖^2
      ∂interpolationLaw d.F d.x d.r t) =
    ∫ y, (vectorAdjointChildState E i).value
      (coefficientEnvironment d.F d.x d.ell d.r t)
      (interpolationPotential d.F d.x d.r t) y ∂interpolationLaw d.F d.x d.r t := by
  rw [integral_vectorAdjoint_square d E i ht]
  rw [Finset.sum_eq_single (⟨1,by decide⟩ : {v : Fin 2 // v ≠ 0})]
  · apply integral_congr_ae
    filter_upwards [] with y
    exact (vectorAdjointChildState_value _ _ E i y).symm
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
