import AcceleratedLogConcave.Tensor.NetworkAddedSlots
import AcceleratedLogConcave.Tensor.NetworkSyntaxState

noncomputable section
open scoped Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction ReductionRecords

/-- Insert the recipient's new derivative at the head, preserving all old slots. -/
def headDerivativePorts (a : ℕ) (Free : Type*) :
    ((Fin a ⊕ Free) ⊕ Unit) ≃ (Fin (a+1) ⊕ Free) :=
  (Equiv.sumAssoc _ _ _).trans
    ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _)).trans
      ((Equiv.sumAssoc _ _ _).symm.trans
        (Equiv.sumCongr
          ((Equiv.optionEquivSumPUnit (Fin a)).symm.trans (finSuccEquiv' (0 : Fin (a+1))).symm)
          (Equiv.refl _))))

 theorem headDerivativePorts_old_derivative (a : ℕ) (Free : Type*) (u : Fin a) :
    headDerivativePorts a Free (.inl (.inl u)) = .inl u.succ := by
  simp [headDerivativePorts]

 theorem headDerivativePorts_old_free (a : ℕ) (Free : Type*) (u : Free) :
    headDerivativePorts a Free (.inl (.inr u)) = .inr u := rfl

 theorem headDerivativePorts_fresh (a : ℕ) (Free : Type*) :
    headDerivativePorts a Free (.inr ()) = .inl 0 := by
  simp [headDerivativePorts]

variable {Name : Type*} {σ : CoefficientSignature Name}
def decoratePortEquiv (o : LabelOrigin) : (q : TaggedPending σ) →
    (pendingPorts q ⊕ Unit) ≃ pendingPorts (q.decorate o)
  | .formula _ _ J => headDerivativePorts J.length _
  | .score _ J _ => headDerivativePorts J.length _

theorem decoratePortEquiv_old_origin (o : LabelOrigin) (q : TaggedPending σ) (u : pendingPorts q) :
    pendingPortOrigin (q.decorate o) (decoratePortEquiv o q (.inl u)) = pendingPortOrigin q u := by
  cases q <;> cases u <;>
    simp only [decoratePortEquiv] <;> rfl

theorem decoratePortEquiv_fresh_origin (o : LabelOrigin) (q : TaggedPending σ) :
    pendingPortOrigin (q.decorate o) (decoratePortEquiv o q (.inr ())) = some o := by
  cases q <;> simp only [decoratePortEquiv] <;> rfl

/-- The removed adjoint slot becomes the new graph edge's coordinate. -/
def adjointOperandPorts (j r : ℕ) (i : Fin (r+2)) :
    (Fin j ⊕ Fin (r+2)) ≃ ((Fin j ⊕ Fin (r+1)) ⊕ Unit) :=
  (Equiv.sumCongr (Equiv.refl _) (finSuccEquiv' i)).trans
    ((Equiv.sumCongr (Equiv.refl _) (Equiv.optionEquivSumPUnit _)).trans
      (Equiv.sumAssoc _ _ _).symm)

 theorem adjointOperandPorts_derivative (j r : ℕ) (i : Fin (r+2)) (u : Fin j) :
    adjointOperandPorts j r i (.inl u) = .inl (.inl u) := rfl

 theorem adjointOperandPorts_fresh (j r : ℕ) (i : Fin (r+2)) :
    adjointOperandPorts j r i (.inr i) = .inr () := by simp [adjointOperandPorts]

 theorem adjointOperandPorts_old_free (j r : ℕ) (i : Fin (r+2)) (u : Fin (r+1)) :
    adjointOperandPorts j r i (.inr (i.succAbove u)) = .inl (.inr u) := by
  simp [adjointOperandPorts]

end AcceleratedLogConcave.Tensor.Ordered.Graph
