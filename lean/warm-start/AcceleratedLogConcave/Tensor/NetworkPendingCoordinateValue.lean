import AcceleratedLogConcave.Tensor.NetworkIBPDerivativeValue
import AcceleratedLogConcave.Tensor.NetworkContractStateSum
import AcceleratedLogConcave.Tensor.NetworkAdjointDecomposition

noncomputable section
open scoped Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name} {D : ℕ}

/-- Literal pending syntax evaluated in its own ordered coordinate slots. -/
def pendingCoordinateValue (ρ : CoefficientEnvironment σ D)
    (H : EuclideanSpace ℝ (Fin D) → ℝ) :
    (q : TaggedPending σ) → (pendingPorts q → Fin D) → EuclideanSpace ℝ (Fin D) → ℝ
  | .formula _ E J, a =>
      partialAlong (fun u : Fin J.length => coordinateDirection D (a (.inl u)))
        (List.finRange J.length) (sectionValue ρ H E (fun u => a (.inr u)))
  | .score _ J _, a =>
      partialAlong (fun u : Fin J.length => coordinateDirection D (a (.inl u)))
        (List.finRange J.length) (dir (coordinateDirection D (a (.inr ()))) H)

theorem pendingTensor_coordinateValue {n : ℕ} {Edge : Type*} [Fintype Edge]
    (g : Graph n Edge) (v : Fin (n+1)) (ρ : CoefficientEnvironment σ D)
    (H : EuclideanSpace ℝ (Fin D) → ℝ) (q : TaggedPending σ)
    (e : g.Slot v ≃ pendingPorts q) (a : g.Slot v → Fin D)
    (x : EuclideanSpace ℝ (Fin D)) :
    g.pendingTensor v ρ H q e x a = pendingCoordinateValue ρ H q (a ∘ e.symm) x := by
  cases q <;> rfl

/-- Decorating a recipient is its actual new directional derivative, including scores. -/
theorem pendingCoordinateValue_decorate (ρ : CoefficientEnvironment σ D)
    (H : EuclideanSpace ℝ (Fin D) → ℝ) (o : LabelOrigin) (q : TaggedPending σ)
    (a : pendingPorts (q.decorate o) → Fin D) :
    pendingCoordinateValue ρ H (q.decorate o) a =
      dir (coordinateDirection D (a (decoratePortEquiv o q (.inr ()))))
        (pendingCoordinateValue ρ H q (fun u => a (decoratePortEquiv o q (.inl u)))) := by
  cases q <;> simp only [TaggedPending.decorate, pendingCoordinateValue]
  all_goals erw [partialAlong_finRange_head]
  all_goals rfl

/-- The literal adjoint operand uses the new edge at precisely the removed slot. -/
theorem pendingCoordinateValue_adjoint_operand {r : ℕ}
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (node : NodeAddress) (E : Expr σ (r+2)) (i : Fin (r+2))
    (J : List LabelOrigin) (a : (Fin J.length ⊕ Fin (r+1)) → Fin D) (k : Fin D) :
    pendingCoordinateValue ρ H (.formula (node.child false) E J)
      (Sum.elim a (fun _ => k) ∘ adjointOperandPorts J.length r i) =
    partialAlong (fun u => coordinateDirection D (a (.inl u))) (List.finRange J.length)
      (sectionValue ρ H E (Fin.insertNth i k (fun u => a (.inr u)))) := by
  have hfree : (fun u => Sum.elim a (fun _ => k) (adjointOperandPorts J.length r i (.inr u))) =
      Fin.insertNth i k (fun u => a (.inr u)) := by
    funext u
    refine Fin.succAboveCases i ?_ ?_ u
    · simp only [adjointOperandPorts_fresh, Sum.elim_inr, Fin.insertNth_apply_same]
    · intro v
      simp only [adjointOperandPorts_old_free, Sum.elim_inl, Fin.insertNth_apply_succAbove]
  change partialAlong (fun u => coordinateDirection D
    (Sum.elim a (fun _ => k) (adjointOperandPorts J.length r i (.inl u))))
    (List.finRange J.length)
    (sectionValue ρ H E (fun u => Sum.elim a (fun _ => k)
      (adjointOperandPorts J.length r i (.inr u)))) = _
  simp only [adjointOperandPorts_derivative, Sum.elim_inl]
  rw [hfree]

end AcceleratedLogConcave.Tensor.Ordered.Graph
