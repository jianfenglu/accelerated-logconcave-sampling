import AcceleratedLogConcave.Tensor.NetworkContractChildSyntax

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name}
variable {D n : ℕ} {Edge : Type*} [Fintype Edge] (g : Graph n Edge)

theorem decoratedSectionTensor_cast_derivative_length {r j k : ℕ}
    (v : Fin (n+1)) (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (E : Expr σ r) (e : g.Slot v ≃ (Fin j ⊕ Fin r)) (h : j = k)
    (x : EuclideanSpace ℝ (Fin D)) :
    g.decoratedSectionTensor v ρ H E
      (e.trans (Equiv.sumCongr (finCongr h) (Equiv.refl _))) x =
      g.decoratedSectionTensor v ρ H E e x := by
  subst k
  rfl

theorem contractChildSyntax_tensor {r j : ℕ} (p : Fin (n+1))
    (part : g.Slot p → Bool)
    (hi : ∃ q : g.InPort p, part (.inl q) = false)
    (ho : ∃ q : g.OutPort p, part (.inr q) = true)
    (J : List LabelOrigin) (hJ : J.length = j) (A : List (Fin j))
    (node : NodeAddress) (E : Expr σ (r+2)) (b : Bool) (i : Fin (r+2))
    (selected : (Fin A.length ⊕ Fin (r+1)) ≃ {z : g.Slot p // part z = b})
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (x : EuclideanSpace ℝ (Fin D)) :
    let Q := g.contractChildSyntax p part hi ho J hJ A node E b i selected
    (g.replaceVertex p part).pendingTensor (splitVertex p p b) ρ H Q.1 Q.2 x =
      (g.replaceVertex p part).decoratedSectionTensor (splitVertex p p b) ρ H E
        (g.decoratedOperandEquiv p part hi ho b i selected).symm x := by
  exact (g.replaceVertex p part).decoratedSectionTensor_cast_derivative_length
    _ ρ H E _ _ x

end AcceleratedLogConcave.Tensor.Ordered.Graph
