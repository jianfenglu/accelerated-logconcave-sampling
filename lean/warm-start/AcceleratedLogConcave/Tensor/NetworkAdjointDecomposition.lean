import AcceleratedLogConcave.Tensor.NetworkScoreCoordinates
import AcceleratedLogConcave.Tensor.NetworkPrincipalIBP

/-! Literal finite adjoint decomposition: principal field plus every positional score route. -/
noncomputable section
open scoped Classical BigOperators ContDiff
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction
variable {n D : ℕ} {Edge Name : Type*} [Fintype Edge] {σ : CoefficientSignature Name}
variable (g : Graph n Edge) (p : Fin (n+1))

def decoratedAdjointOperandTensor {r j : ℕ}
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (E : Expr σ (r+2)) (i : Fin (r+2)) (e : g.Slot p ≃ (Fin j ⊕ Fin (r+1)))
    (x : EuclideanSpace ℝ (Fin D)) (k : Fin D) : Coeff (g.Slot p) D :=
  WithLp.toLp 2 (fun a =>
    partialAlong (fun u => coordinateDirection D (a (g.decoratedLabelSlot p e u))) (List.finRange j)
      (sectionValue ρ H E (Fin.insertNth i k (fun u => a (g.adjointFreeSlot p e u)))) x)

private theorem list_sum_positions {α : Type*} (l : List α) (f : α → ℝ) :
    (l.map f).sum = ∑ u : Fin l.length, f (l.get u) := by
  rw [← List.sum_ofFn]
  congr 1
  ext u
  simp

 theorem decoratedSectionTensor_adjoint {r j : ℕ}
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (hρ : ∀ c a, ContDiff ℝ ∞ (fun x => ρ c x a)) (hH : ContDiff ℝ ∞ H)
    (E : Expr σ (r+2)) (i : Fin (r+2)) (e : g.Slot p ≃ (Fin j ⊕ Fin (r+1)))
    (x : EuclideanSpace ℝ (Fin D)) (a : g.Slot p → Fin D) :
    g.decoratedSectionTensor p ρ H (.adjoint i E) e x a =
      g.adjointCoordinateTensor p H (g.decoratedAdjointOperandTensor p ρ H E i e) x a +
      ∑ u : Fin (scoreRoutes (List.finRange j)).length,
        g.decoratedScoreRouteTensor p ρ H E i e ((scoreRoutes (List.finRange j)).get u) x a := by
  change partialAlong _ _ _ x = adjointField H (coordinateDirection D) _ x + ∑ u : Fin (scoreRoutes (List.finRange j)).length, ∑ k : Fin D, _
  rw [decorated_evaluate_adjoint _ _ ρ H hρ hH E i]
  simp only [decoratedAdjointOperandTensor, decoratedLabelSlot, adjointFreeSlot]
  congr 1
  simp_rw [list_sum_positions]
  exact Finset.sum_comm

/-- None is the principal branch; every Some index is a list position, not a set element. -/
def decoratedAdjointBranchTensor {r j : ℕ}
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (E : Expr σ (r+2)) (i : Fin (r+2)) (e : g.Slot p ≃ (Fin j ⊕ Fin (r+1)))
    (x : EuclideanSpace ℝ (Fin D)) : Option (Fin (scoreRoutes (List.finRange j)).length) → Coeff (g.Slot p) D
  | none => g.adjointCoordinateTensor p H (g.decoratedAdjointOperandTensor p ρ H E i e) x
  | some u => g.decoratedScoreRouteTensor p ρ H E i e ((scoreRoutes (List.finRange j)).get u) x

 theorem coordinateEval_decorated_adjoint {r j : ℕ}
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (hρ : ∀ c a, ContDiff ℝ ∞ (fun x => ρ c x a)) (hH : ContDiff ℝ ∞ H)
    (E : Expr σ (r+2)) (i : Fin (r+2)) (e : g.Slot p ≃ (Fin j ⊕ Fin (r+1)))
    (x : EuclideanSpace ℝ (Fin D)) (T : g.Tensors D)
    (hparent : T p = g.decoratedSectionTensor p ρ H (.adjoint i E) e x) :
    g.coordinateEval D T = ∑ u : Option (Fin (scoreRoutes (List.finRange j)).length),
      g.coordinateEval D (g.replaceTensorAt p T (g.decoratedAdjointBranchTensor p ρ H E i e x u)) := by
  apply g.coordinateEval_sum_at p T
  intro a
  rw [hparent, Fintype.sum_option]
  exact g.decoratedSectionTensor_adjoint p ρ H hρ hH E i e x a
end AcceleratedLogConcave.Tensor.Ordered.Graph
