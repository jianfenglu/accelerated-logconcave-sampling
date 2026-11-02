import AcceleratedLogConcave.Tensor.NetworkLinearity
import AcceleratedLogConcave.Tensor.CoordinateReduction

/-! Actual decorated contraction route sums on all original network ports. -/
noncomputable section
open scoped Classical BigOperators ContDiff
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction
variable {n D : ℕ} {Edge Name : Type*} [Fintype Edge]
    {σ : CoefficientSignature Name}
variable (g : Graph n Edge) (p : Fin (n+1))

/-- Every outside derivative occurrence remains a distinct parent port. -/
def decoratedSectionTensor (ρ : CoefficientEnvironment σ D)
    (H : EuclideanSpace ℝ (Fin D) → ℝ) {r j : ℕ} (E : Expr σ r)
    (e : g.Slot p ≃ (Fin j ⊕ Fin r)) (x : EuclideanSpace ℝ (Fin D)) :
    Coeff (g.Slot p) D := WithLp.toLp 2 (fun a =>
      partialAlong (fun u : Fin j => coordinateDirection D (a (e.symm (.inl u))))
        (List.finRange j) (sectionValue ρ H E (fun u => a (e.symm (.inr u)))) x)

/-- One positional Leibniz route, still carrying the entire original port assignment. -/
def decoratedContractRouteTensor (ρ : CoefficientEnvironment σ D)
    (H : EuclideanSpace ℝ (Fin D) → ℝ) {r s j : ℕ}
    (E : Expr σ (r+2)) (F : Expr σ (s+2)) (i : Fin (r+2)) (k : Fin (s+2))
    (e : g.Slot p ≃ (Fin j ⊕ Fin (r+s+2)))
    (route : List (Fin j) × List (Fin j)) (x : EuclideanSpace ℝ (Fin D)) :
    Coeff (g.Slot p) D := WithLp.toLp 2 (fun a => ∑ c : Fin D,
      partialAlong (fun u : Fin j => coordinateDirection D (a (e.symm (.inl u))))
        route.1 (sectionValue ρ H E (leftAssignment i (fun u => a (e.symm (.inr u))) c)) x *
      partialAlong (fun u : Fin j => coordinateDirection D (a (e.symm (.inl u))))
        route.2 (sectionValue ρ H F (rightAssignment k (fun u => a (e.symm (.inr u))) c)) x)

private theorem list_sum_positions {α : Type*} (l : List α) (f : α → ℝ) :
    (l.map f).sum = ∑ u : Fin l.length, f (l.get u) := by
  rw [← List.sum_ofFn]
  congr 1
  ext u
  simp

/-- Exact local route decomposition using literal evaluated derivatives. -/
theorem decoratedSectionTensor_contract (ρ : CoefficientEnvironment σ D)
    (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (hρ : ∀ c a, ContDiff ℝ ∞ (fun x => ρ c x a)) (hH : ContDiff ℝ ∞ H)
    {r s j : ℕ} (E : Expr σ (r+2)) (F : Expr σ (s+2))
    (i : Fin (r+2)) (k : Fin (s+2)) (e : g.Slot p ≃ (Fin j ⊕ Fin (r+s+2)))
    (x : EuclideanSpace ℝ (Fin D)) (a : g.Slot p → Fin D) :
    g.decoratedSectionTensor p ρ H (.contract E F i k) e x a =
      ∑ u : Fin (routes (List.finRange j)).length,
        g.decoratedContractRouteTensor p ρ H E F i k e
          ((routes (List.finRange j)).get u) x a := by
  change partialAlong _ _ _ x = ∑ u : Fin (routes (List.finRange j)).length, ∑ c : Fin D, _
  rw [decorated_contract _ _ ρ H hρ hH E F i k]
  simp_rw [list_sum_positions]
  exact Finset.sum_comm

/-- Actual global network route expansion, indexed by positions so even equal-valued
routes keep their multiplicity. No derivative coordinate is frozen or discarded. -/
theorem coordinateEval_decorated_contract (ρ : CoefficientEnvironment σ D)
    (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (hρ : ∀ c a, ContDiff ℝ ∞ (fun x => ρ c x a)) (hH : ContDiff ℝ ∞ H)
    {r s j : ℕ} (E : Expr σ (r+2)) (F : Expr σ (s+2))
    (i : Fin (r+2)) (k : Fin (s+2)) (e : g.Slot p ≃ (Fin j ⊕ Fin (r+s+2)))
    (x : EuclideanSpace ℝ (Fin D)) (T : g.Tensors D)
    (hparent : T p = g.decoratedSectionTensor p ρ H (.contract E F i k) e x) :
    g.coordinateEval D T =
      ∑ u : Fin (routes (List.finRange j)).length,
        g.coordinateEval D (g.replaceTensorAt p T
          (g.decoratedContractRouteTensor p ρ H E F i k e
            ((routes (List.finRange j)).get u) x)) := by
  apply g.coordinateEval_sum_at p T
  intro a
  rw [hparent]
  exact g.decoratedSectionTensor_contract p ρ H hρ hH E F i k e x a
end AcceleratedLogConcave.Tensor.Ordered.Graph
