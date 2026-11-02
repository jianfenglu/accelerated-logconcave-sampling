import AcceleratedLogConcave.Tensor.NetworkLocalEvents
import AcceleratedLogConcave.Tensor.NetworkSyntaxPermutation
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section
open MeasureTheory
open scoped Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name} {D : ℕ}

namespace SyntaxState
/-- Equality transport changes only the displayed forest index. -/
theorem value_cast {s t : List (TaggedPending σ)} (h : s = t) (S : SyntaxState s)
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (x : EuclideanSpace ℝ (Fin D)) :
    (h ▸ S : SyntaxState t).value ρ H x = S.value ρ H x := by
  subst t
  rfl
end SyntaxState

/-- The permutation case of the actual integral induction transports its literal
state to the canonical child. The sole bound premise is the child induction bound. -/
theorem integral_permutation_le {r : ℕ} (node : NodeAddress)
    (perm : Equiv.Perm (Fin r)) (E : Expr σ r) (J : List LabelOrigin)
    (before after : List (TaggedPending σ))
    (S : SyntaxState (before ++ [.formula node (.permute perm E) J] ++ after))
    (hn : ((before ++ [TaggedPending.formula node (.permute perm E) J] ++ after).map TaggedPending.tag).Nodup)
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (μ : Measure (EuclideanSpace ℝ (Fin D))) (bound : ℝ)
    (ih : ∀ child : SyntaxState (before ++ [.formula node E J] ++ after),
      |∫ x, child.value ρ H x ∂μ| ≤ bound) :
    |∫ x, S.value ρ H x ∂μ| ≤ bound := by
  have ho := other_tag_ne_selected before after (.formula node (.permute perm E) J) hn
  have hm := map_erasePermutation_canonical node perm E J before after ho
  let child : SyntaxState (before ++ [.formula node E J] ++ after) := hm ▸ S.erasePermutationAt node
  have he (x : EuclideanSpace ℝ (Fin D)) : child.value ρ H x = S.value ρ H x := by
    rw [SyntaxState.value_cast]
    exact S.value_erasePermutationAt node ρ H x
  have hh := ih child
  simpa only [he] using hh

end AcceleratedLogConcave.Tensor.Ordered.Graph
