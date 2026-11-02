import AcceleratedLogConcave.Tensor.PhaseGibbsNetwork
import AcceleratedLogConcave.Tensor.NetworkPendingCoordinateValue

/-! Primitive phase coefficient hypotheses imply analytic closure of every
literal intermediate network, including derivative nodes and retained scores.
No finished-expression integrability or moment bound is a field. -/
noncomputable section
open MeasureTheory
open scoped Classical BigOperators ContDiff
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction ReductionRecords PolynomialClosure Conditional.Appell
variable {Name : Type*} {σ : CoefficientSignature Name} {D : ℕ}

structure PhaseAnalyticEnvironment (σ : CoefficientSignature Name) (D : ℕ)
    extends SmoothGibbsEnvironment D where
  coefficients : CoefficientEnvironment σ D
  coefficient_smooth : ∀ c a, ContDiff ℝ ∞ (fun x => coefficients c x a)
  coefficient_jets : ∀ c a, HasPolynomialJets (fun x => coefficients c x a)

namespace PhaseAnalyticEnvironment
variable (P : PhaseAnalyticEnvironment σ D)

private theorem polynomialJets_partial {L : Type*} (d : L → EuclideanSpace ℝ (Fin D))
    (J : List L) {f : EuclideanSpace ℝ (Fin D) → ℝ} (hf : HasPolynomialJets f) :
    HasPolynomialJets (partialAlong d J f) := by
  induction J with
  | nil => exact hf
  | cons v J ih => exact ih.direction (d v)

theorem decorated_expression_jets {r : ℕ} (e : Expr σ r) (a : Fin r → Fin D)
    {L : Type*} (d : L → EuclideanSpace ℝ (Fin D)) (J : List L) :
    HasPolynomialJets (partialAlong d J (sectionValue P.coefficients P.potential e a)) :=
  polynomialJets_partial d J
    (section_hasPolynomialJets P.coefficients P.potential P.coefficient_smooth P.smooth
      P.coefficient_jets P.score_jets e a)

theorem pending_smooth (q : TaggedPending σ) (a : pendingPorts q → Fin D) :
    ContDiff ℝ ∞ (pendingCoordinateValue P.coefficients P.potential q a) := by
  cases q with
  | formula node e J =>
    exact contDiff_partialAlong _ _
      (contDiff_section P.coefficients P.potential P.coefficient_smooth P.smooth e _)
  | score node J h => exact contDiff_partialAlong _ _ (contDiff_dir P.smooth _)

theorem pending_polynomial_jets (q : TaggedPending σ) (a : pendingPorts q → Fin D) :
    HasPolynomialJets (pendingCoordinateValue P.coefficients P.potential q a) := by
  cases q with
  | formula node e J =>
    exact polynomialJets_partial _ _
      (section_hasPolynomialJets P.coefficients P.potential P.coefficient_smooth P.smooth
        P.coefficient_jets P.score_jets e _)
  | score node J h => exact polynomialJets_partial _ _ (P.score_jets _)

theorem tensor_smooth {s : List (TaggedPending σ)} (S : SyntaxState s)
    (v : Fin (S.n+1)) (a : S.graph.Slot v → Fin D) :
    ContDiff ℝ ∞ (fun x => S.tensors P.coefficients P.potential x v a) := by
  let := S.edgeFintype
  have he : (fun x => S.tensors P.coefficients P.potential x v a) =
      pendingCoordinateValue P.coefficients P.potential (S.pending v)
        (a ∘ (S.ports v).symm) := by
    funext x
    exact pendingTensor_coordinateValue _ _ _ _ _ _ _ _
  rw [he]
  exact P.pending_smooth _ _

theorem tensor_polynomial_jets {s : List (TaggedPending σ)} (S : SyntaxState s)
    (v : Fin (S.n+1)) (a : S.graph.Slot v → Fin D) :
    HasPolynomialJets (fun x => S.tensors P.coefficients P.potential x v a) := by
  let := S.edgeFintype
  have he : (fun x => S.tensors P.coefficients P.potential x v a) =
      pendingCoordinateValue P.coefficients P.potential (S.pending v)
        (a ∘ (S.ports v).symm) := by
    funext x
    exact pendingTensor_coordinateValue _ _ _ _ _ _ _ _
  rw [he]
  exact P.pending_polynomial_jets _ _

/-- Every literal intermediate network is integrable under the genuine law,
by polynomial closure and ambient moments, without an expression-moment field. -/
theorem integrable_value {s : List (TaggedPending σ)} (S : SyntaxState s) :
    Integrable (S.value P.coefficients P.potential) P.toSmoothGibbsEnvironment.law := by
  let := S.edgeFintype
  let : IsFiniteMeasure P.toSmoothGibbsEnvironment.law := P.finite
  unfold SyntaxState.value coordinateEval
  apply integrable_finsetSum
  intro a _
  exact (HasGrowth.prod Finset.univ (fun v _ => P.tensor_polynomial_jets S v _ [])).integrable
    (continuous_finsetProd _ (fun v _ => (P.tensor_smooth S v _).continuous)).aestronglyMeasurable
    P.moments
end PhaseAnalyticEnvironment
end AcceleratedLogConcave.Tensor.Ordered.Graph
