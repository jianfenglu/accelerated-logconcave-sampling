import AcceleratedLogConcave.Tensor.NetworkDecoratedContract
import AcceleratedLogConcave.Tensor.ReductionRecords

/-! Literal syntax and retained origin/port data for canonical reduction states.
No tensor value, global equality, or norm certificate is part of the data. -/
noncomputable section
open scoped Classical BigOperators
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name}

def pendingPorts : TaggedPending σ → Type
  | @TaggedPending.formula _ _ r _ _ J => Fin J.length ⊕ Fin r
  | .score _ J _ => Fin J.length ⊕ Unit

/-- Only derivative labels and the distinguished score output carry reduction origins. -/
def pendingPortOrigin : (p : TaggedPending σ) → pendingPorts p → Option LabelOrigin
  | .formula _ _ J, .inl i => some (J.get i)
  | .formula _ _ _, .inr _ => none
  | .score _ J _, .inl i => some (J.get i)
  | .score a _ _, .inr _ => some (.ibp a)

/-- Syntax order and ordered graph orientation are explicitly separate. -/
structure SyntaxState (s : List (TaggedPending σ)) where
  n : ℕ
  Edge : Type
  edgeFintype : Fintype Edge
  graph : Graph n Edge
  admissible : graph.Admissible
  pending : Fin (n+1) → TaggedPending σ
  occurrence : Fin s.length ≃ Fin (n+1)
  occurrence_spec : ∀ i, pending (occurrence i) = s.get i
  ports : ∀ v, graph.Slot v ≃ pendingPorts (pending v)
  originWire : LabelOrigin → Option Edge
  origin_spec : ∀ v u o, pendingPortOrigin (pending v) u = some o →
    Sum.elim Subtype.val Subtype.val ((ports v).symm u) = originWire o

variable {D n : ℕ} {Edge : Type*} [Fintype Edge]

def pendingTensor (g : Graph n Edge) (v : Fin (n+1))
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (p : TaggedPending σ) (e : g.Slot v ≃ pendingPorts p)
    (x : EuclideanSpace ℝ (Fin D)) : Coeff (g.Slot v) D :=
  match p, e with
  | .formula _ E _J, e => g.decoratedSectionTensor v ρ H E e x
  | .score _ J _, e => WithLp.toLp 2 (fun a =>
      partialAlong (fun i : Fin J.length => coordinateDirection D (a (e.symm (.inl i))))
        (List.finRange J.length)
        (dir (coordinateDirection D (a (e.symm (.inr ())))) H) x)

namespace SyntaxState
variable {s : List (TaggedPending σ)} (S : SyntaxState s)

/-- Every factor is evaluated directly from the retained syntax and ports. -/
def tensors (ρ : CoefficientEnvironment σ D)
    (H : EuclideanSpace ℝ (Fin D) → ℝ) (x : EuclideanSpace ℝ (Fin D)) :=
  letI := S.edgeFintype
  fun v => S.graph.pendingTensor v ρ H (S.pending v) (S.ports v) x

def value (ρ : CoefficientEnvironment σ D)
    (H : EuclideanSpace ℝ (Fin D) → ℝ) (x : EuclideanSpace ℝ (Fin D)) : ℝ :=
  letI := S.edgeFintype
  S.graph.coordinateEval D (S.tensors ρ H x)

end SyntaxState
end AcceleratedLogConcave.Tensor.Ordered.Graph
