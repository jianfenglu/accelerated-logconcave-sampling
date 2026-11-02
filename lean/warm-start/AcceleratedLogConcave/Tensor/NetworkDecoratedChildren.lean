import AcceleratedLogConcave.Tensor.NetworkDecoratedContract
import AcceleratedLogConcave.Tensor.NetworkChildSlots

/-! Actual derivative directions are read from inherited child ports. -/
noncomputable section
open scoped Classical BigOperators ContDiff
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction
variable {n D : ℕ} {Edge Name : Type*} [Fintype Edge]
    {σ : CoefficientSignature Name}
variable (g : Graph n Edge) (p : Fin (n+1)) (part : g.Slot p → Bool)
    (hI : ∃ q : g.InPort p, part (.inl q) = false)
    (hO : ∃ q : g.OutPort p, part (.inr q) = true)

private theorem partialAlong_congr_directions {V L : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (d e : L → V) (J : List L)
    (h : ∀ u ∈ J, d u = e u) (f : V → ℝ) :
    partialAlong d J f = partialAlong e J f := by
  induction J with
  | nil => rfl
  | cons u J ih =>
    simp only [partialAlong]
    rw [h u (by simp), ih (fun v hv => h v (by simp [hv]))]

/-- Directions for labels routed to this child are taken from that child's own ports.
The irrelevant branch is zero and is never used by the routed derivative list. -/
def childCoordinateDirection {L : Type*} (b : Bool) (labelSlot : L → g.Slot p)
    (a : (g.replaceVertex p part).Slot (splitVertex p p b) → Fin D) (u : L) :
    EuclideanSpace ℝ (Fin D) :=
  if h : part (labelSlot u) = b then
    coordinateDirection D (a (g.inheritedChildSlot p part hI hO b (labelSlot u) h))
  else 0

omit [Fintype Edge] in
theorem childCoordinateDirection_value {L : Type*} (b : Bool) (labelSlot : L → g.Slot p)
    (u : L) (hu : part (labelSlot u) = b) (c : Option Edge → Fin D) (k : Fin D) :
    g.childCoordinateDirection p part hI hO b labelSlot
      (Sum.elim (fun q => extendAssignment c k q.val) (fun q => extendAssignment c k q.val)) u =
    coordinateDirection D (Sum.elim (fun q : g.InPort p => c q.val)
      (fun q : g.OutPort p => c q.val) (labelSlot u)) := by
  simp only [childCoordinateDirection, dite_eq_left hu, inheritedChildSlot_value]

/-- A literal decorated operand, including the inherited derivative coordinates. -/
def decoratedContractChildTensor {r : ℕ} {L : Type*} (b : Bool)
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (E : Expr σ (r+2)) (i : Fin (r+2))
    (freeSlot : Fin (r+1) → g.Slot p) (hfree : ∀ u, part (freeSlot u) = b)
    (labelSlot : L → g.Slot p) (J : List L) (x : EuclideanSpace ℝ (Fin D)) :
    Coeff ((g.replaceVertex p part).Slot (splitVertex p p b)) D :=
  WithLp.toLp 2 (fun a => partialAlong (g.childCoordinateDirection p part hI hO b labelSlot a) J
    (sectionValue ρ H E (Fin.insertNth i (a (g.joiningChildSlot p part b))
      (fun u => a (g.inheritedChildSlot p part hI hO b (freeSlot u) (hfree u))))) x)

theorem decoratedContractChildTensor_value {r : ℕ} {L : Type*} (b : Bool)
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (E : Expr σ (r+2)) (i : Fin (r+2))
    (freeSlot : Fin (r+1) → g.Slot p) (hfree : ∀ u, part (freeSlot u) = b)
    (labelSlot : L → g.Slot p) (J : List L) (hlabels : ∀ u ∈ J, part (labelSlot u) = b)
    (x : EuclideanSpace ℝ (Fin D)) (c : Option Edge → Fin D) (k : Fin D) :
    g.decoratedContractChildTensor p part hI hO b ρ H E i freeSlot hfree labelSlot J x
      (Sum.elim (fun q => extendAssignment c k q.val) (fun q => extendAssignment c k q.val)) =
    partialAlong (fun u => coordinateDirection D (Sum.elim
      (fun q : g.InPort p => c q.val) (fun q : g.OutPort p => c q.val) (labelSlot u))) J
      (sectionValue ρ H E (Fin.insertNth i k (fun u => Sum.elim
        (fun q : g.InPort p => c q.val) (fun q : g.OutPort p => c q.val) (freeSlot u)))) x := by
  unfold decoratedContractChildTensor
  change partialAlong _ J (sectionValue ρ H E _) x = _
  have hjoin : Sum.elim (fun q => extendAssignment c k q.val)
      (fun q => extendAssignment c k q.val) (g.joiningChildSlot p part b) = k := by
    cases b <;> rfl
  simp only [hjoin, inheritedChildSlot_value]
  apply congrFun
  apply partialAlong_congr_directions
  intro u hu
  exact g.childCoordinateDirection_value p part hI hO b labelSlot u (hlabels u hu) c k
end AcceleratedLogConcave.Tensor.Ordered.Graph
