import AcceleratedLogConcave.Tensor.NetworkMatrixSquare
import AcceleratedLogConcave.Tensor.NetworkActualIBP
import AcceleratedLogConcave.Conditional.Flow.ExtendedState

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped Classical BigOperators
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction ActualCoefficientIntegrability Conditional
open Analysis.PositiveVarianceSlab

/-- The unexpanded vector square has just the closing wire. It is deliberately
not asserted admissible: one original-data IBP adds the missing forward edge. -/
def vectorSquareGraph : Graph 1 Empty where
  source := Empty.elim
  target := Empty.elim
  forward e := e.elim

def vectorSquareSlot (v : Fin 2) : vectorSquareGraph.Slot v :=
  if h : v = 0 then .inl ⟨none, by subst v; rfl⟩
  else .inr ⟨none, by
    have hv : v = 1 := by omega
    subst v
    rfl⟩

theorem vectorSquareSlot_unique (v : Fin 2) (u : vectorSquareGraph.Slot v) :
    u = vectorSquareSlot v := by
  fin_cases v <;> cases u with
  | inl u =>
    rcases u with ⟨w,h⟩
    cases w with
    | none => simp_all [vectorSquareSlot, incoming, outgoing, vectorSquareGraph] <;> norm_num [incoming, outgoing, vectorSquareGraph, Fin.ext_iff] at h
    | some e => exact e.elim
  | inr u =>
    rcases u with ⟨w,h⟩
    cases w with
    | none => simp_all [vectorSquareSlot, incoming, outgoing, vectorSquareGraph] <;> norm_num [incoming, outgoing, vectorSquareGraph, Fin.ext_iff] at h
    | some e => exact e.elim

def vectorSlotEquiv (v : Fin 2) : vectorSquareGraph.Slot v ≃ Fin 1 where
  toFun _ := 0
  invFun _ := vectorSquareSlot v
  left_inv := fun u => (vectorSquareSlot_unique v u).symm
  right_inv i := Subsingleton.elim _ i

def vectorSquareFamily {D : ℕ} (A : FinCoeff 1 D) : vectorSquareGraph.Tensors D :=
  fun v => WithLp.toLp 2 (fun a => A (fun _ => a (vectorSquareSlot v)))

theorem vectorSquareFamily_value {D : ℕ} (A : FinCoeff 1 D)
    (c : Option Empty → Fin D) (v : Fin 2) :
    vectorSquareGraph.wireValue (vectorSquareFamily A) c v = A (fun _ => c none) := by
  fin_cases v <;> rfl

theorem coordinateEval_vectorSquareFamily {D : ℕ} (A : FinCoeff 1 D) :
    vectorSquareGraph.coordinateEval D (vectorSquareFamily A) = ‖A‖^2 := by
  let w : Option Empty ≃ Fin 1 := {
    toFun := fun _ => 0
    invFun := fun _ => none
    left_inv := by intro x; cases x with | none => rfl | some e => exact e.elim
    right_inv := fun i => Subsingleton.elim _ i }
  have hv : vectorSquareGraph.coordinateEval D (vectorSquareFamily A) =
      ∑ c : Option Empty → Fin D, (A (fun _ => c none))^2 := by
    unfold coordinateEval
    apply Finset.sum_congr rfl
    intro c _
    change (∏ v : Fin 2, vectorSquareGraph.wireValue (vectorSquareFamily A) c v) = _
    simp only [vectorSquareFamily_value, Fin.prod_univ_two, pow_two]
  rw [hv]
  calc
    (∑ c : Option Empty → Fin D, (A (fun _ => c none))^2) =
        ∑ a : Fin 1 → Fin D, (A a)^2 := by
      apply Fintype.sum_equiv (Equiv.arrowCongr w (Equiv.refl (Fin D)))
      intro c
      rfl
    _ = ‖A‖^2 := by
      symm
      convert PiLp.norm_sq_eq_of_L2 (fun _ : Fin 1 → Fin D => ℝ) A using 1
      apply Finset.sum_congr rfl
      intro a _
      exact (sq_abs (A a)).symm

/-- The sole recipient of the first vector-square IBP restores both nonempty
port sides, allowing the existing admissible-network induction without change. -/
theorem vectorSquare_recipient_admissible :
    (vectorSquareGraph.recipientGraph 0 1 (by decide)).Admissible := by
  intro v
  fin_cases v
  · exact ⟨⟨⟨none,rfl⟩⟩,⟨⟨some none,rfl⟩⟩⟩
  · exact ⟨⟨⟨some none,rfl⟩⟩,⟨⟨none,rfl⟩⟩⟩


def vectorAdjointOperand {D : ℕ} (ρ : CoefficientEnvironment signature D)
    (H : EuclideanSpace ℝ (Fin D) → ℝ) (E : Expr signature 2) (i : Fin 2)
    (y : EuclideanSpace ℝ (Fin D)) (k : Fin D) : Coeff (vectorSquareGraph.Slot 0) D :=
  WithLp.toLp 2 (fun a => Expr.evaluate ρ H E y
    (Fin.insertNth i k (fun _ => a (vectorSquareSlot 0))))

/-- Exact original-law first IBP of a literal vector adjoint square. The right
side is the actual derivative-recipient family, not a supplied equality witness. -/
theorem integral_vectorAdjoint_square {D : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (E : Expr signature 2) (i : Fin 2) {t : ℝ}
    (ht : t ∈ Set.Icc (left d.b) (right d.b)) :
    let ρ := coefficientEnvironment d.F d.x d.ell d.r t
    let H := interpolationPotential d.F d.x d.r t
    let T := fun y => vectorSquareFamily (Expr.evaluate ρ H (.adjoint i E) y)
    let A := vectorAdjointOperand ρ H E i
    (∫ y, ‖Expr.evaluate ρ H (.adjoint i E) y‖^2
      ∂interpolationLaw d.F d.x d.r t) =
      ∑ q : {v : Fin 2 // v ≠ 0}, ∫ y,
        (vectorSquareGraph.recipientGraph 0 q.val (Ne.symm q.property)).coordinateEval D
          (vectorSquareGraph.principalRecipientFamily 0 q.val (Ne.symm q.property) T A y)
        ∂interpolationLaw d.F d.x d.r t := by
  let ρ := coefficientEnvironment d.F d.x d.ell d.r t
  let H := interpolationPotential d.F d.x d.r t
  let T := fun y => vectorSquareFamily (Expr.evaluate ρ H (.adjoint i E) y)
  let A := vectorAdjointOperand ρ H E i
  have hA : ∀ k a, ActualDecoratedCoordinate d.F d.x d.ell d.r t
      (fun y => A y k a) := by
    intro k a
    exact ⟨2,E,Fin.insertNth i k (fun _ => a (vectorSquareSlot 0)),[],rfl⟩
  have hT : ∀ v, v ≠ 0 → ∀ a, ActualDecoratedCoordinate d.F d.x d.ell d.r t
      (fun y => T y v a) := by
    intro v _ a
    exact ⟨1,.adjoint i E,(fun _ => a (vectorSquareSlot v)),[],rfl⟩
  have hp : ∀ y, T y 0 = vectorSquareGraph.adjointCoordinateTensor 0 H A y := by
    intro y
    rfl
  have h := integral_actual_adjoint_network d.hF d.hlo d.hhi d.hb0 d.hb1 d.x d.r ht
    vectorSquareGraph 0 T A hA hT hp
  simpa only [T,coordinateEval_vectorSquareFamily] using h

end AcceleratedLogConcave.Tensor.Ordered.Graph
