import AcceleratedLogConcave.Tensor.TerminalSlotBound
import AcceleratedLogConcave.Tensor.NetworkActualPending
import AcceleratedLogConcave.Tensor.TerminalBudgetBounds

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction ReductionRecords ActualCoefficientIntegrability Conditional
variable {D n : ℕ} {Edge : Type*} [Fintype Edge]

 theorem coefficient_pending_split_bound (g : Graph n Edge) (v : Fin (n+1))
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (hsmall : d.r^2*d.ell ≤ 1/2) (c : Name) (node : NodeAddress) (J : List LabelOrigin)
    (e : g.Slot v ≃ pendingPorts (.formula node (Expr.coefficient c) J))
    {t : ℝ} (ht : -1<t ∧ t<1) (y : EuclideanSpace ℝ (Fin D))
    (S : Finset (g.Slot v)) (hS : NontrivialSplit S) :
    splitNorm D S (g.pendingTensor v (coefficientEnvironment d.F d.x d.ell d.r t)
      (interpolationPotential d.F d.x d.r t) (.formula node (Expr.coefficient c) J) e y) ≤
      (2:ℝ)^(signature.size c+J.length) * ((signature.size c+J.length).factorial : ℝ) *
        (Real.sqrt (conditionalVariance t)) ^ (-(signature.weight c : ℝ) - (J.length : ℝ)) := by
  let f : g.Slot v ≃ coefficientDerivativeSlots c J.length :=
    e.trans (coefficientTerminalSlotEquiv c J.length).symm
  have he : g.pendingTensor v (coefficientEnvironment d.F d.x d.ell d.r t)
      (interpolationPotential d.F d.x d.r t) (.formula node (Expr.coefficient c) J) e y =
      WithLp.toLp 2 (fun a => actualCoefficientDerivative d.F d.x d.ell d.r t c J.length y
        (a ∘ f.symm)) := by
    ext a
    symm
    exact actualCoefficientDerivative_terminal d.F d.x d.ell d.r t c J.length y
      (a ∘ e.symm)
  rw [he]
  exact (splitNorm_slotEquiv_le D f S _).trans
    (actualCoefficientDerivative_split_budget d hsmall c J.length ht y _
      (nontrivialSplit_map_equiv f hS))

 theorem score_pending_split_bound (g : Graph n Edge) (v : Fin (n+1))
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (hsmall : d.r^2*d.ell ≤ 1/2) (node : NodeAddress) (o : LabelOrigin) (J : List LabelOrigin)
    (e : g.Slot v ≃ pendingPorts (.score node (o::J) (by simp)))
    {t : ℝ} (ht : -1<t ∧ t<1) (y : EuclideanSpace ℝ (Fin D))
    (S : Finset (g.Slot v)) (hS : NontrivialSplit S) :
    splitNorm D S (g.pendingTensor v (coefficientEnvironment d.F d.x d.ell d.r t)
      (interpolationPotential d.F d.x d.r t) (.score node (o::J) (by simp)) e y) ≤
      (2:ℝ)^(J.length+2) * ((J.length+2).factorial : ℝ) *
        (Real.sqrt (conditionalVariance t)) ^ (-(J.length : ℝ)) := by
  let f : g.Slot v ≃ coefficientDerivativeSlots (Sum.inr ()) J.length :=
    (e.trans (scoreTerminalSlotEquiv J.length)).trans
      (coefficientTerminalSlotEquiv (Sum.inr ()) J.length).symm
  have he : g.pendingTensor v (coefficientEnvironment d.F d.x d.ell d.r t)
      (interpolationPotential d.F d.x d.r t) (.score node (o::J) (by simp)) e y =
      WithLp.toLp 2 (fun a => actualCoefficientDerivative d.F d.x d.ell d.r t
        (Sum.inr ()) J.length y (a ∘ f.symm)) := by
    ext a
    exact actualScore_terminal d J.length ht y (a ∘ e.symm)
  rw [he]
  have hh := (splitNorm_slotEquiv_le D f S _).trans
    (actualCoefficientDerivative_split_budget d hsmall (Sum.inr ()) J.length ht y _
      (nontrivialSplit_map_equiv f hS))
  simpa [signature,Nat.add_comm] using hh

/-- Every actual terminal occurrence satisfies its literal source budget. -/
theorem pendingTensor_terminal_bound (g : Graph n Edge) (v : Fin (n+1))
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (hsmall : d.r^2*d.ell ≤ 1/2) {L V : Type*} (values : OriginValues L V)
    (q : TaggedPending signature) (hq : (q.erase values).Terminal)
    (e : g.Slot v ≃ pendingPorts q) {t : ℝ} (ht : -1<t ∧ t<1)
    (y : EuclideanSpace ℝ (Fin D)) (S : Finset (g.Slot v)) (hS : NontrivialSplit S) :
    splitNorm D S (g.pendingTensor v (coefficientEnvironment d.F d.x d.ell d.r t)
      (interpolationPotential d.F d.x d.r t) q e y) ≤
      (2:ℝ)^((q.erase values).sizeBudget) * (((q.erase values).sizeBudget).factorial : ℝ) *
        (Real.sqrt (conditionalVariance t)) ^ (-((q.erase values).smoothingBudget : ℝ)) := by
  cases q with
  | formula node E J =>
    cases E with
    | coefficient c =>
      have hh := coefficient_pending_split_bound g v d hsmall c node J e ht y S hS
      simpa [TaggedPending.erase,Pending.sizeBudget,Pending.smoothingBudget,
        Expr.size,Expr.weight,neg_add,sub_eq_add_neg,add_comm] using hh
    | _ => simp [TaggedPending.erase,Pending.Terminal] at hq
  | score node J hJ =>
    cases J with
    | nil => exact False.elim (hJ rfl)
    | cons o J =>
      have hh := score_pending_split_bound g v d hsmall node o J e ht y S hS
      simpa [TaggedPending.erase,Pending.sizeBudget,Pending.smoothingBudget,Nat.add_assoc] using hh

end AcceleratedLogConcave.Tensor.Ordered.Graph
