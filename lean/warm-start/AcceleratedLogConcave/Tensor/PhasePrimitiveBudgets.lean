import AcceleratedLogConcave.Tensor.PhaseTerminalNetwork
import AcceleratedLogConcave.Tensor.PhaseAnalyticEnvironment

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name} {D : ℕ}

/-- Canonical actual derivative tensor of one primitive, with derivative slots
kept distinct from the primitive's output slots. -/
def phaseCoefficientJet (ρ : CoefficientEnvironment σ D) (a : Name) (j : ℕ)
    (x : EuclideanSpace ℝ (Fin D)) : Coeff (Fin j ⊕ Fin (σ.arity a)) D :=
  WithLp.toLp 2 (fun z => partialAlong
    (fun u : Fin j => coordinateDirection D (z (.inl u))) (List.finRange j)
    (fun y => ρ a y (fun u => z (.inr u))) x)

/-- A differentiated score is retained only at rank at least two. -/
def phaseScoreJet (H : EuclideanSpace ℝ (Fin D) → ℝ) (j : ℕ)
    (x : EuclideanSpace ℝ (Fin D)) : Coeff (Fin j ⊕ Unit) D :=
  WithLp.toLp 2 (fun z => partialAlong
    (fun u : Fin j => coordinateDirection D (z (.inl u))) (List.finRange j)
    (dir (coordinateDirection D (z (.inr ()))) H) x)

/-- Only actual primitive spatial jets and actual score-Hessian jets occur in
this quantitative hypothesis. There are no moments or composite expressions. -/
structure PhasePrimitiveBudgets (ρ : CoefficientEnvironment σ D)
    (H : EuclideanSpace ℝ (Fin D) → ℝ) (c R : ℝ) : Prop where
  coefficient : ∀ a j x (A : Finset (Fin j ⊕ Fin (σ.arity a))),
    NontrivialSplit A → splitNorm D A (phaseCoefficientJet ρ a j x) ≤
      c^(σ.size a+j) * ((σ.size a+j).factorial : ℝ) *
        R^(-((σ.weight a : ℝ)+(j : ℝ)))
  score : ∀ j, 0 < j → ∀ x (A : Finset (Fin j ⊕ Unit)),
    NontrivialSplit A → splitNorm D A (phaseScoreJet H j x) ≤
      c^(j+1) * ((j+1).factorial : ℝ) * R^(-((j-1 : ℕ) : ℝ))

/-- Slot relabeling converts canonical primitive budgets into the exact terminal
network inputs. Connectedness remains in SyntaxState, not in a tensor estimate. -/
theorem PhasePrimitiveBudgets.pending_bound
    {ρ : CoefficientEnvironment σ D} {H : EuclideanSpace ℝ (Fin D) → ℝ}
    {c R : ℝ} (h : PhasePrimitiveBudgets ρ H c R)
    {n : ℕ} {Edge : Type*} [Fintype Edge] (g : Graph n Edge) (v : Fin (n+1))
    (q : TaggedPending σ) (e : g.Slot v ≃ pendingPorts q)
    {L V : Type*} (values : OriginValues L V) (hq : q.activeNode = none)
    (x : EuclideanSpace ℝ (Fin D)) (A : Finset (g.Slot v)) (hA : NontrivialSplit A) :
    splitNorm D A (g.pendingTensor v ρ H q e x) ≤
      c^(q.erase values).sizeBudget * ((q.erase values).sizeBudget.factorial : ℝ) *
        R^(-((q.erase values).smoothingBudget : ℝ)) := by
  cases q with
  | formula node E J =>
    cases E with
    | coefficient a =>
      let e' : g.Slot v ≃ (Fin J.length ⊕ Fin (σ.arity a)) := e
      have he : g.pendingTensor v ρ H (.formula node (.coefficient a) J) e x =
          WithLp.toLp 2 (fun z => phaseCoefficientJet ρ a J.length x (z ∘ e'.symm)) := by
        ext z
        rfl
      rw [he]
      have hh := (splitNorm_slotEquiv_le D e' A (phaseCoefficientJet ρ a J.length x)).trans
        (h.coefficient a J.length x _ (nontrivialSplit_map_equiv e' hA))
      simpa [TaggedPending.erase,Pending.sizeBudget,Pending.smoothingBudget,
        Expr.size,Expr.weight] using hh
    | permute p E => simp [TaggedPending.activeNode] at hq
    | contract E F i j => simp [TaggedPending.activeNode] at hq
    | derivative E => simp [TaggedPending.activeNode] at hq
    | adjoint i E => simp [TaggedPending.activeNode] at hq
  | score node J hJ =>
    let e' : g.Slot v ≃ (Fin J.length ⊕ Unit) := e
    have he : g.pendingTensor v ρ H (.score node J hJ) e x =
        WithLp.toLp 2 (fun z => phaseScoreJet H J.length x (z ∘ e'.symm)) := by
      ext z
      rfl
    rw [he]
    have hh := (splitNorm_slotEquiv_le D e' A (phaseScoreJet H J.length x)).trans
      (h.score J.length (List.length_pos_iff.mpr hJ) x _ (nontrivialSplit_map_equiv e' hA))
    simpa only [TaggedPending.erase,Pending.sizeBudget,Pending.smoothingBudget,
      List.length_map,NNReal.coe_natCast] using hh
end AcceleratedLogConcave.Tensor.Ordered.Graph

namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction ReductionRecords MeasureTheory
variable {Name : Type*} {σ : CoefficientSignature Name} {D : ℕ}

theorem PhasePrimitiveBudgets.terminal_integral_bound
    (P : PhaseAnalyticEnvironment σ D) {c R : ℝ}
    (h : PhasePrimitiveBudgets P.coefficients P.potential c R)
    [IsProbabilityMeasure P.toSmoothGibbsEnvironment.law]
    {s : List (TaggedPending σ)} (S : SyntaxState s)
    {L V : Type*} (values : OriginValues L V)
    (hleaf : ∀ q ∈ s, q.activeNode = none) :
    |∫ y, S.value P.coefficients P.potential y ∂P.toSmoothGibbsEnvironment.law| ≤
      (D : ℝ) * phaseBudgetProduct c R (eraseForest values s) := by
  apply S.phase_terminal_integral_abs_bound P.coefficients P.potential
    P.toSmoothGibbsEnvironment.law values c R hleaf
  dsimp only
  let := S.edgeFintype
  intro v A hA y
  apply h.pending_bound S.graph v (S.pending v) (S.ports v) values _ y A hA
  apply hleaf
  obtain ⟨j,rfl⟩ := S.occurrence.surjective v
  rw [S.occurrence_spec]
  exact List.get_mem _ _
end AcceleratedLogConcave.Tensor.Ordered.Graph
