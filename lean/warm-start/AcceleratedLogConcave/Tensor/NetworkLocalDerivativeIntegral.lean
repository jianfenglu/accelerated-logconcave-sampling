import AcceleratedLogConcave.Tensor.NetworkSyntaxDerivative
import AcceleratedLogConcave.Tensor.NetworkLocalPermutationIntegral

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
open MeasureTheory
open scoped Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name} {D : ℕ}

namespace SyntaxState
variable {s : List (TaggedPending σ)} (S : SyntaxState s)

theorem pending_mem (v : Fin (S.n+1)) : S.pending v ∈ s := by
  rw [← S.occurrence.apply_symm_apply v, S.occurrence_spec]
  exact List.get_mem ..

theorem pending_tag_injective (hn : (s.map TaggedPending.tag).Nodup) :
    Function.Injective (fun v => (S.pending v).tag) := by
  intro v w h
  have hv := S.occurrence_spec (S.occurrence.symm v)
  have hw := S.occurrence_spec (S.occurrence.symm w)
  simp only [Equiv.apply_symm_apply] at hv hw
  have he : (s.get (S.occurrence.symm v)).tag = (s.get (S.occurrence.symm w)).tag := by
    rw [← hv, ← hw]; exact h
  have hi : (S.occurrence.symm v).val = (S.occurrence.symm w).val := by
    apply (hn.getElem_inj_iff
      (hi := by simp)
      (hj := by simp)).mp
    simpa using he
  exact S.occurrence.symm.injective (Fin.ext hi)

/-- Inventory freshness protects all old labelled ports, including score outputs. -/
theorem derivative_origin_fresh (a : NodeAddress)
    (hf : LabelOrigin.derivative a ∉ attachedOrigins s)
    (v : Fin (S.n+1)) (u : pendingPorts (S.pending v)) :
    pendingPortOrigin (S.pending v) u ≠ some (.derivative a) := by
  have hm := S.pending_mem v
  generalize hp : S.pending v = p at u hm ⊢
  intro h
  have hl : LabelOrigin.derivative a ∈ p.labels := by
    cases p with
    | formula b E J =>
      cases u with
      | inl i =>
        have he : J.get i = .derivative a := Option.some.inj h
        exact he ▸ List.get_mem J i
      | inr i => cases h
    | score b J hJ =>
      cases u with
      | inl i =>
        have he : J.get i = .derivative a := Option.some.inj h
        exact he ▸ List.get_mem J i
      | inr i => cases h
  exact hf (List.mem_flatMap.mpr ⟨p, hm, hl⟩)

/-- Derivative reduction leaves the entire graph and its admissibility unchanged.
Only the consumed output's previously fresh origin is recorded. -/
def eraseDerivativeAt (a : NodeAddress)
    (hn : (s.map TaggedPending.tag).Nodup)
    (hf : LabelOrigin.derivative a ∉ attachedOrigins s)
    (v₀ : Fin (S.n+1)) (u₀ : pendingPorts (S.pending v₀))
    (h₀ : derivativeOutput a (S.pending v₀) = some u₀) :
    SyntaxState (s.map (eraseDerivative a)) where
  n := S.n
  Edge := S.Edge
  edgeFintype := S.edgeFintype
  graph := S.graph
  admissible := S.admissible
  pending v := eraseDerivative a (S.pending v)
  occurrence := (finCongr (List.length_map ..)).trans S.occurrence
  occurrence_spec := by
    intro i
    simp only [Equiv.trans_apply]
    rw [S.occurrence_spec]
    simp
  ports v := (S.ports v).trans (eraseDerivativePorts a (S.pending v)).symm
  originWire := Function.update S.originWire (.derivative a)
    (Sum.elim Subtype.val Subtype.val ((S.ports v₀).symm u₀))
  origin_spec := by
    intro v u o ho
    change Sum.elim Subtype.val Subtype.val
      ((S.ports v).symm (eraseDerivativePorts a (S.pending v) u)) = _
    rcases eraseDerivative_origin_cases a (S.pending v) u o ho with hold | ⟨rfl, hnew⟩
    · have hne : o ≠ .derivative a := by
        intro he; subst o
        exact S.derivative_origin_fresh a hf v _ hold
      rw [Function.update_of_ne hne]
      exact S.origin_spec v _ o hold
    · rw [Function.update_self]
      have hv : v = v₀ := S.pending_tag_injective hn
        ((derivativeOutput_tag a _ _ hnew).trans (derivativeOutput_tag a _ _ h₀).symm)
      subst v
      have hu := Option.some.inj (hnew.symm.trans h₀)
      exact congrArg (fun z => Sum.elim Subtype.val Subtype.val ((S.ports v₀).symm z)) hu

theorem value_eraseDerivativeAt (a : NodeAddress)
    (hn : (s.map TaggedPending.tag).Nodup)
    (hf : LabelOrigin.derivative a ∉ attachedOrigins s)
    (v₀ : Fin (S.n+1)) (u₀ : pendingPorts (S.pending v₀))
    (h₀ : derivativeOutput a (S.pending v₀) = some u₀)
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (x : EuclideanSpace ℝ (Fin D)) :
    (S.eraseDerivativeAt a hn hf v₀ u₀ h₀).value ρ H x = S.value ρ H x := by
  let _ := S.edgeFintype
  unfold value
  congr 1
  funext v
  exact pendingTensor_eraseDerivative S.graph v ρ H a (S.pending v) (S.ports v) x

end SyntaxState

/-- The actual derivative step is transported to its literal canonical child.
The only analytic hypothesis is the child induction bound. -/
theorem integral_derivative_le {r : ℕ} (node : NodeAddress)
    (E : Expr σ r) (J : List LabelOrigin) (before after : List (TaggedPending σ))
    (S : SyntaxState (before ++ [.formula node (.derivative E) J] ++ after))
    (hn : ((before ++ [TaggedPending.formula node (.derivative E) J] ++ after).map
      TaggedPending.tag).Nodup)
    (hi : (originInventory (before ++ [TaggedPending.formula node (.derivative E) J] ++ after)).Nodup)
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (μ : Measure (EuclideanSpace ℝ (Fin D))) (bound : ℝ)
    (ih : ∀ child : SyntaxState
      (before ++ [.formula (node.child false) E (J ++ [.derivative node])] ++ after),
      |∫ x, child.value ρ H x ∂μ| ≤ bound) :
    |∫ x, S.value ρ H x ∂μ| ≤ bound := by
  have ho := other_tag_ne_selected before after (.formula node (.derivative E) J) hn
  have hm := map_eraseDerivative_canonical node E J before after ho
  have hf : LabelOrigin.derivative node ∉ attachedOrigins
      (before ++ [TaggedPending.formula node (.derivative E) J] ++ after) := by
    apply (TaggedStep.derivative node E J before after).fresh_of_inventory hi
    simp [Event.createdOrigins]
  have hex : ∃ (v : Fin (S.n+1)) (u : pendingPorts (S.pending v)),
      derivativeOutput node (S.pending v) = some u := by
    obtain ⟨i, he⟩ := List.mem_iff_get.mp
      (show TaggedPending.formula node (.derivative E) J ∈
        before ++ [TaggedPending.formula node (.derivative E) J] ++ after by simp)
    refine ⟨S.occurrence i, ?_⟩
    rw [S.occurrence_spec, he]
    exact ⟨.inr (Fin.last r), by simp [derivativeOutput]⟩
  obtain ⟨v, u, hu⟩ := hex
  let child : SyntaxState
      (before ++ [.formula (node.child false) E (J ++ [.derivative node])] ++ after) :=
    hm ▸ S.eraseDerivativeAt node hn hf v u hu
  have he (x : EuclideanSpace ℝ (Fin D)) : child.value ρ H x = S.value ρ H x := by
    rw [SyntaxState.value_cast]
    exact S.value_eraseDerivativeAt node hn hf v u hu ρ H x
  simpa only [he] using ih child

end AcceleratedLogConcave.Tensor.Ordered.Graph
