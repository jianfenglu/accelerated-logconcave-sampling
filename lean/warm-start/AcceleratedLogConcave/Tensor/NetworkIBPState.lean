import AcceleratedLogConcave.Tensor.NetworkIBPFamily

noncomputable section
open scoped Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name}
namespace SyntaxState
variable {s : List (TaggedPending σ)} (S : SyntaxState s)

/-- Complete same-length principal IBP state. All syntax, occurrences, ports,
origins, graph orientation and admissibility are retained; no value certificate. -/
def ibpAt (ip iq : Fin s.length) (hne : ip ≠ iq)
    (operand recipient : TaggedPending σ)
    (A : (S.graph.recipientGraph (S.occurrence ip) (S.occurrence iq)
      (fun h => hne (S.occurrence.injective h))).SyntaxAt (σ := σ) (S.occurrence ip))
    (B : (S.graph.recipientGraph (S.occurrence ip) (S.occurrence iq)
      (fun h => hne (S.occurrence.injective h))).SyntaxAt (σ := σ) (S.occurrence iq))
    (hA : A.1 = operand) (hB : B.1 = recipient)
    (wire : LabelOrigin → Option (Option S.Edge))
    (hOld : ∀ v u o, pendingPortOrigin (S.pending v) u = some o →
      oldWire (S.originWire o) = wire o)
    (hAo : ∀ u o, pendingPortOrigin A.1 u = some o →
      Sum.elim Subtype.val Subtype.val (A.2.symm u) = wire o)
    (hBo : ∀ u o, pendingPortOrigin B.1 u = some o →
      Sum.elim Subtype.val Subtype.val (B.2.symm u) = wire o) :
    SyntaxState (ibpForest s ip iq operand recipient) := by
  letI := S.edgeFintype
  let p := S.occurrence ip
  let q := S.occurrence iq
  have hpq : p ≠ q := fun h => hne (S.occurrence.injective h)
  let P : ∀ v, S.graph.SyntaxAt (σ := σ) v := fun v => ⟨S.pending v, S.ports v⟩
  let Q := S.graph.ibpSyntaxFamily p q hpq P A B
  refine {
    n := S.n
    Edge := Option S.Edge
    edgeFintype := inferInstance
    graph := S.graph.recipientGraph p q hpq
    admissible := S.graph.recipientGraph_admissible p q hpq S.admissible
    pending := fun v => (Q v).1
    occurrence := (finCongr (ibpForest_length s ip iq operand recipient)).trans S.occurrence
    occurrence_spec := ?_
    ports := fun v => (Q v).2
    originWire := wire
    origin_spec := ?_ }
  · intro u
    let v : Fin s.length := Fin.cast (ibpForest_length s ip iq operand recipient) u
    have hu : u = Fin.cast (ibpForest_length s ip iq operand recipient).symm v := by
      apply Fin.ext
      rfl
    rw [hu, ibpForest_get]
    change (Q (S.occurrence v)).1 = _
    by_cases hq : v = iq
    · rw [ite_eq_left hq, hq]
      exact (congrArg Sigma.fst (S.graph.ibpSyntaxFamily_target p q hpq P A B)).trans hB
    rw [ite_eq_right hq]
    by_cases hp : v = ip
    · rw [ite_eq_left hp, hp]
      exact (congrArg Sigma.fst (S.graph.ibpSyntaxFamily_source p q hpq P A B)).trans hA
    rw [ite_eq_right hp]
    have hvp : S.occurrence v ≠ p := fun h => hp (S.occurrence.injective h)
    have hvq : S.occurrence v ≠ q := fun h => hq (S.occurrence.injective h)
    exact (congrArg Sigma.fst
      (S.graph.ibpSyntaxFamily_other p q hpq P A B (S.occurrence v) hvp hvq)).trans
        (S.occurrence_spec v)
  · apply S.graph.ibpSyntaxFamily_origin p q hpq P A B wire _ hAo hBo
    intro v u o hu
    exact (congrArg oldWire (S.origin_spec v u o hu)).trans (hOld v u o hu)

end SyntaxState
end AcceleratedLogConcave.Tensor.Ordered.Graph
