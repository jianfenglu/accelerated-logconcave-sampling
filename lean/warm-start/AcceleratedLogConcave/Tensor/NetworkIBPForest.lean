import AcceleratedLogConcave.Tensor.NetworkSyntaxState

noncomputable section
open scoped Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name}

/-- Principal IBP keeps the ordered forest and replaces exactly two occurrences. -/
def ibpForest (s : List (TaggedPending σ)) (p q : Fin s.length)
    (operand recipient : TaggedPending σ) : List (TaggedPending σ) :=
  (s.set p.val operand).set q.val recipient

 theorem ibpForest_length (s : List (TaggedPending σ)) (p q : Fin s.length)
    (operand recipient : TaggedPending σ) :
    (ibpForest s p q operand recipient).length = s.length := by
  simp [ibpForest]

 theorem ibpForest_get (s : List (TaggedPending σ)) (p q : Fin s.length)
    (operand recipient : TaggedPending σ) (u : Fin s.length) :
    (ibpForest s p q operand recipient).get
      (Fin.cast (ibpForest_length s p q operand recipient).symm u) =
      if u = q then recipient else if u = p then operand else s.get u := by
  simp only [ibpForest, List.get_eq_getElem, List.getElem_set]
  congr 1
  · exact propext (by simp only [Fin.ext_iff]; exact eq_comm)
  · congr 1
    exact propext (by simp only [Fin.ext_iff]; exact eq_comm)

 theorem set_forest_boundary (before after : List (TaggedPending σ))
    (old new : TaggedPending σ) :
    (before ++ old :: after).set before.length new = before ++ new :: after := by
  induction before with
  | nil => rfl
  | cons a before ih => simp [ih]

/-- Positional replacement is literally the canonical after-recipient forest. -/
theorem ibpForest_after_values (before between after : List (TaggedPending σ))
    (source recipient operand decorated : TaggedPending σ) :
    (((before ++ source :: (between ++ recipient :: after)).set before.length operand).set
      (before.length + 1 + between.length) decorated) =
      before ++ operand :: (between ++ decorated :: after) := by
  rw [set_forest_boundary]
  have hlen : (before ++ operand :: between).length = before.length + 1 + between.length := by
    simp
    omega
  rw [← hlen]
  have hassoc : before ++ operand :: (between ++ recipient :: after) =
      (before ++ operand :: between) ++ recipient :: after := by simp
  rw [hassoc, set_forest_boundary]
  simp

/-- The opposite syntax order is the same two-position update, not a new schedule. -/
theorem ibpForest_before_values (before between after : List (TaggedPending σ))
    (source recipient operand decorated : TaggedPending σ) :
    (((before ++ recipient :: (between ++ source :: after)).set
      (before.length + 1 + between.length) operand).set before.length decorated) =
      before ++ decorated :: (between ++ operand :: after) := by
  rw [List.set_comm operand decorated (by omega)]
  exact ibpForest_after_values before between after recipient source decorated operand

end AcceleratedLogConcave.Tensor.Ordered.Graph
