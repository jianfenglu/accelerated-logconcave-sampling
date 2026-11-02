import AcceleratedLogConcave.Tensor.MaterialExpressionSmooth
import AcceleratedLogConcave.Tensor.ReductionExpansion

noncomputable section
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open AdjointReduction ReductionRecords

def IsMaterialPending : TaggedPending signature → Prop
  | .formula _ e _ => IsMaterialExpression e
  | .score .. => True

def IsMaterialForest (s : List (TaggedPending signature)) : Prop :=
  ∀ p ∈ s, IsMaterialPending p

@[simp] theorem isMaterialForest_nil : IsMaterialForest [] := by simp [IsMaterialForest]
@[simp] theorem isMaterialForest_cons (p : TaggedPending signature) (s : List (TaggedPending signature)) :
    IsMaterialForest (p::s) ↔ IsMaterialPending p ∧ IsMaterialForest s := by simp [IsMaterialForest]
@[simp] theorem isMaterialForest_append (s t : List (TaggedPending signature)) :
    IsMaterialForest (s++t) ↔ IsMaterialForest s ∧ IsMaterialForest t := by
  simp [IsMaterialForest,List.mem_append,or_imp,forall_and]
@[simp] theorem isMaterialPending_decorate (o : LabelOrigin) (p : TaggedPending signature) :
    IsMaterialPending (p.decorate o) ↔ IsMaterialPending p := by cases p <;> rfl

theorem formula_isMaterial_of_mem {s : List (TaggedPending signature)} (hs : IsMaterialForest s)
    {r : ℕ} (node : NodeAddress) (e : Expr signature r) (J : List LabelOrigin)
    (h : .formula node e J ∈ s) : IsMaterialExpression e := hs _ h

theorem derivative_formula_not_mem {s : List (TaggedPending signature)} (hs : IsMaterialForest s)
    {r : ℕ} (node : NodeAddress) (e : Expr signature r) (J : List LabelOrigin) :
    .formula node (.derivative e) J ∉ s := by
  intro h
  exact hs _ h

theorem taggedStep_isMaterial {s t : List (TaggedPending signature)} {event : Event}
    (h : TaggedStep event t s) (hs : IsMaterialForest s) : IsMaterialForest t := by
  cases h <;>
    simp_all only [isMaterialForest_append,isMaterialForest_cons,isMaterialForest_nil,
      isMaterialPending_decorate]
  all_goals simp_all [IsMaterialPending,IsMaterialExpression]

theorem legalTrace_isMaterial {events s t} (h : LegalTrace (σ := signature) events s t)
    (hs : IsMaterialForest s) : IsMaterialForest t := by
  induction h with
  | nil => exact hs
  | cons first rest ih => exact ih (taggedStep_isMaterial first.legal hs)

theorem initialTwoFormulas_isMaterial {r q : ℕ} (e : Expr signature r) (f : Expr signature q)
    (he : IsMaterialExpression e) (hf : IsMaterialExpression f) (j k : ℕ) :
    IsMaterialForest (initialTwoFormulas e f j k) := by
  simp [initialTwoFormulas,IsMaterialPending,he,hf]

/-- Every actual terminal branch keeps the restricted material grammar; score leaves
are allowed separately, and a standalone derivative constructor cannot occur. -/
theorem terminalBranch_isMaterial {r q : ℕ} (e : Expr signature r) (f : Expr signature q)
    (he : IsMaterialExpression e) (hf : IsMaterialExpression f) (j k : ℕ)
    (run : List Event × List (TaggedPending signature))
    (hr : run ∈ terminalBranches (initialTwoFormulas e f j k)
      (initialTwoFormulas_support_nodup e f j k)
      (initialTwoFormulas_inventory_nodup e f j k)) : IsMaterialForest run.2 := by
  have htrace := ((ExpansionTree.build (initialTwoFormulas e f j k)
    (initialTwoFormulas_support_nodup e f j k)
    (initialTwoFormulas_inventory_nodup e f j k)).branch_sound run hr).1
  exact legalTrace_isMaterial htrace (initialTwoFormulas_isMaterial e f he hf j k)

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
