import AcceleratedLogConcave.Tensor.ReductionBudgets

/-!
# Origin-tagged structural reduction

Permutation nodes remain in the syntax and reduction, but do not consume an
address component. Tags distinguish occurrences rather than coefficient values.
This module supplies the tagged local relation and its literal erasure; a global
terminal-record reconstruction theorem is a separate obligation.
-/

open scoped NNReal

namespace AcceleratedLogConcave.Tensor

namespace Expr
variable {Name : Type*} {σ : CoefficientSignature Name} {r : ℕ}

/-- Ordered leaf addresses after collapsing only permutation edges. -/
def collapsedLeafAddresses : {r : ℕ} → Expr σ r → List (List Bool)
  | _, .coefficient _ => [[]]
  | _, .permute _ e => collapsedLeafAddresses e
  | _, .contract e f _ _ =>
      (collapsedLeafAddresses e).map (List.cons false) ++
      (collapsedLeafAddresses f).map (List.cons true)
  | _, .derivative e => (collapsedLeafAddresses e).map (List.cons false)
  | _, .adjoint _ e => (collapsedLeafAddresses e).map (List.cons false)

theorem collapsedLeafAddresses_length (e : Expr σ r) :
    e.collapsedLeafAddresses.length = e.coefficients.length := by
  induction e <;> simp_all [collapsedLeafAddresses, coefficients]

theorem collapsedLeafAddresses_nodup (e : Expr σ r) :
    e.collapsedLeafAddresses.Nodup := by
  have prefixed {l : List (List Bool)} (b : Bool) (h : l.Nodup) :
      (l.map (List.cons b)).Nodup :=
    h.map (fun _ _ hh => (List.cons.inj hh).2)
  induction e with
  | coefficient c => simp [collapsedLeafAddresses]
  | permute p e ih => exact ih
  | derivative e ih => exact prefixed false ih
  | adjoint i e ih => exact prefixed false ih
  | contract e f i j ih₁ ih₂ =>
    refine List.nodup_append.mpr ⟨prefixed false ih₁, prefixed true ih₂, ?_⟩
    intro a ha b hb hab
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hb
    exact Bool.false_ne_true (List.cons.inj hab).1

/-- The index is a coefficient occurrence, so equal names retain multiplicity. -/
def collapsedOccurrenceAddress (e : Expr σ r) (i : e.Occurrence) : List Bool :=
  e.collapsedLeafAddresses.get
    ⟨i.val, by rw [e.collapsedLeafAddresses_length]; exact i.isLt⟩

theorem collapsedOccurrenceAddress_injective (e : Expr σ r) :
    Function.Injective e.collapsedOccurrenceAddress := by
  intro i j h
  have hh := e.collapsedLeafAddresses_nodup.injective_get h
  apply Fin.ext
  exact congrArg (fun z : Fin e.collapsedLeafAddresses.length => z.val) hh
end Expr

namespace AdjointReduction.ReductionRecords
variable {Name Label E : Type*} {σ : CoefficientSignature Name}

/-- Root position separates equal copies of the same original expression. -/
structure NodeAddress where
  root : ℕ
  path : List Bool
  deriving DecidableEq

def NodeAddress.child (a : NodeAddress) (b : Bool) : NodeAddress :=
  ⟨a.root, a.path ++ [b]⟩

inductive OccurrenceTag
  | formula (node : NodeAddress)
  | score (creator : NodeAddress)
  deriving DecidableEq

inductive LabelOrigin
  | initial (root position : ℕ)
  | derivative (node : NodeAddress)
  | ibp (node : NodeAddress)
  deriving DecidableEq

/-- Values are fixed separately: an origin cannot silently change direction. -/
structure OriginValues (Label E : Type*) where
  label : LabelOrigin → Label
  direction : Label → E

/-- Both adjoint branches use one symbolic wire; its numeric interpretation may
coincide with other wires and is never required to be injective. -/
def OriginValues.score (v : OriginValues Label E) (a : NodeAddress) : E :=
  v.direction (v.label (.ibp a))

inductive TaggedPending (σ : CoefficientSignature Name)
  | formula {r : ℕ} (node : NodeAddress) (expression : Expr σ r)
      (labels : List LabelOrigin)
  | score (creator : NodeAddress) (labels : List LabelOrigin) (nonempty : labels ≠ [])

namespace TaggedPending

def tag : TaggedPending σ → OccurrenceTag
  | .formula a _ _ => .formula a
  | .score a _ _ => .score a

def labels : TaggedPending σ → List LabelOrigin
  | .formula _ _ J => J
  | .score _ J _ => J

def decorate (i : LabelOrigin) : TaggedPending σ → TaggedPending σ
  | .formula a e J => .formula a e (i :: J)
  | .score a J _ => .score a (i :: J) (by simp)

def erase (v : OriginValues Label E) : TaggedPending σ → Pending σ Label E
  | .formula _ e J => .formula e (J.map v.label)
  | .score a J h => .score (v.score a) (J.map v.label) (by simpa using h)

@[simp] theorem erase_decorate (v : OriginValues Label E) (i : LabelOrigin)
    (p : TaggedPending σ) :
    (p.decorate i).erase v = (p.erase v).decorate (v.label i) := by cases p <;> rfl

@[simp] theorem tag_decorate (i : LabelOrigin) (p : TaggedPending σ) :
    (p.decorate i).tag = p.tag := by cases p <;> rfl

@[simp] theorem labels_decorate (i : LabelOrigin) (p : TaggedPending σ) :
    (p.decorate i).labels = i :: p.labels := by cases p <;> rfl
end TaggedPending

def eraseForest (v : OriginValues Label E) (s : List (TaggedPending σ)) :
    List (Pending σ Label E) := s.map (TaggedPending.erase v)

theorem route_map {L M : Type*} (f : L → M) {J A B : List L}
    (h : (A, B) ∈ routes J) : (A.map f, B.map f) ∈ routes (J.map f) := by
  induction J generalizing A B with
  | nil => simp [routes] at h; obtain ⟨rfl, rfl⟩ := h; simp [routes]
  | cons i J ih =>
    simp only [routes, List.mem_append, List.mem_map] at h
    rcases h with ⟨⟨C, D⟩, h, he⟩ | ⟨⟨C, D⟩, h, he⟩
    · cases he
      exact List.mem_append_left _ (List.mem_map.mpr ⟨_, ih h, rfl⟩)
    · cases he
      exact List.mem_append_right _ (List.mem_map.mpr ⟨_, ih h, rfl⟩)

theorem scoreRoute_map {L M : Type*} (f : L → M) {J A B : List L}
    (h : (A, B) ∈ scoreRoutes J) :
    (A.map f, B.map f) ∈ scoreRoutes (J.map f) := by
  have hroute : (A, B) ∈ routes J := by
    rw [routes_eq]; exact List.mem_cons_of_mem _ h
  have hr := route_map f hroute
  rw [routes_eq] at hr
  rcases List.mem_cons.mp hr with he | he
  · have hn := scoreRoutes_left_ne_nil J (A, B) h
    have ha : A.map f = [] := congrArg Prod.fst he
    exact False.elim (hn (List.map_eq_nil_iff.mp ha))
  · exact he

/-- Destination ownership determines both ordered parts of a legal route.
The statement preserves repeated values; it does not replace lists by sets. -/
theorem route_eq_filter {L : Type*} (left : L → Bool) {J A B : List L}
    (h : (A, B) ∈ routes J)
    (hA : ∀ x ∈ A, left x = true) (hB : ∀ x ∈ B, left x = false) :
    A = J.filter left ∧ B = J.filter (fun x => !(left x)) := by
  induction J generalizing A B with
  | nil => simp [routes] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | cons i J ih =>
    simp only [routes, List.mem_append, List.mem_map] at h
    rcases h with ⟨⟨C, D⟩, h, he⟩ | ⟨⟨C, D⟩, h, he⟩
    · cases he
      have hi := hB i (by simp)
      obtain ⟨hc, hd⟩ := ih h hA (fun x hx => hB x (by simp [hx]))
      simp [hi, hc, hd]
    · cases he
      have hi := hA i (by simp)
      obtain ⟨hc, hd⟩ := ih h (fun x hx => hA x (by simp [hx])) hB
      simp [hi, hc, hd]

/-- Two legal partitions consistent with the same destination ownership coincide. -/
theorem route_unique_of_destinations {L : Type*} (left : L → Bool)
    {J A B C D : List L} (h : (A, B) ∈ routes J) (k : (C, D) ∈ routes J)
    (hA : ∀ x ∈ A, left x = true) (hB : ∀ x ∈ B, left x = false)
    (hC : ∀ x ∈ C, left x = true) (hD : ∀ x ∈ D, left x = false) :
    A = C ∧ B = D := by
  obtain ⟨ha, hb⟩ := route_eq_filter left h hA hB
  obtain ⟨hc, hd⟩ := route_eq_filter left k hC hD
  exact ⟨ha.trans hc.symm, hb.trans hd.symm⟩

/-- Local event payload. Silent permutations are retained in a legal trace,
although they will not be paid choices in a terminal routing record. -/
inductive Event
  | permute (node : NodeAddress)
  | derivative (node : NodeAddress)
  | contract (node : NodeAddress) (left right : List LabelOrigin)
  | score (node : NodeAddress) (left right : List LabelOrigin)
  | ibp (node : NodeAddress) (recipient : OccurrenceTag)
  deriving DecidableEq

def Event.node : Event → NodeAddress
  | .permute a | .derivative a | .contract a _ _ | .score a _ _ | .ibp a _ => a

def Event.contractions : Event → ℕ
  | .contract .. => 1
  | _ => 0

def Event.scores : Event → ℕ
  | .score .. => 1
  | _ => 0

/-- The six literal constructors, with origin creation fixed by the redex node.
IBP recipients are different positions; tag uniqueness is a forest invariant,
not an equality test on erased tensor values. -/
inductive TaggedStep : Event → List (TaggedPending σ) → List (TaggedPending σ) → Prop
  | permute {r : ℕ} (a) (p : Equiv.Perm (Fin r)) (e : Expr σ r) (J)
      (before after : List (TaggedPending σ)) :
      TaggedStep (.permute a) (before ++ [.formula a e J] ++ after)
        (before ++ [.formula a (.permute p e) J] ++ after)
  | derivative {r : ℕ} (a) (e : Expr σ r) (J)
      (before after : List (TaggedPending σ)) :
      TaggedStep (.derivative a) (before ++ [.formula (a.child false) e (J ++ [.derivative a])] ++ after)
        (before ++ [.formula a (.derivative e) J] ++ after)
  | contract {r s : ℕ} (a) (e : Expr σ (r+2)) (f : Expr σ (s+2))
      (i : Fin (r+2)) (j : Fin (s+2)) (J A B)
      (route : (A, B) ∈ routes J) (before after : List (TaggedPending σ)) :
      TaggedStep (.contract a A B) (before ++ [.formula (a.child false) e A,
        .formula (a.child true) f B] ++ after)
        (before ++ [.formula a (.contract e f i j) J] ++ after)
  | score {r : ℕ} (a) (e : Expr σ (r+2)) (i : Fin (r+2)) (J A B)
      (route : (A, B) ∈ scoreRoutes J) (before after : List (TaggedPending σ)) :
      TaggedStep (.score a A B) (before ++ [.score a A (scoreRoutes_left_ne_nil J (A, B) route),
        .formula (a.child false) e B] ++ after)
        (before ++ [.formula a (.adjoint i e) J] ++ after)
  | ibpAfter {r : ℕ} (a) (e : Expr σ (r+2)) (i : Fin (r+2)) (J)
      (other : TaggedPending σ) (before between after : List (TaggedPending σ)) :
      TaggedStep (.ibp a other.tag) (before ++ [.formula (a.child false) e J] ++ between ++
        [other.decorate (.ibp a)] ++ after)
        (before ++ [.formula a (.adjoint i e) J] ++ between ++ [other] ++ after)
  | ibpBefore {r : ℕ} (a) (e : Expr σ (r+2)) (i : Fin (r+2)) (J)
      (other : TaggedPending σ) (before between after : List (TaggedPending σ)) :
      TaggedStep (.ibp a other.tag) (before ++ [other.decorate (.ibp a)] ++ between ++
        [.formula (a.child false) e J] ++ after)
        (before ++ [other] ++ between ++ [.formula a (.adjoint i e) J] ++ after)

/-- Literal erasure retains every ordered forest position and label value. -/
theorem TaggedStep.erase (v : OriginValues Label E) {s t : List (TaggedPending σ)}
    {event : Event} (h : TaggedStep event t s) : Step (eraseForest v t) (eraseForest v s) := by
  cases h with
  | permute a p e J before after =>
    simpa [eraseForest, TaggedPending.erase] using
      Step.permute p e (J.map v.label) (eraseForest v before) (eraseForest v after)
  | derivative a e J before after =>
    simpa [eraseForest, TaggedPending.erase] using
      Step.derivative e (J.map v.label) (v.label (.derivative a))
        (eraseForest v before) (eraseForest v after)
  | contract a e f i j J A B h before after =>
    simpa [eraseForest, TaggedPending.erase] using
      Step.contract e f i j _ _ _ (route_map v.label h)
        (eraseForest v before) (eraseForest v after)
  | score a e i J A B h before after =>
    simpa [eraseForest, TaggedPending.erase] using
      Step.score e i (v.score a) _ _ _ (scoreRoute_map v.label h)
        (eraseForest v before) (eraseForest v after)
  | ibpAfter a e i J other before between after =>
    have hs := Step.ibpAfter e i (J.map v.label) (v.label (.ibp a)) (other.erase v)
        (eraseForest v before) (eraseForest v between) (eraseForest v after)
    cases other <;> simpa [eraseForest, TaggedPending.erase,
      TaggedPending.decorate, Pending.decorate] using hs
  | ibpBefore a e i J other before between after =>
    have hs := Step.ibpBefore e i (J.map v.label) (v.label (.ibp a)) (other.erase v)
        (eraseForest v before) (eraseForest v between) (eraseForest v after)
    cases other <;> simpa [eraseForest, TaggedPending.erase,
      TaggedPending.decorate, Pending.decorate] using hs

/-- Exact event-indexed budget changes, rather than existential loss counters. -/
theorem TaggedStep.budgets (v : OriginValues Label E) {s t : List (TaggedPending σ)}
    {event : Event} (h : TaggedStep event t s) :
    forestSize (eraseForest v t) + event.contractions = forestSize (eraseForest v s) ∧
    forestLabels (eraseForest v t) + event.scores = forestLabels (eraseForest v s) ∧
    forestSmoothing (eraseForest v t) + 2 * (event.scores : ℝ≥0) =
      forestSmoothing (eraseForest v s) := by
  cases h with
  | permute =>
    simp [eraseForest, TaggedPending.erase, forestSize, forestLabels, forestSmoothing,
      Pending.sizeBudget, Pending.labelBudget, Pending.smoothingBudget,
      Expr.size, Expr.weightedOperationCount, Expr.weight, Event.contractions, Event.scores]
  | derivative =>
    simp only [eraseForest, List.map_append, List.map_cons, List.map_nil,
      TaggedPending.erase, forestSize, forestLabels, forestSmoothing,
      List.sum_append, List.sum_cons, List.sum_nil,
      Pending.sizeBudget, Pending.labelBudget, Pending.smoothingBudget,
      Expr.size, Expr.weightedOperationCount, Expr.weight,
      List.length_append, List.length_cons, List.length_nil, List.length_map,
      Event.contractions, Event.scores, Nat.cast_zero, mul_zero, add_zero]
    refine ⟨by omega, by omega, ?_⟩
    push_cast
    ring
  | contract a e f i j J A B route before after =>
    have hr : A.length + B.length = J.length := route_length J (A, B) route
    have hrw : (A.length : ℝ≥0) + B.length = J.length := by exact_mod_cast hr
    simp only [eraseForest, List.map_append, List.map_cons, List.map_nil,
      TaggedPending.erase, forestSize, forestLabels, forestSmoothing,
      List.sum_append, List.sum_cons, List.sum_nil,
      Pending.sizeBudget, Pending.labelBudget, Pending.smoothingBudget,
      Expr.size, Expr.weightedOperationCount, Expr.weight, List.length_map,
      Event.contractions, Event.scores, Nat.cast_zero, mul_zero, add_zero]
    refine ⟨by omega, by omega, ?_⟩
    linear_combination hrw
  | score a e i J A B route before after =>
    have hr := scoreRoute_length J A B route
    have hp : 0 < A.length := List.length_pos_iff.mpr
      (scoreRoutes_left_ne_nil J (A, B) route)
    have hrw : ((A.length - 1 : ℕ) : ℝ≥0) + B.length + 1 = J.length := by
      exact_mod_cast (show A.length - 1 + B.length + 1 = J.length by omega)
    simp only [eraseForest, List.map_append, List.map_cons, List.map_nil,
      TaggedPending.erase, forestSize, forestLabels, forestSmoothing,
      List.sum_append, List.sum_cons, List.sum_nil,
      Pending.sizeBudget, Pending.labelBudget, Pending.smoothingBudget,
      Expr.size, Expr.weightedOperationCount, Expr.weight, List.length_map,
      Event.contractions, Event.scores, Nat.cast_one, mul_one, add_zero]
    refine ⟨by omega, by omega, ?_⟩
    linear_combination hrw
  | ibpAfter a e i J other before between after
  | ibpBefore a e i J other before between after =>
    simp only [eraseForest, List.map_append, List.map_cons, List.map_nil]
    rw [TaggedPending.erase_decorate]
    simp only [forestSize, forestLabels, forestSmoothing,
      List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil]
    rw [Pending.sizeBudget_decorate, Pending.labelBudget_decorate,
      Pending.smoothingBudget_decorate]
    simp only [TaggedPending.erase, Pending.sizeBudget, Pending.labelBudget,
      Pending.smoothingBudget, Expr.size, Expr.weightedOperationCount, Expr.weight,
      Event.contractions, Event.scores, Nat.cast_zero, mul_zero, add_zero]
    exact ⟨by omega, by omega, by ring⟩

/-- Each branch creates precisely one occurrence at contraction or score. -/
theorem TaggedStep.length {s t : List (TaggedPending σ)} {event : Event}
    (h : TaggedStep event t s) :
    t.length = s.length + event.contractions + event.scores := by
  cases h <;> simp [Event.contractions, Event.scores] <;> omega

/-- Syntactic permutations are still actual rank-decreasing steps. -/
theorem TaggedStep.rank (v : OriginValues Label E) {s t : List (TaggedPending σ)}
    {event : Event} (h : TaggedStep event t s) :
    forestRank (eraseForest v t) + 1 = forestRank (eraseForest v s) :=
  step_rank (h.erase v)

/-- Inspect the actual syntax: permutations are nonterminal silent steps. -/
def TaggedPending.activeNode : TaggedPending σ → Option NodeAddress
  | .formula _ (.coefficient _) _ => none
  | .formula a _ _ => some a
  | .score _ _ _ => none

/-- The forest is always scheduled in its original list order. -/
def firstNonterminal : List (TaggedPending σ) → Option NodeAddress
  | [] => none
  | p :: ps => p.activeNode.or (firstNonterminal ps)

/-- A legal local step at precisely the first nonterminal occurrence. -/
structure CanonicalStep (event : Event) (t s : List (TaggedPending σ)) : Prop where
  legal : TaggedStep event t s
  scheduled : firstNonterminal s = some event.node

theorem CanonicalStep.same_scheduled_node {s t u : List (TaggedPending σ)}
    {a b : Event} (ha : CanonicalStep a t s) (hb : CanonicalStep b u s) :
    a.node = b.node := Option.some.inj (ha.scheduled.symm.trans hb.scheduled)

/-- Event lists are data; legality is a separate proposition about actual states. -/
inductive LegalTrace : List Event → List (TaggedPending σ) → List (TaggedPending σ) → Prop
  | nil (s) : LegalTrace [] s s
  | cons {event events s t u} (first : CanonicalStep event t s)
      (rest : LegalTrace events t u) : LegalTrace (event :: events) s u

theorem LegalTrace.erase (v : OriginValues Label E) {events s t}
    (h : LegalTrace (σ := σ) events s t) :
    Steps events.length (eraseForest v s) (eraseForest v t) := by
  induction h with
  | nil => exact Steps.zero _
  | cons first rest ih => exact Steps.succ (first.legal.erase v) ih

theorem LegalTrace.budgets (v : OriginValues Label E) {events s t}
    (h : LegalTrace (σ := σ) events s t) :
    forestSize (eraseForest v t) + (events.map Event.contractions).sum =
      forestSize (eraseForest v s) ∧
    forestLabels (eraseForest v t) + (events.map Event.scores).sum =
      forestLabels (eraseForest v s) ∧
    forestSmoothing (eraseForest v t) +
      2 * ((events.map Event.scores).sum : ℝ≥0) = forestSmoothing (eraseForest v s) := by
  induction h with
  | nil => simp
  | cons first rest ih =>
    obtain ⟨hs, hl, hw⟩ := first.legal.budgets v
    simp only [List.map_cons, List.sum_cons]
    refine ⟨by omega, by omega, ?_⟩
    rw [Nat.cast_add]
    linear_combination ih.2.2 + hw

theorem LegalTrace.length {events s t} (h : LegalTrace (σ := σ) events s t) :
    t.length = s.length + (events.map Event.contractions).sum +
      (events.map Event.scores).sum := by
  induction h with
  | nil => simp
  | cons first rest ih =>
    have := first.legal.length
    simp only [List.map_cons, List.sum_cons]
    omega

/-- Equal tensor values do not identify recipients: a unique tag fixes a list position. -/
theorem recipient_index_unique (s : List (TaggedPending σ))
    (h : (s.map TaggedPending.tag).Nodup) (i j : Fin s.length)
    (he : (s.get i).tag = (s.get j).tag) : i = j := by
  have hi : i.val < (s.map TaggedPending.tag).length := by simp
  have hj : j.val < (s.map TaggedPending.tag).length := by simp
  have he' : (s.map TaggedPending.tag).get ⟨i.val, hi⟩ =
      (s.map TaggedPending.tag).get ⟨j.val, hj⟩ := by simpa using he
  have hh := h.injective_get he'
  exact Fin.ext (congrArg (fun z : Fin (s.map TaggedPending.tag).length => z.val) hh)

/-- A legal IBP step really targets another tagged occurrence in a unique-tag forest. -/
theorem TaggedStep.ibp_recipient_ne_redex {s t : List (TaggedPending σ)}
    {a : NodeAddress} {recipient : OccurrenceTag}
    (h : TaggedStep (.ibp a recipient) t s) (hs : (s.map TaggedPending.tag).Nodup) :
    recipient ≠ .formula a := by
  cases h with
  | ibpAfter a e i J other before between after =>
    have hs' := (List.nodup_append.mp (show ((before.map TaggedPending.tag) ++
      [OccurrenceTag.formula a] ++ between.map TaggedPending.tag ++ [other.tag] ++
      after.map TaggedPending.tag).Nodup by simpa [TaggedPending.tag] using hs)).1
    have hd := (List.nodup_append.mp hs').2.2
    intro he
    exact hd (.formula a) (by simp) other.tag (by simp) he.symm
  | ibpBefore a e i J other before between after =>
    have hs' := (List.nodup_append.mp (show ((before.map TaggedPending.tag) ++
      [other.tag] ++ between.map TaggedPending.tag ++ [OccurrenceTag.formula a] ++
      after.map TaggedPending.tag).Nodup by simpa [TaggedPending.tag] using hs)).1
    have hd := (List.nodup_append.mp hs').2.2
    intro he
    exact hd other.tag (by simp) (.formula a) (by simp) he

/-- Attached origins retain positional multiplicity, even when values coincide. -/
def attachedOrigins (s : List (TaggedPending σ)) : List LabelOrigin :=
  s.flatMap TaggedPending.labels

/-- Only derivative and principal IBP events create an attached origin. -/
def Event.createdOrigins : Event → Multiset LabelOrigin
  | .derivative a => {.derivative a}
  | .ibp a _ => {.ibp a}
  | _ => 0

private theorem origin_cons (a : LabelOrigin) (J : List LabelOrigin) :
    ((a :: J : List LabelOrigin) : Multiset LabelOrigin) = {a} + J := rfl

private theorem origin_singleton (a : LabelOrigin) :
    (([a] : List LabelOrigin) : Multiset LabelOrigin) = {a} := rfl

/-- Routing redistributes attached origins; derivative and IBP add exactly one. -/
theorem TaggedStep.origins {s t : List (TaggedPending σ)} {event : Event}
    (h : TaggedStep event t s) :
    (attachedOrigins t : Multiset LabelOrigin) =
      (attachedOrigins s : Multiset LabelOrigin) + event.createdOrigins := by
  cases h with
  | permute =>
    simp only [attachedOrigins, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, TaggedPending.labels, Event.createdOrigins, add_zero]
  | derivative =>
    simp only [attachedOrigins, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, TaggedPending.labels, Event.createdOrigins,
      ← Multiset.coe_add, origin_cons, Multiset.coe_nil]
    abel
  | contract a e f i j J A B route before after =>
    have hr : (A : Multiset LabelOrigin) + B = J := by
      exact Multiset.coe_eq_coe.mpr (route_perm J (A, B) route)
    simp only [attachedOrigins, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, TaggedPending.labels, List.append_nil,
      ← Multiset.coe_add, Event.createdOrigins, add_zero]
    simpa only [attachedOrigins, add_assoc] using congrArg
      (fun x : Multiset LabelOrigin => (attachedOrigins before : Multiset LabelOrigin) +
        x + (attachedOrigins after : Multiset LabelOrigin)) hr
  | score a e i J A B route before after =>
    have hr : (A : Multiset LabelOrigin) + B = J := by
      apply Multiset.coe_eq_coe.mpr
      exact route_perm J (A, B) (by rw [routes_eq]; exact List.mem_cons_of_mem _ route)
    simp only [attachedOrigins, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, TaggedPending.labels, List.append_nil,
      ← Multiset.coe_add, Event.createdOrigins, add_zero]
    simpa only [attachedOrigins, add_assoc] using congrArg
      (fun x : Multiset LabelOrigin => (attachedOrigins before : Multiset LabelOrigin) +
        x + (attachedOrigins after : Multiset LabelOrigin)) hr
  | ibpAfter a e i J other before between after
  | ibpBefore a e i J other before between after =>
    cases other <;> simp only [attachedOrigins, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, TaggedPending.decorate, TaggedPending.labels,
      Event.createdOrigins, ← Multiset.coe_add, origin_cons,
      Multiset.coe_nil] <;> abel

/-- Freshness is checked against the entire old forest, including score leaves. -/
def Event.FreshFor (event : Event) (s : List (TaggedPending σ)) : Prop :=
  ∀ o ∈ event.createdOrigins, o ∉ attachedOrigins s

theorem Event.createdOrigins_nodup (event : Event) : event.createdOrigins.Nodup := by
  cases event <;> simp [Event.createdOrigins]

/-- Routing cannot identify distinct origins; new origins need explicit freshness. -/
theorem TaggedStep.origins_nodup {s t : List (TaggedPending σ)} {event : Event}
    (h : TaggedStep event t s) (hs : (attachedOrigins s).Nodup)
    (hf : event.FreshFor s) : (attachedOrigins t).Nodup := by
  apply Multiset.coe_nodup.mp
  rw [h.origins]
  apply Multiset.nodup_add.mpr
  refine ⟨Multiset.coe_nodup.mpr hs, event.createdOrigins_nodup, ?_⟩
  rw [Multiset.disjoint_left]
  intro o ho he
  exact hf o he (by simpa using ho)


/-- Origins reserved by actual unexpanded syntax. Permutations reserve nothing. -/
def futureOrigins (a : NodeAddress) : {r : ℕ} → Expr σ r → Multiset LabelOrigin
  | _, .coefficient _ => 0
  | _, .permute _ e => futureOrigins a e
  | _, .contract e f _ _ => futureOrigins (a.child false) e + futureOrigins (a.child true) f
  | _, .derivative e => {.derivative a} + futureOrigins (a.child false) e
  | _, .adjoint _ e => {.ibp a} + futureOrigins (a.child false) e

def TaggedPending.futureOrigins : TaggedPending σ → Multiset LabelOrigin
  | .formula a e _ => ReductionRecords.futureOrigins a e
  | .score .. => 0

def forestFutureOrigins (s : List (TaggedPending σ)) : Multiset LabelOrigin :=
  (s.map TaggedPending.futureOrigins).sum

/-- A score choice uses the adjoint wire as score direction, retiring its
reserved attached-derivative occurrence. The symbolic wire itself remains. -/
def Event.retiredOrigins : Event → Multiset LabelOrigin
  | .score a _ _ => {.ibp a}
  | _ => 0

theorem TaggedStep.future_origins {s t : List (TaggedPending σ)} {event : Event}
    (h : TaggedStep event t s) :
    forestFutureOrigins t + event.createdOrigins + event.retiredOrigins =
      forestFutureOrigins s := by
  cases h with
  | ibpAfter a e i J other before between after
  | ibpBefore a e i J other before between after =>
    cases other <;>
      simp only [forestFutureOrigins, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil, TaggedPending.decorate,
        TaggedPending.futureOrigins, futureOrigins, Event.createdOrigins, Event.retiredOrigins] <;> abel
  | _ =>
    simp only [forestFutureOrigins, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil,
      TaggedPending.futureOrigins, futureOrigins, Event.createdOrigins, Event.retiredOrigins]
    abel

/-- Both live and still-reserved origins count, preventing reuse of a consumed node. -/
def originInventory (s : List (TaggedPending σ)) : Multiset LabelOrigin :=
  (attachedOrigins s : Multiset LabelOrigin) + forestFutureOrigins s

theorem TaggedStep.origin_inventory {s t : List (TaggedPending σ)} {event : Event}
    (h : TaggedStep event t s) :
    originInventory t + event.retiredOrigins = originInventory s := by
  unfold originInventory
  rw [h.origins]
  have hf := h.future_origins
  calc
    _ = (attachedOrigins s : Multiset LabelOrigin) +
        (forestFutureOrigins t + event.createdOrigins + event.retiredOrigins) := by abel
    _ = _ := by rw [hf]

/-- Freshness is a consequence of a syntax-reservation invariant, rather than an
extra premise imposed separately at every derivative or IBP event. -/
theorem TaggedStep.fresh_of_inventory {s t : List (TaggedPending σ)} {event : Event}
    (h : TaggedStep event t s) (hs : (originInventory s).Nodup) : event.FreshFor s := by
  have hd := (Multiset.nodup_add.mp hs).2.2
  intro o ho ha
  have hf : o ∈ forestFutureOrigins s := by
    rw [← h.future_origins]
    exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inr ho)))
  exact (Multiset.disjoint_left.mp hd) (by simpa using ha) hf

theorem TaggedStep.inventory_nodup {s t : List (TaggedPending σ)} {event : Event}
    (h : TaggedStep event t s) (hs : (originInventory s).Nodup) :
    (originInventory t).Nodup := by
  rw [← h.origin_inventory] at hs
  exact (Multiset.nodup_add.mp hs).1

theorem TaggedStep.attached_nodup_of_inventory {s t : List (TaggedPending σ)} {event : Event}
    (h : TaggedStep event t s) (hs : (originInventory s).Nodup) :
    (attachedOrigins t).Nodup := by
  exact Multiset.coe_nodup.mp (Multiset.nodup_add.mp (h.inventory_nodup hs)).1

theorem LegalTrace.inventory_nodup {events s t} (h : LegalTrace (σ := σ) events s t)
    (hs : (originInventory s).Nodup) : (originInventory t).Nodup := by
  induction h with
  | nil => exact hs
  | cons first rest ih => exact ih (first.legal.inventory_nodup hs)

theorem LegalTrace.origin_inventory {events s t} (h : LegalTrace (σ := σ) events s t) :
    originInventory t + (events.map Event.retiredOrigins).sum = originInventory s := by
  induction h with
  | nil => simp
  | cons first rest ih =>
    have hh := first.legal.origin_inventory
    simp only [List.map_cons, List.sum_cons]
    calc
      _ = (originInventory _ + (List.map Event.retiredOrigins _).sum) +
          Event.retiredOrigins _ := by abel
      _ = _ := by rw [ih, hh]

theorem TaggedPending.futureOrigins_eq_zero (p : TaggedPending σ)
    (h : p.activeNode = none) : p.futureOrigins = 0 := by
  cases p with
  | score => rfl
  | formula a e J => cases e <;> simp_all [TaggedPending.activeNode,
      TaggedPending.futureOrigins, ReductionRecords.futureOrigins]

theorem terminal_futureOrigins_eq_zero (s : List (TaggedPending σ))
    (h : ∀ p ∈ s, p.activeNode = none) : forestFutureOrigins s = 0 := by
  unfold forestFutureOrigins
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  exact p.futureOrigins_eq_zero (h p hp)
/-- Relative potential live tags: the Boolean distinguishes formula and score. -/
def relativeSupport : {r : ℕ} → Expr σ r → List (List Bool × Bool)
  | _, .coefficient _ => [([], false), ([], true)]
  | _, .permute _ e => relativeSupport e
  | _, .contract e f _ _ => [([], false), ([], true)] ++
      (relativeSupport e).map (fun p : List Bool × Bool => (false :: p.1, p.2)) ++
      (relativeSupport f).map (fun p : List Bool × Bool => (true :: p.1, p.2))
  | _, .derivative e => [([], false), ([], true)] ++
      (relativeSupport e).map (fun p : List Bool × Bool => (false :: p.1, p.2))
  | _, .adjoint _ e => [([], false), ([], true)] ++
      (relativeSupport e).map (fun p : List Bool × Bool => (false :: p.1, p.2))

private theorem prefixSupport_nodup (b : Bool) {l : List (List Bool × Bool)}
    (h : l.Nodup) : (l.map (fun p : List Bool × Bool => (b :: p.1, p.2))).Nodup := by
  apply h.map
  intro x y he
  apply Prod.ext
  · exact (List.cons.inj (congrArg Prod.fst he)).2
  · have hh := congrArg (fun p : List Bool × Bool => p.2) he
    exact hh

private theorem prefixedSupport_disjoint (l m : List (List Bool × Bool)) :
    List.Disjoint (l.map (fun p : List Bool × Bool => (false :: p.1, p.2)))
      (m.map (fun p : List Bool × Bool => (true :: p.1, p.2))) := by
  intro a ha hb
  obtain ⟨x, _, hx⟩ := List.mem_map.mp ha
  obtain ⟨y, _, hy⟩ := List.mem_map.mp hb
  exact Bool.false_ne_true (List.cons.inj (congrArg Prod.fst (hx.trans hy.symm))).1

private theorem roots_prefix_nodup (b : Bool) {l : List (List Bool × Bool)}
    (h : l.Nodup) :
    ([([], false), ([], true)] ++ l.map (fun p : List Bool × Bool => (b :: p.1, p.2))).Nodup := by
  simp only [List.cons_append, List.nil_append, List.nodup_cons]
  refine ⟨?_, ?_, prefixSupport_nodup b h⟩ <;> simp

private theorem roots_two_prefix_nodup {l m : List (List Bool × Bool)}
    (hl : l.Nodup) (hm : m.Nodup) :
    ([([], false), ([], true)] ++ l.map (fun p : List Bool × Bool => (false :: p.1, p.2)) ++
      m.map (fun p : List Bool × Bool => (true :: p.1, p.2))).Nodup := by
  rw [List.append_assoc]
  simp only [List.cons_append, List.nil_append, List.nodup_cons]
  refine ⟨?_, ?_, List.nodup_append.mpr
    ⟨prefixSupport_nodup false hl, prefixSupport_nodup true hm,
      fun a ha b hb he => prefixedSupport_disjoint l m ha (he ▸ hb)⟩⟩ <;> simp

theorem relativeSupport_nodup {r : ℕ} (e : Expr σ r) : (relativeSupport e).Nodup := by
  induction e with
  | coefficient => simp [relativeSupport]
  | permute p e ih => exact ih
  | derivative e ih => exact roots_prefix_nodup false ih
  | adjoint i e ih => exact roots_prefix_nodup false ih
  | contract e f i j ih ih' => exact roots_two_prefix_nodup ih ih'

def tagAt (a : NodeAddress) (p : List Bool × Bool) : OccurrenceTag :=
  if p.2 then .score ⟨a.root, a.path ++ p.1⟩ else .formula ⟨a.root, a.path ++ p.1⟩

theorem tagAt_injective (a : NodeAddress) : Function.Injective (tagAt a) := by
  rintro ⟨p, b⟩ ⟨q, c⟩ h
  cases b <;> cases c <;> simp only [tagAt, Bool.false_eq_true, ↓reduceIte,
     OccurrenceTag.formula.injEq, OccurrenceTag.score.injEq,
    NodeAddress.mk.injEq, true_and, List.append_cancel_left_eq] at h ⊢ <;>
    simp_all

def expressionSupport (a : NodeAddress) {r : ℕ} (e : Expr σ r) : List OccurrenceTag :=
  (relativeSupport e).map (tagAt a)

theorem expressionSupport_nodup (a : NodeAddress) {r : ℕ} (e : Expr σ r) :
    (expressionSupport a e).Nodup := (relativeSupport_nodup e).map (tagAt_injective a)

private theorem tagAt_prefix (a : NodeAddress) (b : Bool) (p : List Bool × Bool) :
    tagAt a (b :: p.1, p.2) = tagAt (a.child b) p := by
  rcases p with ⟨p, c⟩
  cases c <;> simp [tagAt, NodeAddress.child, List.append_assoc]

@[simp] theorem expressionSupport_coefficient (a : NodeAddress) (c : Name) :
    expressionSupport a (.coefficient (σ := σ) c) = [.formula a, .score a] := by
  cases a; simp [expressionSupport, relativeSupport, tagAt]

@[simp] theorem expressionSupport_permute {r : ℕ} (a : NodeAddress)
    (p : Equiv.Perm (Fin r)) (e : Expr σ r) :
    expressionSupport a (.permute p e) = expressionSupport a e := rfl

@[simp] theorem expressionSupport_derivative {r : ℕ} (a : NodeAddress) (e : Expr σ r) :
    expressionSupport a (.derivative e) =
      [.formula a, .score a] ++ expressionSupport (a.child false) e := by
  simp [expressionSupport, relativeSupport, List.map_map, Function.comp_def, tagAt_prefix]
  cases a; simp [tagAt]

@[simp] theorem expressionSupport_adjoint {r : ℕ} (a : NodeAddress)
    (e : Expr σ (r+2)) (i : Fin (r+2)) :
    expressionSupport a (.adjoint i e) =
      [.formula a, .score a] ++ expressionSupport (a.child false) e := by
  simp [expressionSupport, relativeSupport, List.map_map, Function.comp_def, tagAt_prefix]
  cases a; simp [tagAt]

@[simp] theorem expressionSupport_contract {r s : ℕ} (a : NodeAddress)
    (e : Expr σ (r+2)) (f : Expr σ (s+2)) (i : Fin (r+2)) (j : Fin (s+2)) :
    expressionSupport a (.contract e f i j) =
      [.formula a, .score a] ++ expressionSupport (a.child false) e ++
        expressionSupport (a.child true) f := by
  simp [expressionSupport, relativeSupport, List.map_map, Function.comp_def, tagAt_prefix]
  cases a; simp [tagAt]

namespace TaggedPending

def support : TaggedPending σ → List OccurrenceTag
  | .formula a e _ => expressionSupport a e
  | .score a _ _ => [.score a]

@[simp] theorem support_decorate (i : LabelOrigin) (p : TaggedPending σ) :
    (p.decorate i).support = p.support := by cases p <;> rfl

end TaggedPending

def forestSupport (s : List (TaggedPending σ)) : List OccurrenceTag :=
  s.flatMap TaggedPending.support

@[simp] theorem forestSupport_append (s t : List (TaggedPending σ)) :
    forestSupport (s ++ t) = forestSupport s ++ forestSupport t := List.flatMap_append

/-- Each literal rewrite only retires potential tags; it cannot introduce a collision. -/
theorem TaggedStep.support_sublist {s t : List (TaggedPending σ)} {event : Event}
    (h : TaggedStep event t s) : (forestSupport t).Sublist (forestSupport s) := by
  cases h with
  | permute => simp [forestSupport, TaggedPending.support]
  | derivative a e J before after =>
    simp only [forestSupport, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      TaggedPending.support, expressionSupport_derivative, List.append_nil]
    exact ((List.Sublist.refl _).append
      ((List.Sublist.refl _).cons (OccurrenceTag.score a) |>.cons (OccurrenceTag.formula a))).append
        (List.Sublist.refl _)
  | contract a e f i j J A B route before after =>
    simp only [forestSupport, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      TaggedPending.support, expressionSupport_contract, List.append_nil, List.append_assoc]
    exact (List.Sublist.refl _).append
      (((List.Sublist.refl _).cons (OccurrenceTag.score a) |>.cons (OccurrenceTag.formula a)).append
        (List.Sublist.refl _))
  | score a e i J A B route before after =>
    simp only [forestSupport, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      TaggedPending.support, expressionSupport_adjoint, List.append_nil, List.cons_append,
      List.nil_append]
    exact ((List.Sublist.refl _).append
      ((List.Sublist.refl _).cons (OccurrenceTag.formula a))).append (List.Sublist.refl _)
  | ibpAfter a e i J other before between after
  | ibpBefore a e i J other before between after =>
    cases other <;> simp only [forestSupport, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      TaggedPending.decorate, TaggedPending.support, expressionSupport_adjoint,
      List.append_nil] <;> first
    | exact ((((List.Sublist.refl _).append
        ((List.Sublist.refl _).cons (OccurrenceTag.score a) |>.cons (OccurrenceTag.formula a))).append
        (List.Sublist.refl _)).append (List.Sublist.refl _)).append (List.Sublist.refl _)
    | exact ((((List.Sublist.refl _).append (List.Sublist.refl _)).append (List.Sublist.refl _)).append
        ((List.Sublist.refl _).cons (OccurrenceTag.score a) |>.cons (OccurrenceTag.formula a))).append
        (List.Sublist.refl _)

theorem TaggedStep.support_nodup {s t : List (TaggedPending σ)} {event : Event}
    (h : TaggedStep event t s) (hs : (forestSupport s).Nodup) :
    (forestSupport t).Nodup := hs.sublist h.support_sublist
theorem expressionSupport_formula_mem (a : NodeAddress) {r : ℕ} (e : Expr σ r) :
    OccurrenceTag.formula a ∈ expressionSupport a e := by
  induction e generalizing a <;> simp_all

theorem TaggedPending.tag_mem_support (p : TaggedPending σ) : p.tag ∈ p.support := by
  cases p with
  | formula a e J => exact expressionSupport_formula_mem a e
  | score => simp [TaggedPending.tag, TaggedPending.support]

theorem liveTags_sublist_support (s : List (TaggedPending σ)) :
    (s.map TaggedPending.tag).Sublist (forestSupport s) := by
  induction s with
  | nil => simp [forestSupport]
  | cons p ps ih =>
    change ([p.tag] ++ ps.map TaggedPending.tag).Sublist (p.support ++ forestSupport ps)
    exact (List.singleton_sublist.mpr p.tag_mem_support).append ih

theorem liveTags_nodup_of_support (s : List (TaggedPending σ))
    (hs : (forestSupport s).Nodup) : (s.map TaggedPending.tag).Nodup :=
  hs.sublist (liveTags_sublist_support s)

theorem LegalTrace.support_sublist {events s t} (h : LegalTrace (σ := σ) events s t) :
    (forestSupport t).Sublist (forestSupport s) := by
  induction h with
  | nil => exact List.Sublist.refl _
  | cons first rest ih => exact ih.trans first.legal.support_sublist

theorem LegalTrace.support_nodup {events s t} (h : LegalTrace (σ := σ) events s t)
    (hs : (forestSupport s).Nodup) : (forestSupport t).Nodup := hs.sublist h.support_sublist

def OccurrenceTag.root : OccurrenceTag → ℕ
  | .formula a | .score a => a.root

theorem expressionSupport_root (a : NodeAddress) {r : ℕ} (e : Expr σ r)
    (tag : OccurrenceTag) (h : tag ∈ expressionSupport a e) : tag.root = a.root := by
  obtain ⟨⟨p,b⟩, _, rfl⟩ := List.mem_map.mp h
  cases b <;> rfl

theorem expressionSupport_disjoint_roots (a b : NodeAddress) {r s : ℕ}
    (e : Expr σ r) (f : Expr σ s) (h : a.root ≠ b.root) :
    List.Disjoint (expressionSupport a e) (expressionSupport b f) := by
  intro tag ha hb
  exact h ((expressionSupport_root a e tag ha).symm.trans (expressionSupport_root b f tag hb))

theorem twoFormula_support_nodup (a b : NodeAddress) {r s : ℕ}
    (e : Expr σ r) (f : Expr σ s) (J K : List LabelOrigin) (h : a.root ≠ b.root) :
    (forestSupport [.formula a e J, .formula b f K]).Nodup := by
  simp only [forestSupport, List.flatMap_cons, List.flatMap_nil,
    TaggedPending.support, List.append_nil]
  apply List.nodup_append.mpr
  refine ⟨expressionSupport_nodup a e, expressionSupport_nodup b f, ?_⟩
  intro x hx y hy he
  exact expressionSupport_disjoint_roots a b e f h hx (he ▸ hy)

/-- Reserve the two possible fresh-origin kinds at every supported node. -/
def OccurrenceTag.asOrigin : OccurrenceTag → LabelOrigin
  | .formula a => .derivative a
  | .score a => .ibp a

theorem OccurrenceTag.asOrigin_injective : Function.Injective OccurrenceTag.asOrigin := by
  intro x y h
  cases x <;> cases y <;> simp_all [OccurrenceTag.asOrigin]

def originSupport (a : NodeAddress) {r : ℕ} (e : Expr σ r) : Multiset LabelOrigin :=
  ((expressionSupport a e).map OccurrenceTag.asOrigin : List LabelOrigin)

theorem originSupport_nodup (a : NodeAddress) {r : ℕ} (e : Expr σ r) :
    (originSupport a e).Nodup :=
  Multiset.coe_nodup.mpr ((expressionSupport_nodup a e).map OccurrenceTag.asOrigin_injective)

@[simp] theorem originSupport_permute (a : NodeAddress) {r : ℕ}
    (p : Equiv.Perm (Fin r)) (e : Expr σ r) :
    originSupport a (.permute p e) = originSupport a e := rfl

@[simp] theorem originSupport_derivative (a : NodeAddress) {r : ℕ} (e : Expr σ r) :
    originSupport a (.derivative e) =
      ({.derivative a} + {.ibp a}) + originSupport (a.child false) e := by
  simp only [originSupport, expressionSupport_derivative, List.map_append,
    List.map_cons, List.map_nil, OccurrenceTag.asOrigin, ← Multiset.coe_add]
  rfl

@[simp] theorem originSupport_adjoint (a : NodeAddress) {r : ℕ}
    (e : Expr σ (r+2)) (i : Fin (r+2)) :
    originSupport a (.adjoint i e) =
      ({.derivative a} + {.ibp a}) + originSupport (a.child false) e := by
  simp only [originSupport, expressionSupport_adjoint, List.map_append,
    List.map_cons, List.map_nil, OccurrenceTag.asOrigin, ← Multiset.coe_add]
  rfl

@[simp] theorem originSupport_contract (a : NodeAddress) {r s : ℕ}
    (e : Expr σ (r+2)) (f : Expr σ (s+2)) (i : Fin (r+2)) (j : Fin (s+2)) :
    originSupport a (.contract e f i j) =
      ({.derivative a} + {.ibp a}) + originSupport (a.child false) e +
        originSupport (a.child true) f := by
  simp only [originSupport, expressionSupport_contract, List.map_append,
    List.map_cons, List.map_nil, OccurrenceTag.asOrigin, ← Multiset.coe_add]
  rfl

theorem futureOrigins_le_originSupport (a : NodeAddress) {r : ℕ} (e : Expr σ r) :
    futureOrigins a e ≤ originSupport a e := by
  induction e generalizing a with
  | coefficient => exact zero_le
  | permute p e ih => exact ih a
  | derivative e ih =>
    simp only [futureOrigins, originSupport_derivative]
    exact add_le_add (by exact le_add_of_nonneg_right (zero_le)) (ih _)
  | adjoint i e ih =>
    simp only [futureOrigins, originSupport_adjoint]
    exact add_le_add (by exact le_add_of_nonneg_left (zero_le)) (ih _)
  | contract e f i j ih ih' =>
    simp only [futureOrigins, originSupport_contract]
    exact add_le_add ((ih _).trans (le_add_of_nonneg_left (zero_le))) (ih' _)

theorem futureOrigins_nodup (a : NodeAddress) {r : ℕ} (e : Expr σ r) :
    (futureOrigins a e).Nodup :=
  Multiset.nodup_of_le (futureOrigins_le_originSupport a e) (originSupport_nodup a e)

/-- Future origins have their node's root and cannot be initial origins. -/
theorem futureOrigins_root (a : NodeAddress) {r : ℕ} (e : Expr σ r)
    (o : LabelOrigin) (h : o ∈ futureOrigins a e) :
    ∃ b : NodeAddress, b.root = a.root ∧ (o = .derivative b ∨ o = .ibp b) := by
  have hm := Multiset.mem_of_le (futureOrigins_le_originSupport a e) h
  obtain ⟨tag, ht, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp hm)
  have hr := expressionSupport_root a e tag ht
  cases tag with
  | formula b => exact ⟨b, hr, Or.inl rfl⟩
  | score b => exact ⟨b, hr, Or.inr rfl⟩

theorem initial_not_mem_futureOrigins (a : NodeAddress) {r : ℕ} (e : Expr σ r)
    (root position : ℕ) : LabelOrigin.initial root position ∉ futureOrigins a e := by
  intro h
  obtain ⟨b, _, h | h⟩ := futureOrigins_root a e _ h <;> cases h

theorem futureOrigins_disjoint_roots (a b : NodeAddress) {r s : ℕ}
    (e : Expr σ r) (f : Expr σ s) (h : a.root ≠ b.root) :
    Disjoint (futureOrigins a e) (futureOrigins b f) := by
  rw [Multiset.disjoint_left]
  intro o ha hb
  obtain ⟨x, hx, hxa | hxa⟩ := futureOrigins_root a e o ha <;>
    obtain ⟨y, hy, hya | hya⟩ := futureOrigins_root b f o hb <;>
    simp_all


/-- Initial derivative positions are distinct even when their values coincide. -/
def initialLabels (root count : ℕ) : List LabelOrigin :=
  (List.range count).map (LabelOrigin.initial root)

theorem initialLabels_nodup (root count : ℕ) : (initialLabels root count).Nodup :=
  (List.nodup_range).map (fun _ _ h => (LabelOrigin.initial.inj h).2)

theorem initialLabels_disjoint (a b j k : ℕ) (h : a ≠ b) :
    List.Disjoint (initialLabels a j) (initialLabels b k) := by
  intro o ho hp
  obtain ⟨x, _, hx⟩ := List.mem_map.mp ho
  obtain ⟨y, _, hy⟩ := List.mem_map.mp hp
  exact h (LabelOrigin.initial.inj (hx.trans hy.symm)).1

def initialTwoFormulas {r s : ℕ} (e : Expr σ r) (f : Expr σ s) (j k : ℕ) :
    List (TaggedPending σ) :=
  [.formula ⟨0, []⟩ e (initialLabels 0 j), .formula ⟨1, []⟩ f (initialLabels 1 k)]

theorem initialTwoFormulas_support_nodup {r s : ℕ}
    (e : Expr σ r) (f : Expr σ s) (j k : ℕ) :
    (forestSupport (initialTwoFormulas e f j k)).Nodup :=
  twoFormula_support_nodup _ _ e f _ _ (by decide)

theorem initialTwoFormulas_inventory_nodup {r s : ℕ}
    (e : Expr σ r) (f : Expr σ s) (j k : ℕ) :
    (originInventory (initialTwoFormulas e f j k)).Nodup := by
  have hi : (initialLabels 0 j ++ initialLabels 1 k).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨initialLabels_nodup _ _, initialLabels_nodup _ _, ?_⟩
    intro a ha b hb he
    exact initialLabels_disjoint 0 1 j k (by decide) ha (he ▸ hb)
  have hf : (futureOrigins ⟨0, []⟩ e + futureOrigins ⟨1, []⟩ f).Nodup := by
    exact Multiset.nodup_add.mpr ⟨futureOrigins_nodup _ e, futureOrigins_nodup _ f,
      futureOrigins_disjoint_roots _ _ e f (by decide)⟩
  simp only [originInventory, initialTwoFormulas, attachedOrigins,
    List.flatMap_cons, List.flatMap_nil, TaggedPending.labels, forestFutureOrigins,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, TaggedPending.futureOrigins,
    List.append_nil, add_zero]
  apply Multiset.nodup_add.mpr
  refine ⟨Multiset.coe_nodup.mpr hi, hf, ?_⟩
  rw [Multiset.disjoint_left]
  intro o ho hp
  have ho' : o ∈ initialLabels 0 j ∨ o ∈ initialLabels 1 k := by simpa using ho
  rcases ho' with ho | ho <;>
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp ho <;>
    rcases Multiset.mem_add.mp hp with hp | hp
  all_goals exact initial_not_mem_futureOrigins _ _ _ _ hp

/-- The standard initial two copies automatically satisfy both origin invariants. -/
theorem LegalTrace.initialTwoFormulas_invariants {r q : ℕ} (e : Expr σ r) (f : Expr σ q)
    (j k : ℕ) {events t} (h : LegalTrace events (initialTwoFormulas e f j k) t) :
    (t.map TaggedPending.tag).Nodup ∧ (attachedOrigins t).Nodup := by
  refine ⟨liveTags_nodup_of_support t
    (h.support_nodup (initialTwoFormulas_support_nodup e f j k)), ?_⟩
  exact Multiset.coe_nodup.mp
    (Multiset.nodup_add.mp (h.inventory_nodup (initialTwoFormulas_inventory_nodup e f j k))).1

/-- Fixed original-syntax order for the origin inventory, excluding permutation nodes. -/
def futureOriginOrder (a : NodeAddress) : {r : ℕ} → Expr σ r → List LabelOrigin
  | _, .coefficient _ => []
  | _, .permute _ e => futureOriginOrder a e
  | _, .contract e f _ _ => futureOriginOrder (a.child false) e ++ futureOriginOrder (a.child true) f
  | _, .derivative e => .derivative a :: futureOriginOrder (a.child false) e
  | _, .adjoint _ e => .ibp a :: futureOriginOrder (a.child false) e

theorem futureOriginOrder_coe (a : NodeAddress) {r : ℕ} (e : Expr σ r) :
    (futureOriginOrder a e : Multiset LabelOrigin) = futureOrigins a e := by
  induction e generalizing a <;>
    simp_all [futureOriginOrder, futureOrigins, ← Multiset.coe_add, origin_cons]

def initialOriginOrder {r s : ℕ} (e : Expr σ r) (f : Expr σ s) (j k : ℕ) : List LabelOrigin :=
  initialLabels 0 j ++ initialLabels 1 k ++
    futureOriginOrder ⟨0, []⟩ e ++ futureOriginOrder ⟨1, []⟩ f

theorem initialOriginOrder_coe {r s : ℕ} (e : Expr σ r) (f : Expr σ s) (j k : ℕ) :
    (initialOriginOrder e f j k : Multiset LabelOrigin) =
      originInventory (initialTwoFormulas e f j k) := by
  simp [initialOriginOrder, originInventory, initialTwoFormulas, attachedOrigins,
    TaggedPending.labels, forestFutureOrigins, TaggedPending.futureOrigins,
    ← Multiset.coe_add, futureOriginOrder_coe, add_assoc]

theorem initialOriginOrder_nodup {r s : ℕ} (e : Expr σ r) (f : Expr σ s) (j k : ℕ) :
    (initialOriginOrder e f j k).Nodup := by
  apply Multiset.coe_nodup.mp
  rw [initialOriginOrder_coe]
  exact initialTwoFormulas_inventory_nodup e f j k

def LabelOrigin.adjointNode? : LabelOrigin → Option NodeAddress
  | .ibp a => some a
  | _ => none
/-- The paid terminal encoding does not contain silent permutation events or
per-step partitions. Reconstruction from this smaller data is not asserted here. -/
inductive AdjointChoice
  | score
  | ibp (recipient : OccurrenceTag)
  deriving DecidableEq

inductive Destination
  | coefficient (leaf : NodeAddress)
  | score (creator : NodeAddress)
  deriving DecidableEq

structure RawTerminalRecord where
  adjoints : List (NodeAddress × AdjointChoice)
  destinations : List (LabelOrigin × Destination)
  deriving DecidableEq

def TaggedPending.destination : TaggedPending σ → Destination
  | .formula a _ _ => .coefficient a
  | .score a _ _ => .score a

/-- At terminal states these are actual coefficient-leaf or score-creator destinations. -/
def terminalDestinations (s : List (TaggedPending σ)) : List (LabelOrigin × Destination) :=
  s.flatMap (fun p => p.labels.map (fun o => (o, p.destination)))

@[simp] theorem terminalDestinations_origins (s : List (TaggedPending σ)) :
    (terminalDestinations s).map Prod.fst = attachedOrigins s := by
  induction s with
  | nil => rfl
  | cons p s ih =>
    simp_all [terminalDestinations, attachedOrigins, List.map_map, Function.comp_def]

def Event.adjointDecision : Event → Option (NodeAddress × AdjointChoice)
  | .score a _ _ => some (a, .score)
  | .ibp a recipient => some (a, .ibp recipient)
  | _ => none

/-- Raw extraction from an event list and endpoint. Legality and terminality
are hypotheses of the associated theorems, not preconditions enforced here. -/
def encodeRaw (events : List Event) (terminal : List (TaggedPending σ)) : RawTerminalRecord :=
  ⟨events.filterMap Event.adjointDecision, terminalDestinations terminal⟩

/-- Every reserved derivative origin ends at exactly one destination or is the
unused IBP origin retired by an actual score choice. No origin is copied. -/
theorem LegalTrace.terminal_origin_accounting {events s t}
    (h : LegalTrace (σ := σ) events s t) (ht : ∀ p ∈ t, p.activeNode = none) :
    ((encodeRaw events t).destinations.map Prod.fst : Multiset LabelOrigin) +
      (events.map Event.retiredOrigins).sum = originInventory s := by
  have hh := h.origin_inventory
  simpa [encodeRaw, originInventory, terminal_futureOrigins_eq_zero t ht] using hh

theorem LegalTrace.destination_origins_nodup {events s t}
    (h : LegalTrace (σ := σ) events s t) (hs : (originInventory s).Nodup) :
    ((encodeRaw events t).destinations.map Prod.fst).Nodup := by
  simp only [encodeRaw, terminalDestinations_origins]
  exact Multiset.coe_nodup.mp (Multiset.nodup_add.mp (h.inventory_nodup hs)).1

/-- Fixed inventories, rather than terminal-list order, index these arrays.
On a complete legal initial run, `none` denotes a score-consumed IBP derivative
role; for arbitrary inputs to the encoder it can simply denote a missing key. -/
structure FixedTerminalRecord where
  adjoints : List (Option AdjointChoice)
  destinations : List (Option Destination)
  deriving DecidableEq

def encodeFixed (origins : List LabelOrigin) (nodes : List NodeAddress)
    (events : List Event) (terminal : List (TaggedPending σ)) : FixedTerminalRecord :=
  ⟨nodes.map (fun a => (events.filterMap Event.adjointDecision).lookup a),
    origins.map (fun o => (terminalDestinations terminal).lookup o)⟩

/-- Equality of fixed-order records recovers each keyed destination lookup. -/
theorem encodeFixed_destination_eq (origins : List LabelOrigin) (nodes : List NodeAddress)
    {events events' : List Event} {s t : List (TaggedPending σ)}
    (h : encodeFixed origins nodes events s = encodeFixed origins nodes events' t)
    (o : LabelOrigin) (ho : o ∈ origins) :
    (terminalDestinations s).lookup o = (terminalDestinations t).lookup o := by
  exact List.map_inj_left.mp (congrArg FixedTerminalRecord.destinations h) o ho

theorem encodeFixed_adjoint_eq (origins : List LabelOrigin) (nodes : List NodeAddress)
    {events events' : List Event} {s t : List (TaggedPending σ)}
    (h : encodeFixed origins nodes events s = encodeFixed origins nodes events' t)
    (a : NodeAddress) (ha : a ∈ nodes) :
    (events.filterMap Event.adjointDecision).lookup a =
      (events'.filterMap Event.adjointDecision).lookup a := by
  exact List.map_inj_left.mp (congrArg FixedTerminalRecord.adjoints h) a ha

def encodeInitial {r s : ℕ} (e : Expr σ r) (f : Expr σ s) (j k : ℕ)
    (events : List Event) (terminal : List (TaggedPending σ)) : FixedTerminalRecord :=
  let order := initialOriginOrder e f j k
  encodeFixed order (order.filterMap LabelOrigin.adjointNode?) events terminal
/-- Every occurrence carrying an old origin descends inside one old owner's support. -/
def OriginDescends (o : LabelOrigin) (t s : List (TaggedPending σ)) : Prop :=
  ∀ p ∈ t, o ∈ p.labels → ∃ q ∈ s, o ∈ q.labels ∧ p.support.Sublist q.support

namespace OriginDescends

theorem refl (o : LabelOrigin) (s : List (TaggedPending σ)) : OriginDescends o s s := by
  intro p hp ho
  exact ⟨p, hp, ho, List.Sublist.refl _⟩

theorem append {o : LabelOrigin} {s t u v : List (TaggedPending σ)}
    (h : OriginDescends o t s) (h' : OriginDescends o v u) :
    OriginDescends o (t ++ v) (s ++ u) := by
  intro p hp ho
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨q, hq, hqo, hs⟩ := h p hp ho
    exact ⟨q, List.mem_append_left _ hq, hqo, hs⟩
  · obtain ⟨q, hq, hqo, hs⟩ := h' p hp ho
    exact ⟨q, List.mem_append_right _ hq, hqo, hs⟩

theorem trans {o : LabelOrigin} {s t u : List (TaggedPending σ)}
    (h : OriginDescends o u t) (h' : OriginDescends o t s) : OriginDescends o u s := by
  intro p hp ho
  obtain ⟨q, hq, hqo, hpq⟩ := h p hp ho
  obtain ⟨r, hr, hro, hqr⟩ := h' q hq hqo
  exact ⟨r, hr, hro, hpq.trans hqr⟩

theorem singleton {o : LabelOrigin} {p q : TaggedPending σ}
    (hl : o ∈ p.labels → o ∈ q.labels) (hs : p.support.Sublist q.support) :
    OriginDescends o [p] [q] := by
  intro x hx ho
  have hx : x = p := by simpa using hx
  subst x
  exact ⟨q, by simp, hl ho, hs⟩

theorem decorate {o i : LabelOrigin} (p : TaggedPending σ) (h : o ≠ i) :
    OriginDescends o [p.decorate i] [p] := by
  apply singleton
  · simpa only [TaggedPending.labels_decorate, List.mem_cons, h, false_or] using
      (fun h : o ∈ p.labels => h)
  · simp

end OriginDescends

private theorem route_origin_mem {o : LabelOrigin} {J A B : List LabelOrigin}
    (h : (A,B) ∈ routes J) (ho : o ∈ A ∨ o ∈ B) : o ∈ J :=
  (route_perm J (A,B) h).mem_iff.mp (List.mem_append.mpr ho)

/-- Fresh-origin exclusion is the only extra premise for following an old origin. -/
theorem TaggedStep.origin_descends {s t : List (TaggedPending σ)} {event : Event}
    (h : TaggedStep event t s) (o : LabelOrigin) (hf : o ∉ event.createdOrigins) :
    OriginDescends o t s := by
  cases h with
  | permute a p e J before after =>
    apply ((OriginDescends.refl o before).append ?_).append (OriginDescends.refl o after)
    exact OriginDescends.singleton (fun h => h) (by simp [TaggedPending.support])
  | derivative a e J before after =>
    apply ((OriginDescends.refl o before).append ?_).append (OriginDescends.refl o after)
    apply OriginDescends.singleton
    · have hn : o ≠ LabelOrigin.derivative a := by simpa [Event.createdOrigins] using hf
      simp [TaggedPending.labels, hn]
    · simp only [TaggedPending.support, expressionSupport_derivative]
      exact (List.Sublist.refl _).cons (OccurrenceTag.score a) |>.cons (OccurrenceTag.formula a)
  | contract a e f i j J A B route before after =>
    apply ((OriginDescends.refl o before).append ?_).append (OriginDescends.refl o after)
    intro p hp ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · refine ⟨.formula a (.contract e f i j) J, by simp,
        route_origin_mem route (Or.inl ho), ?_⟩
      simp only [TaggedPending.support, expressionSupport_contract]
      simpa only [List.append_nil, List.cons_append, List.nil_append] using
        (((List.Sublist.refl (expressionSupport (a.child false) e)).append
          (List.nil_sublist (expressionSupport (a.child true) f))).cons
            (OccurrenceTag.score a) |>.cons (OccurrenceTag.formula a))
    · refine ⟨.formula a (.contract e f i j) J, by simp,
        route_origin_mem route (Or.inr ho), ?_⟩
      simp only [TaggedPending.support, expressionSupport_contract]
      exact List.sublist_append_right _ _
  | score a e i J A B route before after =>
    have hr : (A,B) ∈ routes J := by rw [routes_eq]; exact List.mem_cons_of_mem _ route
    apply ((OriginDescends.refl o before).append ?_).append (OriginDescends.refl o after)
    intro p hp ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · refine ⟨.formula a (.adjoint i e) J, by simp,
        route_origin_mem hr (Or.inl ho), ?_⟩
      simp only [TaggedPending.support, expressionSupport_adjoint]
      exact ((List.nil_sublist _).cons_cons (OccurrenceTag.score a)).cons (OccurrenceTag.formula a)
    · refine ⟨.formula a (.adjoint i e) J, by simp,
        route_origin_mem hr (Or.inr ho), ?_⟩
      simp only [TaggedPending.support, expressionSupport_adjoint]
      exact List.sublist_append_right _ _
  | ibpAfter a e i J other before between after =>
    have hn : o ≠ LabelOrigin.ibp a := by simpa [Event.createdOrigins] using hf
    apply ((((OriginDescends.refl o before).append ?_).append
      (OriginDescends.refl o between)).append (OriginDescends.decorate other hn)).append
        (OriginDescends.refl o after)
    exact OriginDescends.singleton (fun h => h) (by
      simp only [TaggedPending.support, expressionSupport_adjoint]
      exact List.sublist_append_right _ _)
  | ibpBefore a e i J other before between after =>
    have hn : o ≠ LabelOrigin.ibp a := by simpa [Event.createdOrigins] using hf
    apply ((((OriginDescends.refl o before).append (OriginDescends.decorate other hn)).append
      (OriginDescends.refl o between)).append ?_).append (OriginDescends.refl o after)
    exact OriginDescends.singleton (fun h => h) (by
      simp only [TaggedPending.support, expressionSupport_adjoint]
      exact List.sublist_append_right _ _)

theorem TaggedStep.old_origin_mem {s t : List (TaggedPending σ)} {event : Event}
    (h : TaggedStep event t s) {o : LabelOrigin} (ho : o ∈ attachedOrigins s) :
    o ∈ attachedOrigins t := by
  apply Multiset.mem_coe.mp
  rw [h.origins]
  exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_coe.mpr ho))

/-- Following an already attached origin needs no extra freshness assumption. -/
theorem LegalTrace.origin_descends {events s t} (h : LegalTrace (σ := σ) events s t)
    (hs : (originInventory s).Nodup) {o : LabelOrigin} (ho : o ∈ attachedOrigins s) :
    OriginDescends o t s := by
  induction h with
  | nil => exact OriginDescends.refl _ _
  | cons first rest ih =>
    have hd := first.legal.origin_descends o (fun hf => first.legal.fresh_of_inventory hs o hf ho)
    exact (ih (first.legal.inventory_nodup hs) (first.legal.old_origin_mem ho)).trans hd

/-- A globally unique attached origin has exactly one occurrence owner. -/
theorem attachedOrigin_owner_unique (s : List (TaggedPending σ))
    (hs : (attachedOrigins s).Nodup) {o : LabelOrigin} {p q : TaggedPending σ}
    (hp : p ∈ s) (hq : q ∈ s) (hop : o ∈ p.labels) (hoq : o ∈ q.labels) : p = q := by
  induction s with
  | nil => simp at hp
  | cons a s ih =>
    have hn : (a.labels ++ attachedOrigins s).Nodup := hs
    obtain ⟨_, htail, hd⟩ := List.nodup_append.mp hn
    simp only [List.mem_cons] at hp hq
    rcases hp with rfl | hp <;> rcases hq with rfl | hq
    · rfl
    · have hmem : o ∈ attachedOrigins s := List.mem_flatMap.mpr ⟨q, hq, hoq⟩
      exact False.elim (hd o hop o hmem rfl)
    · have hmem : o ∈ attachedOrigins s := List.mem_flatMap.mpr ⟨p, hp, hop⟩
      exact False.elim (hd o hoq o hmem rfl)
    · exact ih htail hp hq

/-- Entire endpoint support remains inside the support of the original owner. -/
theorem LegalTrace.owner_support {events s t} (h : LegalTrace (σ := σ) events s t)
    (hs : (originInventory s).Nodup) {o : LabelOrigin} {p q : TaggedPending σ}
    (hp : p ∈ s) (hop : o ∈ p.labels) (hq : q ∈ t) (hoq : o ∈ q.labels) :
    q.support.Sublist p.support := by
  have ho : o ∈ attachedOrigins s := List.mem_flatMap.mpr ⟨p, hp, hop⟩
  obtain ⟨r, hr, hor, hqr⟩ := h.origin_descends hs ho q hq hoq
  have hn : (attachedOrigins s).Nodup :=
    Multiset.coe_nodup.mp (Multiset.nodup_add.mp hs).1
  have he : r = p := attachedOrigin_owner_unique s hn hr hp hor hop
  simpa [he] using hqr

def Destination.asTag : Destination → OccurrenceTag
  | .coefficient a => .formula a
  | .score a => .score a

@[simp] theorem TaggedPending.destination_asTag (p : TaggedPending σ) :
    p.destination.asTag = p.tag := by cases p <;> rfl

/-- This holds for all endpoints; terminality makes the destinations actual leaves. -/
theorem LegalTrace.destination_within_owner {events s t}
    (h : LegalTrace (σ := σ) events s t) (hs : (originInventory s).Nodup)
    {o : LabelOrigin} {p : TaggedPending σ} (hp : p ∈ s) (hop : o ∈ p.labels)
    {d : Destination} (hd : (o,d) ∈ terminalDestinations t) : d.asTag ∈ p.support := by
  obtain ⟨q, hq, hd⟩ := List.mem_flatMap.mp hd
  obtain ⟨o', ho', he⟩ := List.mem_map.mp hd
  have heo : o' = o := congrArg Prod.fst he
  have hed : q.destination = d := congrArg Prod.snd he
  subst o'
  have hsupp := h.owner_support hs hp hop hq ho'
  have hm := hsupp.subset q.tag_mem_support
  simpa [← hed] using hm

/-- An attached origin survives every later step; retirement concerns only future origins. -/
theorem LegalTrace.old_origin_mem {events s t} (h : LegalTrace (σ := σ) events s t)
    {o : LabelOrigin} (ho : o ∈ attachedOrigins s) : o ∈ attachedOrigins t := by
  induction h with
  | nil => exact ho
  | cons first rest ih => exact ih (first.legal.old_origin_mem ho)

/-- The terminal record supplies a destination for every origin already attached earlier. -/
theorem LegalTrace.destination_exists {events s t} (h : LegalTrace (σ := σ) events s t)
    {o : LabelOrigin} (ho : o ∈ attachedOrigins s) :
    ∃ d, (o,d) ∈ terminalDestinations t := by
  have hm := h.old_origin_mem ho
  rw [← terminalDestinations_origins t] at hm
  obtain ⟨⟨o', d⟩, hd, he⟩ := List.mem_map.mp hm
  cases he
  exact ⟨d, hd⟩


/-- Keep the entire literal shadow symbolic until a network interpretation is fixed. -/
def symbolicValues : OriginValues LabelOrigin LabelOrigin := ⟨id, id⟩

theorem firstNonterminal_eq_none (s : List (TaggedPending σ)) :
    firstNonterminal s = none ↔ ∀ p ∈ s, p.activeNode = none := by
  induction s with
  | nil => simp [firstNonterminal]
  | cons p s ih =>
    cases hp : p.activeNode <;> simp [firstNonterminal, hp, ih]

theorem firstNonterminal_decompose {s : List (TaggedPending σ)} {a : NodeAddress}
    (h : firstNonterminal s = some a) :
    ∃ before p after, s = before ++ [p] ++ after ∧ p.activeNode = some a := by
  induction s with
  | nil => simp [firstNonterminal] at h
  | cons p s ih =>
    cases hp : p.activeNode with
    | none =>
      have ht : firstNonterminal s = some a := by simpa [firstNonterminal, hp] using h
      obtain ⟨before, q, after, hs, hq⟩ := ih ht
      exact ⟨p :: before, q, after, by simp [hs], hq⟩
    | some b =>
      have hb : b = a := by simpa [firstNonterminal, hp] using h
      exact ⟨[], p, s, by simp, by simpa [hb] using hp⟩

/-- Actual canonical progress, with an IBP recipient at a genuinely different old position. -/
theorem canonical_progress (s : List (TaggedPending σ)) (hs : 2 ≤ s.length)
    (hn : firstNonterminal s ≠ none) : ∃ event t, CanonicalStep event t s := by
  cases he : firstNonterminal s with
  | none => exact False.elim (hn he)
  | some a =>
    obtain ⟨before, p, after, rfl, hp⟩ := firstNonterminal_decompose he
    cases p with
    | score => simp [TaggedPending.activeNode] at hp
    | formula b e J =>
      cases e with
      | coefficient => simp [TaggedPending.activeNode] at hp
      | permute perm e =>
        refine ⟨.permute b, _, TaggedStep.permute b perm e J before after, ?_⟩
        simpa [Event.node, TaggedPending.activeNode] using he.trans (congrArg some
          (Option.some.inj hp).symm)
      | derivative e =>
        refine ⟨.derivative b, _, TaggedStep.derivative b e J before after, ?_⟩
        simpa [Event.node, TaggedPending.activeNode] using he.trans (congrArg some
          (Option.some.inj hp).symm)
      | contract e f i j =>
        refine ⟨.contract b [] J, _, TaggedStep.contract b e f i j J [] J
          (by rw [routes_eq]; simp) before after, ?_⟩
        simpa [Event.node, TaggedPending.activeNode] using he.trans (congrArg some
          (Option.some.inj hp).symm)
      | adjoint i e =>
        have hb : b = a := Option.some.inj hp
        cases before with
        | nil =>
          cases after with
          | nil => simp at hs
          | cons other rest =>
            refine ⟨.ibp b other.tag,
              .formula (b.child false) e J :: other.decorate (.ibp b) :: rest, ?_, ?_⟩
            · simpa using TaggedStep.ibpAfter b e i J other [] [] rest
            · simpa [Event.node, hb] using he
        | cons other rest =>
          refine ⟨.ibp b other.tag,
            (other.decorate (.ibp b) :: rest) ++ [.formula (b.child false) e J] ++ after, ?_, ?_⟩
          · simpa using TaggedStep.ibpBefore b e i J other [] rest after
          · simpa [Event.node, hb] using he

def taggedRank (s : List (TaggedPending σ)) : ℕ := forestRank (eraseForest symbolicValues s)

theorem canonical_wellFounded :
    WellFounded (fun t s : List (TaggedPending σ) => ∃ event, CanonicalStep event t s) :=
  (measure taggedRank).wf.mono (by
    intro t s h
    obtain ⟨event, h⟩ := h
    exact step_rank_lt (h.legal.erase symbolicValues))

/-- Existence of an independently legal terminal trace from every two-occurrence forest. -/
theorem exists_canonical_terminal (s : List (TaggedPending σ)) (hs : 2 ≤ s.length) :
    ∃ events t, LegalTrace events s t ∧ (∀ p ∈ t, p.activeNode = none) := by
  induction s using canonical_wellFounded.induction with
  | h s ih =>
    by_cases ht : firstNonterminal s = none
    · exact ⟨[], s, LegalTrace.nil s, (firstNonterminal_eq_none s).mp ht⟩
    · obtain ⟨event, t, hstep⟩ := canonical_progress s hs ht
      have hlen := hstep.legal.length
      obtain ⟨events, u, htrace, hu⟩ := ih t ⟨event, hstep⟩ (by omega)
      exact ⟨event :: events, u, LegalTrace.cons hstep htrace, hu⟩

theorem TaggedPending.terminal_erase (v : OriginValues Label E) (p : TaggedPending σ)
    (h : p.activeNode = none) : (p.erase v).Terminal := by
  cases p with
  | score => trivial
  | formula a e J => cases e <;> simp_all [TaggedPending.activeNode,
      TaggedPending.erase, Pending.Terminal]

/-- Silent permutation steps are recovered by the fixed original syntax rank. -/
theorem LegalTrace.terminal_step_count (v : OriginValues Label E) {events s t}
    (h : LegalTrace (σ := σ) events s t) (ht : ∀ p ∈ t, p.activeNode = none) :
    events.length = forestRank (eraseForest v s) := by
  have hz : forestRank (eraseForest v t) = 0 := by
    apply (forestRank_eq_zero_iff _).mpr
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact q.terminal_erase v (ht q hq)
  simpa [hz] using steps_rank (h.erase v)

/-- Permutation nesting contributes no entries to the paid origin inventory. -/
theorem futureOriginOrder_length (a : NodeAddress) {r : ℕ} (e : Expr σ r) :
    (futureOriginOrder a e).length = e.weightedOperationCount := by
  induction e generalizing a <;> simp_all [futureOriginOrder, Expr.weightedOperationCount]

theorem initialOriginOrder_length {r s : ℕ} (e : Expr σ r) (f : Expr σ s) (j k : ℕ) :
    (initialOriginOrder e f j k).length = j + k + e.weightedOperationCount +
      f.weightedOperationCount := by
  simp [initialOriginOrder, initialLabels, futureOriginOrder_length, add_assoc]
private theorem flatMap_unchanged {α β : Type*} (tag : α → β) (f : α → List α)
    (l : List α) (keys : List β) (hdis : ∀ x ∈ l, tag x ∉ keys)
    (hf : ∀ x ∈ l, tag x ∉ keys → f x = [x]) : l.flatMap f = l := by
  calc
    l.flatMap f = l.flatMap (fun x => [x]) := List.flatMap_congr (fun x hx => hf x hx (hdis x hx))
    _ = l := by simp

private theorem flatMap_one {α β : Type*} (tag : α → β) (f : α → List α)
    (before after : List α) (p : α)
    (hn : ((before ++ p :: after).map tag).Nodup)
    (hf : ∀ x ∈ before ++ p :: after, tag x ≠ tag p → f x = [x]) :
    (before ++ p :: after).flatMap f = before ++ f p ++ after := by
  induction before with
  | nil =>
    have hn' := List.nodup_cons.mp hn
    have he : after.flatMap f = after := flatMap_unchanged tag f after [tag p]
      (by intro x hx; simpa using (show tag x ≠ tag p from fun he => hn'.1 (he ▸ List.mem_map_of_mem hx)))
      (by intro x hx hk; apply hf x (by simp [hx]); simpa using hk)
    simp [he]
  | cons x xs ih =>
    have hn' := List.nodup_cons.mp hn
    have hx : tag x ≠ tag p := by
      intro he
      apply hn'.1
      simp [he]
    have hi := ih hn'.2 (fun y hy => hf y (by simp_all))
    simp [hf x (by simp) hx, hi]

private theorem flatMap_two {α β : Type*} (tag : α → β) (f : α → List α)
    (before between after : List α) (p q : α)
    (hn : ((before ++ p :: (between ++ q :: after)).map tag).Nodup)
    (hf : ∀ x, tag x ≠ tag p → tag x ≠ tag q → f x = [x]) :
    (before ++ p :: (between ++ q :: after)).flatMap f =
      before ++ f p ++ between ++ f q ++ after := by
  induction before with
  | nil =>
    have hn' := List.nodup_cons.mp hn
    have hp : ∀ x ∈ between ++ q :: after, tag x ≠ tag p := by
      intro x hx he
      exact hn'.1 (he ▸ List.mem_map_of_mem hx)
    have he := flatMap_one tag f between after q hn'.2
      (fun x hm hx => hf x (hp x hm) hx)
    simpa [List.append_assoc] using congrArg (fun z => f p ++ z) he
  | cons x xs ih =>
    have hn' := List.nodup_cons.mp hn
    have hx : tag x ≠ tag p ∧ tag x ≠ tag q := by
      constructor <;> intro he <;> apply hn'.1 <;> simp [he]
    simp [hf x hx.1 hx.2, ih hn'.2, List.append_assoc]

def eventRedex (event : Event) (p : TaggedPending σ) : List (TaggedPending σ) :=
  match event, p with
  | .permute a, .formula _ (.permute _ e) J => [.formula a e J]
  | .derivative a, .formula _ (.derivative e) J =>
      [.formula (a.child false) e (J ++ [.derivative a])]
  | .contract a A B, .formula _ (.contract e f _ _) _ =>
      [.formula (a.child false) e A, .formula (a.child true) f B]
  | .score a A B, .formula _ (.adjoint _ e) _ =>
      if h : A ≠ [] then [.score a A h, .formula (a.child false) e B] else [p]
  | .ibp a _, .formula _ (.adjoint _ e) J => [.formula (a.child false) e J]
  | _, _ => [p]

def interpretPending (event : Event) (p : TaggedPending σ) : List (TaggedPending σ) :=
  if p.tag = .formula event.node then eventRedex event p else
    match event with
    | .ibp a recipient => if p.tag = recipient then [p.decorate (.ibp a)] else [p]
    | _ => [p]

def interpretEvent (event : Event) (s : List (TaggedPending σ)) : List (TaggedPending σ) :=
  s.flatMap (interpretPending event)

theorem TaggedStep.interpret {s t : List (TaggedPending σ)} {event : Event}
    (h : TaggedStep event t s) (hn : (s.map TaggedPending.tag).Nodup) :
    interpretEvent event s = t := by
  cases h with
  | permute a p e J before after =>
    unfold interpretEvent
    rw [show before ++ [TaggedPending.formula a (.permute p e) J] ++ after =
      before ++ TaggedPending.formula a (.permute p e) J :: after by simp]
    rw [flatMap_one TaggedPending.tag _ before after _ (by simpa using hn)]
    · simp [interpretPending, eventRedex, TaggedPending.tag, Event.node]
    · intro x hx hne
      simp [interpretPending, Event.node, TaggedPending.tag] at hne ⊢
      simp [hne]
  | derivative a e J before after =>
    unfold interpretEvent
    rw [show before ++ [TaggedPending.formula a (.derivative e) J] ++ after =
      before ++ TaggedPending.formula a (.derivative e) J :: after by simp]
    rw [flatMap_one TaggedPending.tag _ before after _ (by simpa using hn)]
    · simp [interpretPending, eventRedex, TaggedPending.tag, Event.node]
    · intro x hx hne
      change x.tag ≠ .formula a at hne
      simp [interpretPending, Event.node, hne]
  | contract a e f i j J A B route before after =>
    unfold interpretEvent
    rw [show before ++ [TaggedPending.formula a (.contract e f i j) J] ++ after =
      before ++ TaggedPending.formula a (.contract e f i j) J :: after by simp]
    rw [flatMap_one TaggedPending.tag _ before after _ (by simpa using hn)]
    · simp [interpretPending, eventRedex, TaggedPending.tag, Event.node]
    · intro x hx hne
      change x.tag ≠ .formula a at hne
      simp [interpretPending, Event.node, hne]
  | score a e i J A B route before after =>
    unfold interpretEvent
    rw [show before ++ [TaggedPending.formula a (.adjoint i e) J] ++ after =
      before ++ TaggedPending.formula a (.adjoint i e) J :: after by simp]
    rw [flatMap_one TaggedPending.tag _ before after _ (by simpa using hn)]
    · simp [interpretPending, eventRedex, TaggedPending.tag, Event.node,
        scoreRoutes_left_ne_nil J (A, B) route]
    · intro x hx hne
      change x.tag ≠ .formula a at hne
      simp [interpretPending, Event.node, hne]
  | ibpAfter a e i J other before between after =>
    have hne : other.tag ≠ .formula a :=
      (TaggedStep.ibpAfter a e i J other before between after).ibp_recipient_ne_redex hn
    unfold interpretEvent
    rw [show before ++ [TaggedPending.formula a (.adjoint i e) J] ++ between ++ [other] ++ after =
      before ++ TaggedPending.formula a (.adjoint i e) J :: (between ++ other :: after) by simp [List.append_assoc]]
    rw [flatMap_two TaggedPending.tag _ before between after _ _ (by simpa [List.append_assoc] using hn)]
    · have ho : interpretPending (.ibp a other.tag) other = [other.decorate (.ibp a)] := by
        simp [interpretPending, Event.node, hne]
      rw [ho]
      simp [interpretPending, eventRedex, TaggedPending.tag, Event.node, List.append_assoc]
    · intro x hp hq
      change x.tag ≠ .formula a at hp
      simp [interpretPending, Event.node, hp, hq]
  | ibpBefore a e i J other before between after =>
    have hne : other.tag ≠ .formula a :=
      (TaggedStep.ibpBefore a e i J other before between after).ibp_recipient_ne_redex hn
    unfold interpretEvent
    rw [show before ++ [other] ++ between ++ [TaggedPending.formula a (.adjoint i e) J] ++ after =
      before ++ other :: (between ++ TaggedPending.formula a (.adjoint i e) J :: after) by simp [List.append_assoc]]
    rw [flatMap_two TaggedPending.tag _ before between after _ _ (by simpa [List.append_assoc] using hn)]
    · have ho : interpretPending (.ibp a other.tag) other = [other.decorate (.ibp a)] := by
        simp [interpretPending, Event.node, hne]
      rw [ho]
      simp [interpretPending, eventRedex, TaggedPending.tag, Event.node, List.append_assoc]
    · intro x hp hq
      change x.tag ≠ .formula a at hq
      simp [interpretPending, Event.node, hp, hq]


theorem TaggedStep.deterministic_of_liveTags {s t u : List (TaggedPending σ)} {event : Event}
    (h : TaggedStep event t s) (k : TaggedStep event u s)
    (hn : (s.map TaggedPending.tag).Nodup) : t = u :=
  (h.interpret hn).symm.trans (k.interpret hn)

theorem TaggedStep.deterministic {s t u : List (TaggedPending σ)} {event : Event}
    (h : TaggedStep event t s) (k : TaggedStep event u s)
    (hn : (forestSupport s).Nodup) : t = u :=
  h.deterministic_of_liveTags k (liveTags_nodup_of_support s hn)


/-- Independently legal traces with the same complete event list have the same output.
This does not assert injectivity of a compressed terminal routing record. -/
theorem LegalTrace.deterministic_of_events {events : List Event} {s t u : List (TaggedPending σ)}
    (h : LegalTrace events s t) (k : LegalTrace events s u)
    (hn : (forestSupport s).Nodup) : t = u := by
  induction h generalizing u with
  | nil s => cases k; rfl
  | cons first rest ih =>
    cases k with
    | cons first' rest' =>
      have he := first.legal.deterministic first'.legal hn
      subst he
      exact ih rest' (first.legal.support_nodup hn)


private theorem lookup_destination_pair {l : List (LabelOrigin × Destination)}
    (hn : (l.map Prod.fst).Nodup) {o : LabelOrigin} {d : Destination}
    (hm : (o,d) ∈ l) : l.lookup o = some d := by
  induction l with
  | nil => simp at hm
  | cons pair l ih =>
    rcases pair with ⟨k,b⟩
    simp only [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp hm with he | hm
    · cases he
      simp
    · have ho : o ≠ k := by
        intro he
        subst o
        exact hn.1 (List.mem_map.mpr ⟨(k,d), hm, rfl⟩)
      simp only [List.lookup_cons, show (o == k) = false from beq_eq_false_iff_ne.mpr ho]
      exact ih hn.2 hm

/-- Every endpoint key is unique, so record lookup recovers any listed destination. -/
theorem LegalTrace.destination_lookup_of_mem {events s t}
    (h : LegalTrace (σ := σ) events s t) (hs : (originInventory s).Nodup)
    {o : LabelOrigin} {d : Destination} (hm : (o,d) ∈ terminalDestinations t) :
    (terminalDestinations t).lookup o = some d := by
  apply lookup_destination_pair _ hm
  rw [terminalDestinations_origins]
  exact Multiset.coe_nodup.mp (Multiset.nodup_add.mp (h.inventory_nodup hs)).1

/-- Classify an origin using the actual endpoint record, not a supplied routing witness. -/
def destinationClassifier (t : List (TaggedPending σ)) (support : List OccurrenceTag)
    (o : LabelOrigin) : Bool :=
  ((terminalDestinations t).lookup o).any (fun d => decide (d.asTag ∈ support))

/-- An old origin's recorded destination classifies it into its owner's support. -/
theorem LegalTrace.destinationClassifier_owner {events s t}
    (h : LegalTrace (σ := σ) events s t) (hs : (originInventory s).Nodup)
    {p : TaggedPending σ} (hp : p ∈ s) {o : LabelOrigin} (ho : o ∈ p.labels) :
    destinationClassifier t p.support o = true := by
  obtain ⟨d, hd⟩ := h.destination_exists (List.mem_flatMap.mpr ⟨p, hp, ho⟩)
  have hl := h.destination_lookup_of_mem hs hd
  have hd' := h.destination_within_owner hs hp ho hd
  simp [destinationClassifier, hl, hd']

/-- Disjoint owner supports force the opposite recorded routing choice. -/
theorem LegalTrace.destinationClassifier_other {events s t}
    (h : LegalTrace (σ := σ) events s t) (hs : (originInventory s).Nodup)
    {p q : TaggedPending σ} (hq : q ∈ s) (hdis : List.Disjoint p.support q.support)
    {o : LabelOrigin} (ho : o ∈ q.labels) :
    destinationClassifier t p.support o = false := by
  obtain ⟨d, hd⟩ := h.destination_exists (List.mem_flatMap.mpr ⟨q, hq, ho⟩)
  have hl := h.destination_lookup_of_mem hs hd
  have hd' := h.destination_within_owner hs hq ho hd
  have hn : d.asTag ∉ p.support := fun hm => hdis hm hd'
  simp [destinationClassifier, hl, hn]

/-- The actual destination record reconstructs both ordered parts of a legal route. -/
theorem LegalTrace.route_recovered_from_destinations {events s t}
    (h : LegalTrace (σ := σ) events s t) (hs : (originInventory s).Nodup)
    {p q : TaggedPending σ} (hp : p ∈ s) (hq : q ∈ s)
    (hdis : List.Disjoint p.support q.support) {J : List LabelOrigin}
    (hr : (p.labels,q.labels) ∈ routes J) :
    p.labels = J.filter (destinationClassifier t p.support) ∧
      q.labels = J.filter (fun o => !(destinationClassifier t p.support o)) := by
  apply route_eq_filter _ hr
  · exact fun o ho => h.destinationClassifier_owner hs hp ho
  · exact fun o ho => h.destinationClassifier_other hs hq hdis ho

/-- Independently legal routes agree when their actual destination lookups agree. -/
theorem LegalTrace.routes_equal_of_destination_lookups
    {events events' s s' t t'} (h : LegalTrace (σ := σ) events s t)
    (h' : LegalTrace events' s' t') (hs : (originInventory s).Nodup)
    (hs' : (originInventory s').Nodup)
    {p q p' q' : TaggedPending σ} (hp : p ∈ s) (hq : q ∈ s)
    (hp' : p' ∈ s') (hq' : q' ∈ s')
    (hd : List.Disjoint p.support q.support) (hd' : List.Disjoint p'.support q'.support)
    (hsp : p.support = p'.support) {J : List LabelOrigin}
    (hr : (p.labels,q.labels) ∈ routes J) (hr' : (p'.labels,q'.labels) ∈ routes J)
    (he : ∀ o ∈ J, (terminalDestinations t).lookup o = (terminalDestinations t').lookup o) :
    p.labels = p'.labels ∧ q.labels = q'.labels := by
  have hc (o : LabelOrigin) (ho : o ∈ J) :
      destinationClassifier t p.support o = destinationClassifier t' p'.support o := by
    simp only [destinationClassifier, hsp, he o ho]
  apply route_unique_of_destinations (destinationClassifier t p.support) hr hr'
  · exact fun o ho => h.destinationClassifier_owner hs hp ho
  · exact fun o ho => h.destinationClassifier_other hs hq hd ho
  · intro o ho
    rw [hc o ((route_sublists J _ hr').1.subset ho)]
    exact h'.destinationClassifier_owner hs' hp' ho
  · intro o ho
    rw [hc o ((route_sublists J _ hr').2.subset ho)]
    exact h'.destinationClassifier_other hs' hq' hd' ho

/-- Fixed-order record equality therefore determines the actual ordered route. -/
theorem LegalTrace.routes_equal_of_fixed_record
    (origins : List LabelOrigin) (nodes : List NodeAddress)
    {events events' s s' t t'} (h : LegalTrace (σ := σ) events s t)
    (h' : LegalTrace events' s' t') (hs : (originInventory s).Nodup)
    (hs' : (originInventory s').Nodup)
    {p q p' q' : TaggedPending σ} (hp : p ∈ s) (hq : q ∈ s)
    (hp' : p' ∈ s') (hq' : q' ∈ s')
    (hd : List.Disjoint p.support q.support) (hd' : List.Disjoint p'.support q'.support)
    (hsp : p.support = p'.support) {J : List LabelOrigin}
    (hr : (p.labels,q.labels) ∈ routes J) (hr' : (p'.labels,q'.labels) ∈ routes J)
    (hJ : J ⊆ origins)
    (he : encodeFixed origins nodes events t = encodeFixed origins nodes events' t') :
    p.labels = p'.labels ∧ q.labels = q'.labels := by
  apply h.routes_equal_of_destination_lookups h' hs hs' hp hq hp' hq' hd hd' hsp hr hr'
  intro o ho
  exact encodeFixed_destination_eq origins nodes he o (hJ ho)


theorem contract_child_supports_disjoint (a : NodeAddress) {r s : ℕ}
    (e : Expr σ (r+2)) (f : Expr σ (s+2)) (i : Fin (r+2)) (j : Fin (s+2)) :
    List.Disjoint (expressionSupport (a.child false) e) (expressionSupport (a.child true) f) := by
  have hn := expressionSupport_nodup a (.contract e f i j)
  rw [expressionSupport_contract] at hn
  have ht := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).2
  exact List.disjoint_of_nodup_append ht

theorem score_child_supports_disjoint (a : NodeAddress) {r : ℕ}
    (e : Expr σ (r+2)) (i : Fin (r+2)) :
    List.Disjoint [OccurrenceTag.score a] (expressionSupport (a.child false) e) := by
  have hn := expressionSupport_nodup a (.adjoint i e)
  rw [expressionSupport_adjoint] at hn
  have ht := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
  intro tag hm he
  have hh : tag = .score a := by simpa using hm
  exact ht (hh ▸ he)

end AdjointReduction.ReductionRecords
end AcceleratedLogConcave.Tensor
