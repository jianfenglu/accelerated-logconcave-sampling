import AcceleratedLogConcave.Tensor.ReductionDestinationReplay

/-!
# Finite terminal structural branch counts

The original manuscript's counting paragraph is `sources/warm-start.tex`,
lines 1767–1802 (the pinned source used by `Tensor.Expressions`).
Destination-only compression strengthens its record encoding: the final
location of each adjoint-origin derivative also determines the IBP recipient,
and absence determines the score branch. The bound counts actual legal event
histories, before any numeric interpretation or equality of evaluated outputs.
The explicit expansion-list multiplicity bridge is in `ReductionExpansion`.
-/
open scoped NNReal

namespace AcceleratedLogConcave.Tensor.AdjointReduction.ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name}

/-- Only genuine coefficient leaves and adjoint-created scores can be terminal.
Silent permutations introduce no new index. -/
def potentialDestinations (a : NodeAddress) : {r : ℕ} → Expr σ r → List Destination
  | _, .coefficient _ => [.coefficient a]
  | _, .permute _ e => potentialDestinations a e
  | _, .contract e f _ _ =>
      potentialDestinations (a.child false) e ++ potentialDestinations (a.child true) f
  | _, .derivative e => potentialDestinations (a.child false) e
  | _, .adjoint _ e => .score a :: potentialDestinations (a.child false) e

def TaggedPending.potentialDestinations : TaggedPending σ → List Destination
  | .formula a e _ => ReductionRecords.potentialDestinations a e
  | .score a _ _ => [.score a]

def forestPotentialDestinations (s : List (TaggedPending σ)) : List Destination :=
  s.flatMap TaggedPending.potentialDestinations

@[simp] theorem TaggedPending.potentialDestinations_decorate (o : LabelOrigin)
    (p : TaggedPending σ) : (p.decorate o).potentialDestinations = p.potentialDestinations := by
  cases p <;> rfl

theorem TaggedStep.potentialDestinations_sublist {event s t}
    (h : TaggedStep (σ := σ) event t s) :
    (forestPotentialDestinations t).Sublist (forestPotentialDestinations s) := by
  cases h with
  | ibpAfter a e i J other before between after
  | ibpBefore a e i J other before between after =>
    cases other <;> simp only [forestPotentialDestinations, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, TaggedPending.decorate,
      TaggedPending.potentialDestinations, potentialDestinations, List.append_nil] <;> first
    | exact ((((List.Sublist.refl _).append ((List.Sublist.refl _).cons (Destination.score a))).append
        (List.Sublist.refl _)).append (List.Sublist.refl _)).append (List.Sublist.refl _)
    | exact ((((List.Sublist.refl _).append (List.Sublist.refl _)).append
        (List.Sublist.refl _)).append ((List.Sublist.refl _).cons (Destination.score a))).append
        (List.Sublist.refl _)
  | _ => simp [forestPotentialDestinations, TaggedPending.potentialDestinations,
      potentialDestinations, List.append_assoc]

theorem LegalTrace.potentialDestinations_sublist {events s t}
    (h : LegalTrace (σ := σ) events s t) :
    (forestPotentialDestinations t).Sublist (forestPotentialDestinations s) := by
  induction h with
  | nil => exact List.Sublist.refl _
  | cons first rest ih => exact ih.trans first.legal.potentialDestinations_sublist

theorem TaggedPending.terminal_destination_mem (p : TaggedPending σ)
    (ht : p.activeNode = none) : p.destination ∈ p.potentialDestinations := by
  cases p with
  | score => simp [TaggedPending.destination, TaggedPending.potentialDestinations]
  | formula a e J => cases e <;> simp_all [TaggedPending.activeNode,
      TaggedPending.destination, TaggedPending.potentialDestinations, ReductionRecords.potentialDestinations]

theorem LegalTrace.destination_mem_potential {events s t}
    (h : LegalTrace (σ := σ) events s t) (ht : ∀ p ∈ t, p.activeNode = none)
    {o : LabelOrigin} {d : Destination} (hd : (o,d) ∈ terminalDestinations t) :
    d ∈ forestPotentialDestinations s := by
  apply h.potentialDestinations_sublist.subset
  simp only [terminalDestinations, List.mem_flatMap, List.mem_map] at hd
  obtain ⟨p, hp, x, hx, he⟩ := hd
  have he' : p.destination = d := congrArg Prod.snd he
  rw [← he']
  exact List.mem_flatMap.mpr ⟨p, hp, p.terminal_destination_mem (ht p hp)⟩

theorem potentialDestinations_length_bound (a : NodeAddress) {r : ℕ} (e : Expr σ r) :
    (potentialDestinations a e).length + 1 ≤ e.size := by
  induction e generalizing a with
  | coefficient c =>
    simpa [potentialDestinations, Expr.size] using (σ.two_le_arity c).trans (σ.arity_le_size c)
  | permute p e ih => exact ih a
  | contract e f i j ih ih' =>
    have h := ih (a.child false)
    have h' := ih' (a.child true)
    simp only [potentialDestinations, List.length_append, Expr.size]
    omega
  | derivative e ih =>
    have h := ih (a.child false)
    simp only [potentialDestinations, Expr.size]
    omega
  | adjoint i e ih =>
    have h := ih (a.child false)
    simpa [potentialDestinations, Expr.size] using Nat.add_le_add_right h 1

/-- Arity prevents adjoints from creating an arbitrarily large static score
alphabet. This is stronger than the size-only bound. -/
theorem potentialDestinations_arity_bound (a : NodeAddress) {r : ℕ} (e : Expr σ r) :
    2 * (potentialDestinations a e).length + r ≤ e.size + 2 := by
  induction e generalizing a with
  | coefficient c =>
    simpa [potentialDestinations, Expr.size, Nat.add_comm] using
      Nat.add_le_add_right (σ.arity_le_size c) 2
  | permute p e ih => exact ih a
  | contract e f i j ih ih' =>
    have h := ih (a.child false)
    have h' := ih' (a.child true)
    simp only [potentialDestinations, List.length_append, Expr.size]
    omega
  | derivative e ih =>
    have h := ih (a.child false)
    simp only [potentialDestinations, Expr.size]
    omega
  | adjoint i e ih =>
    have h := ih (a.child false)
    simp only [potentialDestinations, List.length_cons, Expr.size]
    omega

/-- Permutation-free output arity is always positive. -/
theorem expression_arity_pos {r : ℕ} (e : Expr σ r) : 0 < r := by
  induction e with
  | coefficient c => exact lt_of_lt_of_le (by omega : 0 < 2) (σ.two_le_arity c)
  | permute p e ih => exact ih
  | contract => omega
  | derivative => omega
  | adjoint => omega

/-- The original two-copy static alphabet, including absent origins, costs at
most `size + 2`; live-forest size alone does not justify a smaller alphabet. -/
theorem initialTwoFormulas_potential_length {r : ℕ} (e : Expr σ r) (j k : ℕ) :
    (forestPotentialDestinations (initialTwoFormulas e e j k)).length + 1 ≤ e.size + 2 := by
  have h := potentialDestinations_arity_bound (NodeAddress.mk 0 []) e
  have h' := potentialDestinations_arity_bound (NodeAddress.mk 1 []) e
  have hr := expression_arity_pos e
  simp only [initialTwoFormulas, forestPotentialDestinations, List.flatMap_cons,
    List.flatMap_nil, TaggedPending.potentialDestinations, List.append_nil,
    List.length_append]
  omega

/-- A branch is its actual event list and actual endpoint, with independent legality. -/
structure TerminalRun (s : List (TaggedPending σ)) where
  events : List Event
  terminal : List (TaggedPending σ)
  legal : LegalTrace events s terminal
  terminality : ∀ p ∈ terminal, p.activeNode = none

@[ext] theorem TerminalRun.ext {s : List (TaggedPending σ)} {x y : TerminalRun s}
    (he : x.events = y.events) (ht : x.terminal = y.terminal) : x = y := by
  cases x
  cases y
  cases he
  cases ht
  rfl

def TerminalRun.destinationVector {s : List (TaggedPending σ)}
    (origins : List LabelOrigin) (run : TerminalRun s) : Fin origins.length → Option Destination :=
  fun i => (terminalDestinations run.terminal).lookup (origins.get i)

def TerminalRun.destinationList {s : List (TaggedPending σ)}
    (origins : List LabelOrigin) (run : TerminalRun s) : List (Option Destination) :=
  origins.map (fun o => (terminalDestinations run.terminal).lookup o)

/-- Present destinations are represented by an actual index in the supplied alphabet. -/
def encodeDestinationIndex (alphabet : List Destination) (value : Option Destination)
    (hmem : ∀ d, value = some d → d ∈ alphabet) : Option (Fin alphabet.length) :=
  match value with
  | none => none
  | some d => some ⟨alphabet.idxOf d, List.idxOf_lt_length_iff.mpr (hmem d rfl)⟩

@[simp] theorem decode_encodeDestinationIndex (alphabet : List Destination)
    (value : Option Destination) (hmem : ∀ d, value = some d → d ∈ alphabet) :
    (encodeDestinationIndex alphabet value hmem).map alphabet.get = value := by
  cases value with
  | none => rfl
  | some d =>
    simp only [encodeDestinationIndex, Option.map_some, Option.some.injEq]
    exact List.getElem_idxOf _

def TerminalRun.finiteCode {s : List (TaggedPending σ)}
    (origins : List LabelOrigin) (alphabet : List Destination)
    (hmem : ∀ (run : TerminalRun s) (i : Fin origins.length) d,
      run.destinationVector origins i = some d → d ∈ alphabet)
    (run : TerminalRun s) : Fin origins.length → Option (Fin alphabet.length) :=
  fun i => encodeDestinationIndex alphabet (run.destinationVector origins i) (hmem run i)

theorem TerminalRun.finiteCode_injective {s : List (TaggedPending σ)}
    (origins : List LabelOrigin) (alphabet : List Destination)
    (hmem : ∀ (run : TerminalRun s) (i : Fin origins.length) d,
      run.destinationVector origins i = some d → d ∈ alphabet)
    (hinj : Function.Injective (TerminalRun.destinationVector (s := s) origins)) :
    Function.Injective (TerminalRun.finiteCode origins alphabet hmem) := by
  intro x y he
  apply hinj
  funext i
  have hh := congrArg (fun code : Fin origins.length → Option (Fin alphabet.length) =>
    (code i).map alphabet.get) he
  simpa only [TerminalRun.finiteCode, decode_encodeDestinationIndex] using hh

/-- An explicit finite function code proves finiteness; no cardinal bound is assumed. -/
theorem TerminalRun.finite_of_destinationVector {s : List (TaggedPending σ)}
    (origins : List LabelOrigin) (alphabet : List Destination)
    (hmem : ∀ (run : TerminalRun s) (i : Fin origins.length) d,
      run.destinationVector origins i = some d → d ∈ alphabet)
    (hinj : Function.Injective (TerminalRun.destinationVector (s := s) origins)) :
    Finite (TerminalRun s) :=
  Finite.of_injective (TerminalRun.finiteCode origins alphabet hmem)
    (TerminalRun.finiteCode_injective origins alphabet hmem hinj)

/-- Count actual independently legal terminal branches, retaining endpoint multiplicity. -/
theorem TerminalRun.card_le_of_destinationVector {s : List (TaggedPending σ)}
    (origins : List LabelOrigin) (alphabet : List Destination)
    (hmem : ∀ (run : TerminalRun s) (i : Fin origins.length) d,
      run.destinationVector origins i = some d → d ∈ alphabet)
    (hinj : Function.Injective (TerminalRun.destinationVector (s := s) origins)) :
    Nat.card (TerminalRun s) ≤ (alphabet.length + 1) ^ origins.length := by
  have hc := Nat.card_le_card_of_injective (TerminalRun.finiteCode origins alphabet hmem)
    (TerminalRun.finiteCode_injective origins alphabet hmem hinj)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_option,
    Fintype.card_fin] using hc

/-- List-valued fixed records give the same injectivity criterion as indexed vectors. -/
theorem TerminalRun.destinationVector_injective_of_list {s : List (TaggedPending σ)}
    (origins : List LabelOrigin)
    (hinj : Function.Injective (TerminalRun.destinationList (s := s) origins)) :
    Function.Injective (TerminalRun.destinationVector (s := s) origins) := by
  intro x y he
  apply hinj
  apply List.map_congr_left
  intro o ho
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ho
  exact congrFun he i

/-- Convenient public interface with ordinary fixed-order destination lists. -/
theorem TerminalRun.card_le_of_destinationList {s : List (TaggedPending σ)}
    (origins : List LabelOrigin) (alphabet : List Destination)
    (hmem : ∀ (run : TerminalRun s) o d, o ∈ origins →
      (terminalDestinations run.terminal).lookup o = some d → d ∈ alphabet)
    (hinj : Function.Injective (TerminalRun.destinationList (s := s) origins)) :
    Nat.card (TerminalRun s) ≤ (alphabet.length + 1) ^ origins.length := by
  apply TerminalRun.card_le_of_destinationVector origins alphabet
    (fun run i d hd => hmem run (origins.get i) d (List.get_mem _ _) hd)
  exact TerminalRun.destinationVector_injective_of_list origins hinj

theorem TerminalRun.finite_of_destinationList {s : List (TaggedPending σ)}
    (origins : List LabelOrigin) (alphabet : List Destination)
    (hmem : ∀ (run : TerminalRun s) o d, o ∈ origins →
      (terminalDestinations run.terminal).lookup o = some d → d ∈ alphabet)
    (hinj : Function.Injective (TerminalRun.destinationList (s := s) origins)) :
    Finite (TerminalRun s) := by
  apply TerminalRun.finite_of_destinationVector origins alphabet
    (fun run i d hd => hmem run (origins.get i) d (List.get_mem _ _) hd)
  exact TerminalRun.destinationVector_injective_of_list origins hinj

theorem TerminalRun.destination_mem_potential {s : List (TaggedPending σ)}
    (run : TerminalRun s) (o : LabelOrigin) (d : Destination)
    (hd : (terminalDestinations run.terminal).lookup o = some d) :
    d ∈ forestPotentialDestinations s := by
  obtain ⟨pre, post, he, _⟩ := List.lookup_eq_some_iff.mp hd
  apply run.legal.destination_mem_potential run.terminality (o := o)
  rw [he]
  simp

theorem TerminalRun.initial_destinationList_injective {r q : ℕ}
    (e : Expr σ r) (f : Expr σ q) (j k : ℕ) :
    Function.Injective (TerminalRun.destinationList
      (s := initialTwoFormulas e f j k) (initialOriginOrder e f j k)) := by
  intro x y he
  obtain ⟨hev, ht⟩ := x.legal.reconstruct_of_initial_destinations e f j k y.legal
    x.terminality y.terminality he
  exact TerminalRun.ext hev ht

/-- There are finitely many actual terminal branch histories, independently of
whether different branches evaluate to equal tensor values. -/
theorem TerminalRun.initial_finite {r q : ℕ}
    (e : Expr σ r) (f : Expr σ q) (j k : ℕ) :
    Finite (TerminalRun (initialTwoFormulas e f j k)) := by
  apply TerminalRun.finite_of_destinationList (initialOriginOrder e f j k)
    (forestPotentialDestinations (initialTwoFormulas e f j k))
  · intro run o d _ hd
    exact run.destination_mem_potential o d hd
  · exact TerminalRun.initial_destinationList_injective e f j k

/-- Exact fixed-array upper bound: no factorial, chronological ordering factor,
or independent adjoint-choice exponent is charged. -/
theorem TerminalRun.initial_card_bound {r q : ℕ}
    (e : Expr σ r) (f : Expr σ q) (j k : ℕ) :
    Nat.card (TerminalRun (initialTwoFormulas e f j k)) ≤
      ((forestPotentialDestinations (initialTwoFormulas e f j k)).length + 1) ^
        (j + k + e.weightedOperationCount + f.weightedOperationCount) := by
  have h := TerminalRun.card_le_of_destinationList (initialOriginOrder e f j k)
    (forestPotentialDestinations (initialTwoFormulas e f j k))
    (fun run o d _ hd => run.destination_mem_potential o d hd)
    (TerminalRun.initial_destinationList_injective e f j k)
  simpa only [initialOriginOrder_length] using h

/-- Two-copy bound in the manuscript's `N = size + j` scale. -/
theorem TerminalRun.twoCopy_card_bound {r : ℕ} (e : Expr σ r) (j : ℕ) :
    Nat.card (TerminalRun (initialTwoFormulas e e j j)) ≤
      (e.size + 2) ^ (2 * (j + e.weightedOperationCount)) := by
  have h := TerminalRun.initial_card_bound e e j j
  have hp := Nat.pow_le_pow_left (initialTwoFormulas_potential_length e j j)
    (j + j + e.weightedOperationCount + e.weightedOperationCount)
  have he : j + j + e.weightedOperationCount + e.weightedOperationCount =
      2 * (j + e.weightedOperationCount) := by omega
  rw [he] at h hp
  exact h.trans hp

/-- An explicit dimension-free manuscript-scale bound, with constant two.
Permutations and repeated physical coordinates introduce no extra factor. -/
theorem TerminalRun.twoCopy_card_le_size_power {r : ℕ} (e : Expr σ r) (j : ℕ) :
    Nat.card (TerminalRun (initialTwoFormulas e e j j)) ≤
      (2 * (e.size + j)) ^ (2 * (e.size + j)) := by
  have hn := expression_size_two_le e
  have hw := weightedOperationCount_le_size e
  calc
    _ ≤ (e.size + 2) ^ (2 * (j + e.weightedOperationCount)) :=
      TerminalRun.twoCopy_card_bound e j
    _ ≤ (2 * (e.size + j)) ^ (2 * (j + e.weightedOperationCount)) :=
      Nat.pow_le_pow_left (by omega) _
    _ ≤ (2 * (e.size + j)) ^ (2 * (e.size + j)) :=
      Nat.pow_le_pow_right (by omega) (by omega)

/-- The same actual branch histories carry the exact size, derivative-label,
and smoothing losses used in the analytic terminal estimate. -/
theorem TerminalRun.twoCopy_exact_budgets {r : ℕ} (e : Expr σ r) (j : ℕ)
    (run : TerminalRun (initialTwoFormulas e e j j)) :
    forestSize (eraseForest symbolicValues run.terminal) +
        (run.events.map Event.contractions).sum = 2 * (e.size + j) ∧
    forestLabels (eraseForest symbolicValues run.terminal) +
        (run.events.map Event.scores).sum = 2 * (j + e.weightedOperationCount) ∧
    forestSmoothing (eraseForest symbolicValues run.terminal) +
        2 * ((run.events.map Event.scores).sum : ℝ≥0) = 2 * (e.weight + (j : ℝ≥0)) := by
  simpa [initialTwoFormulas, initialLabels, eraseForest, TaggedPending.erase,
    forestSize, forestLabels, forestSmoothing, Pending.sizeBudget, Pending.labelBudget,
    Pending.smoothingBudget, two_mul] using run.legal.budgets symbolicValues

end AcceleratedLogConcave.Tensor.AdjointReduction.ReductionRecords
