import AcceleratedLogConcave.Tensor.ReductionRecords

/-! Reconstruction of independently legal terminal traces from compressed records. -/
namespace AcceleratedLogConcave.Tensor.AdjointReduction.ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name}

/-- Every paid origin is consumed once from the unexpanded syntax reservation. -/
def Event.consumedOrigins (event : Event) : Multiset LabelOrigin :=
  event.createdOrigins + event.retiredOrigins

theorem TaggedStep.consumed_origins {event s t}
    (h : TaggedStep (σ := σ) event t s) :
    forestFutureOrigins t + event.consumedOrigins = forestFutureOrigins s := by
  simpa [Event.consumedOrigins, add_assoc] using h.future_origins

theorem LegalTrace.consumed_origins {events s t}
    (h : LegalTrace (σ := σ) events s t) :
    forestFutureOrigins t + (events.map Event.consumedOrigins).sum =
      forestFutureOrigins s := by
  induction h with
  | nil => simp
  | cons first rest ih =>
    simp only [List.map_cons, List.sum_cons]
    calc
      _ = (forestFutureOrigins _ + (List.map Event.consumedOrigins _).sum) +
          Event.consumedOrigins _ := by abel
      _ = _ := by rw [ih, first.legal.consumed_origins]

theorem LegalTrace.consumed_origins_nodup {events s t}
    (h : LegalTrace (σ := σ) events s t) (hs : (originInventory s).Nodup) :
    ((events.map Event.consumedOrigins).sum).Nodup := by
  have hf := (Multiset.nodup_add.mp hs).2.1
  rw [← h.consumed_origins] at hf
  exact (Multiset.nodup_add.mp hf).2.1

/-- The chronological decision keys, used only to prove uniqueness and lookup persistence. -/
def adjointKeys (events : List Event) : List NodeAddress :=
  (events.filterMap Event.adjointDecision).map Prod.fst

theorem adjointKeys_consumed_le (events : List Event) :
    ((adjointKeys events).map LabelOrigin.ibp : Multiset LabelOrigin) ≤
      (events.map Event.consumedOrigins).sum := by
  induction events with
  | nil => simp [adjointKeys]
  | cons e es ih =>
    cases e <;> simp only [adjointKeys, List.filterMap_cons, Event.adjointDecision,

      List.map_cons, List.sum_cons, Event.consumedOrigins, Event.createdOrigins,
      Event.retiredOrigins, zero_add, add_zero, List.map_map, Function.comp_def,
      ← Multiset.cons_coe, Multiset.singleton_add] at *
    · exact ih
    · exact le_trans ih (Multiset.le_cons_self _ _)
    · exact ih
    · exact Multiset.cons_le_cons _ ih
    · exact Multiset.cons_le_cons _ ih

/-- A legal trace cannot make two decisions at one original adjoint occurrence. -/
theorem LegalTrace.adjointKeys_nodup {events s t}
    (h : LegalTrace (σ := σ) events s t) (hs : (originInventory s).Nodup) :
    (adjointKeys events).Nodup := by
  apply List.Nodup.of_map LabelOrigin.ibp
  apply Multiset.coe_nodup.mp
  exact Multiset.nodup_of_le (adjointKeys_consumed_le events)
    (h.consumed_origins_nodup hs)

private theorem lookup_decision_of_mem (l : List (NodeAddress × AdjointChoice))
    (hn : (l.map Prod.fst).Nodup) {a : NodeAddress} {c : AdjointChoice}
    (hm : (a,c) ∈ l) : l.lookup a = some c := by
  induction l with
  | nil => simp at hm
  | cons p l ih =>
    rcases p with ⟨b,d⟩
    simp only [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp hm with he | hm
    · cases he; simp
    · have hab : a ≠ b := by
        intro he; subst a
        exact hn.1 (List.mem_map.mpr ⟨(b,c), hm, rfl⟩)
      simp only [List.lookup_cons, show (a == b) = false from beq_eq_false_iff_ne.mpr hab]
      exact ih hn.2 hm

/-- Every recorded branch/recipient is recovered by its original-node key. -/
theorem LegalTrace.adjoint_lookup_of_mem {events s t}
    (h : LegalTrace (σ := σ) events s t) (hs : (originInventory s).Nodup)
    {a : NodeAddress} {c : AdjointChoice}
    (hm : (a,c) ∈ events.filterMap Event.adjointDecision) :
    (events.filterMap Event.adjointDecision).lookup a = some c :=
  lookup_decision_of_mem _ (h.adjointKeys_nodup hs) hm

private theorem decision_lookup_none (l : List (NodeAddress × AdjointChoice))
    (a : NodeAddress) (ha : a ∉ l.map Prod.fst) : l.lookup a = none := by
  apply List.lookup_eq_none_iff.mpr
  intro p hp
  simp only [bne_iff_ne]
  intro he
  exact ha (List.mem_map.mpr ⟨p, hp, he.symm⟩)

/-- Removing a common prefix preserves decision lookup equality because no key
in that prefix can occur again in either independently legal suffix. -/
theorem decision_lookups_cancel_prefix (pre xs ys : List Event)
    (hx : (adjointKeys (pre ++ xs)).Nodup)
    (hy : (adjointKeys (pre ++ ys)).Nodup)
    (he : ∀ a, ((pre ++ xs).filterMap Event.adjointDecision).lookup a =
      ((pre ++ ys).filterMap Event.adjointDecision).lookup a) :
    ∀ a, (xs.filterMap Event.adjointDecision).lookup a =
      (ys.filterMap Event.adjointDecision).lookup a := by
  intro a
  simp only [adjointKeys, List.filterMap_append, List.map_append, List.nodup_append] at hx hy
  by_cases hp : a ∈ (pre.filterMap Event.adjointDecision).map Prod.fst
  · have hxa := decision_lookup_none (xs.filterMap Event.adjointDecision) a
      (fun ha => hx.2.2 a hp a ha rfl)
    have hya := decision_lookup_none (ys.filterMap Event.adjointDecision) a
      (fun ha => hy.2.2 a hp a ha rfl)
    exact hxa.trans hya.symm
  · have hp' := decision_lookup_none (pre.filterMap Event.adjointDecision) a hp
    simpa [List.filterMap_append, List.lookup_append, hp'] using he a

/-- Full route payload, kept only for local event recovery. -/
def Event.partition : Event → Option (List LabelOrigin × List LabelOrigin)
  | .contract _ A B | .score _ A B => some (A, B)
  | _ => none

/-- Syntax distinguishes ordinary branches; both adjoint branches share one class. -/
def Event.redexClass : Event → ℕ
  | .permute _ => 1
  | .derivative _ => 2
  | .contract .. => 3
  | .score .. | .ibp .. => 4

def TaggedPending.redexClass : TaggedPending σ → ℕ
  | .formula _ (.permute ..) _ => 1
  | .formula _ (.derivative ..) _ => 2
  | .formula _ (.contract ..) _ => 3
  | .formula _ (.adjoint ..) _ => 4
  | _ => 0

theorem taggedPending_eq_of_tag {s : List (TaggedPending σ)}
    (hn : (s.map TaggedPending.tag).Nodup) {p q : TaggedPending σ}
    (hp : p ∈ s) (hq : q ∈ s) (he : p.tag = q.tag) : p = q := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hp
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hq
  exact congrArg s.get (recipient_index_unique s hn i j he)

theorem TaggedStep.redex_mem {s t : List (TaggedPending σ)} {event : Event}
    (h : TaggedStep event t s) :
    ∃ p ∈ s, p.tag = .formula event.node ∧ p.redexClass = event.redexClass := by
  cases h with
  | permute a perm e J before after =>
    exact ⟨.formula a (.permute perm e) J, by simp, rfl, rfl⟩
  | derivative a e J before after =>
    exact ⟨.formula a (.derivative e) J, by simp, rfl, rfl⟩
  | contract a e f i j J A B route before after =>
    exact ⟨.formula a (.contract e f i j) J, by simp, rfl, rfl⟩
  | score a e i J A B route before after =>
    exact ⟨.formula a (.adjoint i e) J, by simp, rfl, rfl⟩
  | ibpAfter a e i J other before between after =>
    exact ⟨.formula a (.adjoint i e) J, by simp, rfl, rfl⟩
  | ibpBefore a e i J other before between after =>
    exact ⟨.formula a (.adjoint i e) J, by simp, rfl, rfl⟩

theorem CanonicalStep.same_redexClass {s t u : List (TaggedPending σ)} {a b : Event}
    (h : CanonicalStep a t s) (k : CanonicalStep b u s)
    (hn : (s.map TaggedPending.tag).Nodup) : a.redexClass = b.redexClass := by
  obtain ⟨p, hp, hpt, hpc⟩ := h.legal.redex_mem
  obtain ⟨q, hq, hqt, hqc⟩ := k.legal.redex_mem
  have he : p.tag = q.tag := by rw [hpt, hqt, h.same_scheduled_node k]
  have heq := taggedPending_eq_of_tag hn hp hq he
  exact hpc.symm.trans ((congrArg TaggedPending.redexClass heq).trans hqc)

theorem Event.eq_of_payloads {a b : Event} (hn : a.node = b.node)
    (hc : a.redexClass = b.redexClass)
    (ha : a.adjointDecision = b.adjointDecision) (hp : a.partition = b.partition) : a = b := by
  cases a <;> cases b <;>
    simp_all [Event.node, Event.redexClass, Event.adjointDecision, Event.partition]

theorem CanonicalStep.event_eq_of_payloads {s t u : List (TaggedPending σ)} {a b : Event}
    (h : CanonicalStep a t s) (k : CanonicalStep b u s)
    (hn : (s.map TaggedPending.tag).Nodup)
    (ha : a.adjointDecision = b.adjointDecision) (hp : a.partition = b.partition) : a = b :=
  Event.eq_of_payloads (h.same_scheduled_node k) (h.same_redexClass k hn) ha hp

theorem CanonicalStep.partition_cases {s t u : List (TaggedPending σ)} {a b : Event}
    (h : CanonicalStep a t s) (k : CanonicalStep b u s)
    (hn : (s.map TaggedPending.tag).Nodup)
    (ha : a.adjointDecision = b.adjointDecision) :
    (a.partition = none ∧ b.partition = none) ∨
    (∃ n A B C D, a = .contract n A B ∧ b = .contract n C D) ∨
    (∃ n A B C D, a = .score n A B ∧ b = .score n C D) := by
  have hnode := h.same_scheduled_node k
  have hclass := h.same_redexClass k hn
  cases a <;> cases b <;>
    simp_all [Event.node, Event.redexClass, Event.adjointDecision, Event.partition]

theorem CanonicalStep.output_eq_of_payloads {s t u : List (TaggedPending σ)} {a b : Event}
    (h : CanonicalStep a t s) (k : CanonicalStep b u s)
    (hn : (s.map TaggedPending.tag).Nodup)
    (ha : a.adjointDecision = b.adjointDecision) (hp : a.partition = b.partition) : t = u := by
  have he := h.event_eq_of_payloads k hn ha hp
  subst b
  exact h.legal.deterministic_of_liveTags k.legal hn

/-- The common scheduled syntax determines whether a head decision exists, and
its full-trace lookup determines the decision when it exists. -/
theorem CanonicalStep.adjointDecision_eq_of_trace_lookups
    {s t u : List (TaggedPending σ)} {a b : Event} {events events' : List Event}
    (h : CanonicalStep a t s) (k : CanonicalStep b u s)
    (hn : (s.map TaggedPending.tag).Nodup)
    (he : ∀ n, ((a :: events).filterMap Event.adjointDecision).lookup n =
      ((b :: events').filterMap Event.adjointDecision).lookup n) :
    a.adjointDecision = b.adjointDecision := by
  have hnode := h.same_scheduled_node k
  have hclass := h.same_redexClass k hn
  have hh := he a.node
  cases a <;> cases b <;>
    simp_all [Event.node, Event.redexClass, Event.adjointDecision]


/-- Support selected by the syntax when a routing event splits the current owner. -/
def TaggedPending.splitLeftSupport : TaggedPending σ → List OccurrenceTag
  | .formula a (.contract e _ _ _) _ => expressionSupport (a.child false) e
  | .formula a (.adjoint _ _) _ => [.score a]
  | _ => []

theorem contract_first_partitions_equal
    {a : NodeAddress} {A B C D : List LabelOrigin}
    {s s' u u' t t' : List (TaggedPending σ)} {events events' : List Event}
    (h : TaggedStep (.contract a A B) u s) (k : TaggedStep (.contract a C D) u' s')
    (hsame : s = s') (hn : (s.map TaggedPending.tag).Nodup)
    (hs : (originInventory s).Nodup)
    (rest : LegalTrace events u t) (rest' : LegalTrace events' u' t')
    (he : ∀ o, (terminalDestinations t).lookup o = (terminalDestinations t').lookup o) :
    A = C ∧ B = D := by
  have hi := h.inventory_nodup hs
  have hi' := k.inventory_nodup (hsame ▸ hs)
  cases h with
  | contract a e f i j J A B route before after =>
    cases k with
    | contract a e' f' i' j' J' C D route' before' after' =>
      have hp := taggedPending_eq_of_tag hn
        (p := .formula a (.contract e f i j) J)
        (q := .formula a (.contract e' f' i' j') J')
        (by simp) (by rw [hsame]; simp) rfl
      have hJ : J = J' := congrArg TaggedPending.labels hp
      have hL : expressionSupport (a.child false) e = expressionSupport (a.child false) e' :=
        congrArg TaggedPending.splitLeftSupport hp
      exact rest.routes_equal_of_destination_lookups rest' hi hi'
        (p := .formula (a.child false) e A) (q := .formula (a.child true) f B)
        (p' := .formula (a.child false) e' C) (q' := .formula (a.child true) f' D)
        (by simp) (by simp) (by simp) (by simp)
        (contract_child_supports_disjoint a e f i j)
        (contract_child_supports_disjoint a e' f' i' j') hL
        route (by simpa [hJ, TaggedPending.labels] using route') (fun o _ => he o)

theorem score_first_partitions_equal
    {a : NodeAddress} {A B C D : List LabelOrigin}
    {s s' u u' t t' : List (TaggedPending σ)} {events events' : List Event}
    (h : TaggedStep (.score a A B) u s) (k : TaggedStep (.score a C D) u' s')
    (hsame : s = s') (hn : (s.map TaggedPending.tag).Nodup)
    (hs : (originInventory s).Nodup)
    (rest : LegalTrace events u t) (rest' : LegalTrace events' u' t')
    (he : ∀ o, (terminalDestinations t).lookup o = (terminalDestinations t').lookup o) :
    A = C ∧ B = D := by
  have hi := h.inventory_nodup hs
  have hi' := k.inventory_nodup (hsame ▸ hs)
  cases h with
  | score a e i J A B route before after =>
    cases k with
    | score a e' i' J' C D route' before' after' =>
      have hp := taggedPending_eq_of_tag hn
        (p := .formula a (.adjoint i e) J)
        (q := .formula a (.adjoint i' e') J')
        (by simp) (by rw [hsame]; simp) rfl
      have hJ : J = J' := congrArg TaggedPending.labels hp
      have hr : (A,B) ∈ routes J := by rw [routes_eq]; exact List.mem_cons_of_mem _ route
      have hr' : (C,D) ∈ routes J := by
        rw [hJ, routes_eq]; exact List.mem_cons_of_mem _ route'
      exact rest.routes_equal_of_destination_lookups rest' hi hi'
        (p := .score a A (scoreRoutes_left_ne_nil J (A,B) route))
        (q := .formula (a.child false) e B)
        (p' := .score a C (scoreRoutes_left_ne_nil J' (C,D) route'))
        (q' := .formula (a.child false) e' D)
        (by simp) (by simp) (by simp) (by simp)
        (score_child_supports_disjoint a e i)
        (score_child_supports_disjoint a e' i') rfl hr hr' (fun o _ => he o)

/-- Actual common endpoint lookups recover the first routing payload, with no replay witness. -/
theorem CanonicalStep.partition_eq_of_terminal_lookups
    {s u u' t t' : List (TaggedPending σ)} {a b : Event} {events events' : List Event}
    (h : CanonicalStep a u s) (k : CanonicalStep b u' s)
    (hn : (s.map TaggedPending.tag).Nodup) (hs : (originInventory s).Nodup)
    (ha : a.adjointDecision = b.adjointDecision)
    (rest : LegalTrace events u t) (rest' : LegalTrace events' u' t')
    (he : ∀ o, (terminalDestinations t).lookup o = (terminalDestinations t').lookup o) :
    a.partition = b.partition := by
  rcases h.partition_cases k hn ha with hnone | hcontract | hscore
  · exact hnone.1.trans hnone.2.symm
  · obtain ⟨n,A,B,C,D,rfl,rfl⟩ := hcontract
    obtain ⟨rfl,rfl⟩ := contract_first_partitions_equal h.legal k.legal rfl hn hs rest rest' he
    rfl
  · obtain ⟨n,A,B,C,D,rfl,rfl⟩ := hscore
    obtain ⟨rfl,rfl⟩ := score_first_partitions_equal h.legal k.legal rfl hn hs rest rest' he
    rfl

/-- Independent legal first events coincide once the common record recovers the adjoint choice. -/
theorem CanonicalStep.event_eq_of_terminal_lookups
    {s u u' t t' : List (TaggedPending σ)} {a b : Event} {events events' : List Event}
    (h : CanonicalStep a u s) (k : CanonicalStep b u' s)
    (hn : (s.map TaggedPending.tag).Nodup) (hs : (originInventory s).Nodup)
    (ha : a.adjointDecision = b.adjointDecision)
    (rest : LegalTrace events u t) (rest' : LegalTrace events' u' t')
    (he : ∀ o, (terminalDestinations t).lookup o = (terminalDestinations t').lookup o) : a = b :=
  h.event_eq_of_payloads k hn ha (h.partition_eq_of_terminal_lookups k hn hs ha rest rest' he)

theorem LegalTrace.adjoint_key_mem_future {events s t}
    (h : LegalTrace (σ := σ) events s t) {a : NodeAddress}
    (ha : a ∈ adjointKeys events) : .ibp a ∈ forestFutureOrigins s := by
  have hm : LabelOrigin.ibp a ∈
      ((adjointKeys events).map LabelOrigin.ibp : Multiset LabelOrigin) := by
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  have hc := Multiset.mem_of_le (adjointKeys_consumed_le events) hm
  rw [← h.consumed_origins]
  exact Multiset.mem_add.mpr (Or.inr hc)

theorem LegalTrace.destination_key_mem_inventory {events s t}
    (h : LegalTrace (σ := σ) events s t) {o : LabelOrigin} {d : Destination}
    (ho : (o,d) ∈ terminalDestinations t) : o ∈ originInventory s := by
  have hm : o ∈ attachedOrigins t := by
    rw [← terminalDestinations_origins]
    exact List.mem_map.mpr ⟨(o,d), ho, rfl⟩
  rw [← h.origin_inventory]
  exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inl hm)))

/-- Fixed-inventory equality gives unrestricted lookup equality: omitted keys
cannot occur in a legal trace or its endpoint. -/
theorem LegalTrace.lookups_equal_of_fixed_record {events events' s t u}
    (h : LegalTrace (σ := σ) events s t) (k : LegalTrace events' s u)
    (origins : List LabelOrigin) (nodes : List NodeAddress)
    (ho : ∀ o ∈ originInventory s, o ∈ origins)
    (hn : ∀ a, LabelOrigin.ibp a ∈ forestFutureOrigins s → a ∈ nodes)
    (he : encodeFixed origins nodes events t = encodeFixed origins nodes events' u) :
    (∀ a, (events.filterMap Event.adjointDecision).lookup a =
      (events'.filterMap Event.adjointDecision).lookup a) ∧
    (∀ o, (terminalDestinations t).lookup o = (terminalDestinations u).lookup o) := by
  constructor
  · intro a
    by_cases ha : a ∈ nodes
    · exact encodeFixed_adjoint_eq origins nodes he a ha
    · have ht : a ∉ adjointKeys events := fun hm => ha (hn a (h.adjoint_key_mem_future hm))
      have hu : a ∉ adjointKeys events' := fun hm => ha (hn a (k.adjoint_key_mem_future hm))
      exact (decision_lookup_none _ a ht).trans (decision_lookup_none _ a hu).symm
  · intro o
    by_cases ha : o ∈ origins
    · exact encodeFixed_destination_eq origins nodes he o ha
    · have ht : (terminalDestinations t).lookup o = none := by
        apply List.lookup_eq_none_iff.mpr
        intro p hp
        simp only [bne_iff_ne]
        intro heq
        subst o
        exact ha (ho p.1 (h.destination_key_mem_inventory hp))
      have hu : (terminalDestinations u).lookup o = none := by
        apply List.lookup_eq_none_iff.mpr
        intro p hp
        simp only [bne_iff_ne]
        intro heq
        subst o
        exact ha (ho p.1 (k.destination_key_mem_inventory hp))
      exact ht.trans hu.symm

theorem ibp_mem_consumed_iff (events : List Event) (a : NodeAddress) :
    LabelOrigin.ibp a ∈ (events.map Event.consumedOrigins).sum ↔
      a ∈ adjointKeys events := by
  induction events with
  | nil => simp [adjointKeys]
  | cons e es ih =>
    cases e <;> simp [adjointKeys, List.filterMap_cons, Event.adjointDecision,
      Event.consumedOrigins, Event.createdOrigins, Event.retiredOrigins] at *
    all_goals simp only [ih]

/-- Every original adjoint reservation has an actual branch decision in a
terminal run. Combined with `adjointKeys_nodup`, this is exactly-once accounting. -/
theorem LegalTrace.terminal_adjoint_keys {events s t}
    (h : LegalTrace (σ := σ) events s t) (ht : ∀ p ∈ t, p.activeNode = none)
    (a : NodeAddress) : a ∈ adjointKeys events ↔ .ibp a ∈ forestFutureOrigins s := by
  rw [← h.consumed_origins, terminal_futureOrigins_eq_zero t ht, zero_add]
  exact (ibp_mem_consumed_iff events a).symm

/-- An actual decision anywhere in a prefix remains the full trace lookup. -/
theorem LegalTrace.adjoint_lookup_prefix {pre post s t}
    (h : LegalTrace (σ := σ) (pre ++ post) s t) (hs : (originInventory s).Nodup)
    {a : NodeAddress} {c : AdjointChoice}
    (hm : (a,c) ∈ pre.filterMap Event.adjointDecision) :
    ((pre ++ post).filterMap Event.adjointDecision).lookup a = some c := by
  apply h.adjoint_lookup_of_mem hs
  simp only [List.filterMap_append, List.mem_append]
  exact Or.inl hm

/-- A suffix decision is equally recoverable from the full trace record. -/
theorem LegalTrace.adjoint_lookup_suffix {pre post s t}
    (h : LegalTrace (σ := σ) (pre ++ post) s t) (hs : (originInventory s).Nodup)
    {a : NodeAddress} {c : AdjointChoice}
    (hm : (a,c) ∈ post.filterMap Event.adjointDecision) :
    ((pre ++ post).filterMap Event.adjointDecision).lookup a = some c := by
  apply h.adjoint_lookup_of_mem hs
  simp only [List.filterMap_append, List.mem_append]
  exact Or.inr hm

/-- Equal complete decision and endpoint lookups recover an independently legal
terminal trace, including all silent syntax steps. -/
theorem LegalTrace.events_eq_of_terminal_lookups
    {events events' : List Event} {s t t' : List (TaggedPending σ)}
    (h : LegalTrace events s t) (k : LegalTrace events' s t')
    (hn : (forestSupport s).Nodup) (hs : (originInventory s).Nodup)
    (ht : ∀ p ∈ t, p.activeNode = none) (ht' : ∀ p ∈ t', p.activeNode = none)
    (ha : ∀ a, (events.filterMap Event.adjointDecision).lookup a =
      (events'.filterMap Event.adjointDecision).lookup a)
    (hd : ∀ o, (terminalDestinations t).lookup o = (terminalDestinations t').lookup o) :
    events = events' := by
  induction h generalizing events' t' with
  | nil s =>
    cases k with
    | nil => rfl
    | cons first rest =>
      have hh := (firstNonterminal_eq_none s).mpr ht
      rw [first.scheduled] at hh
      contradiction
  | @cons a events s u t first rest ih =>
    cases k with
    | nil =>
      have hh := (firstNonterminal_eq_none s).mpr ht'
      rw [first.scheduled] at hh
      contradiction
    | @cons b events' _ u' t' first' rest' =>
      have hl := liveTags_nodup_of_support s hn
      have hedec := first.adjointDecision_eq_of_trace_lookups first' hl ha
      have he := first.event_eq_of_terminal_lookups first' hl hs hedec rest rest' hd
      subst b
      have hu := first.legal.deterministic first'.legal hn
      subst u'
      have hkeys := (LegalTrace.cons first rest).adjointKeys_nodup hs
      have hkeys' := (LegalTrace.cons first' rest').adjointKeys_nodup hs
      have htail := decision_lookups_cancel_prefix [a] events events' hkeys hkeys' ha
      exact congrArg (List.cons a) (ih rest' (first.legal.support_nodup hn)
        (first.legal.inventory_nodup hs) ht ht' htail hd)

/-- Both the chronological event list and actual terminal forest are reconstructed. -/
theorem LegalTrace.reconstruct_of_terminal_lookups
    {events events' : List Event} {s t t' : List (TaggedPending σ)}
    (h : LegalTrace events s t) (k : LegalTrace events' s t')
    (hn : (forestSupport s).Nodup) (hs : (originInventory s).Nodup)
    (ht : ∀ p ∈ t, p.activeNode = none) (ht' : ∀ p ∈ t', p.activeNode = none)
    (ha : ∀ a, (events.filterMap Event.adjointDecision).lookup a =
      (events'.filterMap Event.adjointDecision).lookup a)
    (hd : ∀ o, (terminalDestinations t).lookup o = (terminalDestinations t').lookup o) :
    events = events' ∧ t = t' := by
  have he := h.events_eq_of_terminal_lookups k hn hs ht ht' ha hd
  refine ⟨he, ?_⟩
  subst events'
  exact h.deterministic_of_events k hn

/-- Compressed fixed records reconstruct two independently legal terminal runs.
The inventories only cover syntax reservations; they do not assert replay validity. -/
theorem LegalTrace.reconstruct_of_fixed_record
    {events events' : List Event} {s t t' : List (TaggedPending σ)}
    (h : LegalTrace events s t) (k : LegalTrace events' s t')
    (hn : (forestSupport s).Nodup) (hs : (originInventory s).Nodup)
    (ht : ∀ p ∈ t, p.activeNode = none) (ht' : ∀ p ∈ t', p.activeNode = none)
    (origins : List LabelOrigin) (nodes : List NodeAddress)
    (ho : ∀ o ∈ originInventory s, o ∈ origins)
    (ha : ∀ a, LabelOrigin.ibp a ∈ forestFutureOrigins s → a ∈ nodes)
    (he : encodeFixed origins nodes events t = encodeFixed origins nodes events' t') :
    events = events' ∧ t = t' := by
  obtain ⟨hdec, hdest⟩ := h.lookups_equal_of_fixed_record k origins nodes ho ha he
  exact h.reconstruct_of_terminal_lookups k hn hs ht ht' hdec hdest

/-- The actual original two-formula syntax supplies every invariant and record
index. No external freshness, counting, or reconstruction hypothesis is needed. -/
theorem LegalTrace.reconstruct_of_initial_record
    {r q : ℕ} (e : Expr σ r) (f : Expr σ q) (j k : ℕ)
    {events events' : List Event} {t t' : List (TaggedPending σ)}
    (h : LegalTrace events (initialTwoFormulas e f j k) t)
    (h' : LegalTrace events' (initialTwoFormulas e f j k) t')
    (ht : ∀ p ∈ t, p.activeNode = none) (ht' : ∀ p ∈ t', p.activeNode = none)
    (he : encodeInitial e f j k events t = encodeInitial e f j k events' t') :
    events = events' ∧ t = t' := by
  apply h.reconstruct_of_fixed_record h' (initialTwoFormulas_support_nodup e f j k)
    (initialTwoFormulas_inventory_nodup e f j k) ht ht'
    (initialOriginOrder e f j k)
    ((initialOriginOrder e f j k).filterMap LabelOrigin.adjointNode?)
    ?_ ?_ he
  · intro o ho
    have heq := initialOriginOrder_coe e f j k
    rw [← heq] at ho
    exact ho
  · intro a ha
    apply List.mem_filterMap.mpr
    refine ⟨.ibp a, ?_, rfl⟩
    have ho : LabelOrigin.ibp a ∈ originInventory (initialTwoFormulas e f j k) :=
      Multiset.mem_add.mpr (Or.inr ha)
    rw [← initialOriginOrder_coe e f j k] at ho
    exact ho

end AcceleratedLogConcave.Tensor.AdjointReduction.ReductionRecords
