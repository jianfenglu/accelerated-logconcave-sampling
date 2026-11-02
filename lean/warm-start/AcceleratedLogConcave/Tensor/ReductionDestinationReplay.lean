import AcceleratedLogConcave.Tensor.ReductionReplay

/-! Destination-only compression retains every independently legal terminal branch. -/
namespace AcceleratedLogConcave.Tensor.AdjointReduction.ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name}

theorem LegalTrace.destination_lookup_none_of_retired {events s t}
    (h : LegalTrace (σ := σ) events s t) (hs : (originInventory s).Nodup)
    {o : LabelOrigin} (ho : o ∈ (events.map Event.retiredOrigins).sum) :
    (terminalDestinations t).lookup o = none := by
  have hn := hs
  rw [← h.origin_inventory] at hn
  have hd := (Multiset.nodup_add.mp hn).2.2
  apply List.lookup_eq_none_iff.mpr
  intro p hp
  simp only [bne_iff_ne]
  intro he
  have hm : o ∈ attachedOrigins t := by
    rw [← terminalDestinations_origins t]
    exact List.mem_map.mpr ⟨p, hp, he.symm⟩
  exact Multiset.disjoint_left.mp hd
    (Multiset.mem_add.mpr (Or.inl (Multiset.mem_coe.mpr hm))) ho

theorem CanonicalStep.score_destination_none {a : NodeAddress} {A B : List LabelOrigin}
    {s u t : List (TaggedPending σ)} {events : List Event}
    (h : CanonicalStep (.score a A B) u s) (rest : LegalTrace events u t)
    (hs : (originInventory s).Nodup) :
    (terminalDestinations t).lookup (.ibp a) = none := by
  apply (LegalTrace.cons h rest).destination_lookup_none_of_retired hs
  simp [Event.retiredOrigins]

theorem TaggedStep.ibp_destination_owner {a : NodeAddress} {recipient : OccurrenceTag}
    {s u t : List (TaggedPending σ)} {events : List Event}
    (h : TaggedStep (.ibp a recipient) u s) (rest : LegalTrace events u t)
    (hs : (originInventory s).Nodup) :
    ∃ q ∈ s, q.tag = recipient ∧ ∃ d,
      (terminalDestinations t).lookup (.ibp a) = some d ∧ d.asTag ∈ q.support := by
  have hi := h.inventory_nodup hs
  cases h with
  | ibpAfter a e i J other before between after =>
    have hp : other.decorate (.ibp a) ∈
        before ++ [TaggedPending.formula (a.child false) e J] ++ between ++
          [other.decorate (.ibp a)] ++ after := by simp
    have ho : LabelOrigin.ibp a ∈ (other.decorate (.ibp a)).labels := by simp
    obtain ⟨d, hd⟩ := rest.destination_exists (List.mem_flatMap.mpr ⟨_, hp, ho⟩)
    refine ⟨other, by simp, rfl, d, rest.destination_lookup_of_mem hi hd, ?_⟩
    simpa using rest.destination_within_owner hi hp ho hd
  | ibpBefore a e i J other before between after =>
    have hp : other.decorate (.ibp a) ∈
        before ++ [other.decorate (.ibp a)] ++ between ++
          [TaggedPending.formula (a.child false) e J] ++ after := by simp
    have ho : LabelOrigin.ibp a ∈ (other.decorate (.ibp a)).labels := by simp
    obtain ⟨d, hd⟩ := rest.destination_exists (List.mem_flatMap.mpr ⟨_, hp, ho⟩)
    refine ⟨other, by simp, rfl, d, rest.destination_lookup_of_mem hi hd, ?_⟩
    simpa using rest.destination_within_owner hi hp ho hd

theorem support_owner_unique (s : List (TaggedPending σ)) (hs : (forestSupport s).Nodup)
    {o : OccurrenceTag} {p q : TaggedPending σ} (hp : p ∈ s) (hq : q ∈ s)
    (hop : o ∈ p.support) (hoq : o ∈ q.support) : p = q := by
  induction s with
  | nil => simp at hp
  | cons a s ih =>
    have hn : (a.support ++ forestSupport s).Nodup := hs
    obtain ⟨_, htail, hd⟩ := List.nodup_append.mp hn
    simp only [List.mem_cons] at hp hq
    rcases hp with rfl | hp <;> rcases hq with rfl | hq
    · rfl
    · have hmem : o ∈ forestSupport s := List.mem_flatMap.mpr ⟨q, hq, hoq⟩
      exact False.elim (hd o hop o hmem rfl)
    · have hmem : o ∈ forestSupport s := List.mem_flatMap.mpr ⟨p, hp, hop⟩
      exact False.elim (hd o hoq o hmem rfl)
    · exact ih htail hp hq

theorem TaggedStep.ibp_recipient_eq_of_destinations {a : NodeAddress} {recipient recipient' : OccurrenceTag}
    {s u u' t t' : List (TaggedPending σ)} {events events' : List Event}
    (h : TaggedStep (.ibp a recipient) u s) (k : TaggedStep (.ibp a recipient') u' s)
    (rest : LegalTrace events u t) (rest' : LegalTrace events' u' t')
    (hn : (forestSupport s).Nodup) (hs : (originInventory s).Nodup)
    (he : (terminalDestinations t).lookup (.ibp a) =
      (terminalDestinations t').lookup (.ibp a)) : recipient = recipient' := by
  obtain ⟨p, hp, hpt, d, hd, hdp⟩ := h.ibp_destination_owner rest hs
  obtain ⟨q, hq, hqt, d', hd', hdq⟩ := k.ibp_destination_owner rest' hs
  have hdd : d = d' := Option.some.inj (hd.symm.trans (he.trans hd'))
  subst d'
  have hpq := support_owner_unique s hn hp hq hdp hdq
  exact hpt.symm.trans ((congrArg TaggedPending.tag hpq).trans hqt)

/-- At the first scheduled adjoint, its own origin's endpoint destination determines
both the score/IBP branch and the old recipient occurrence. -/
theorem CanonicalStep.adjointDecision_eq_of_destinations
    {s u u' t t' : List (TaggedPending σ)} {a b : Event} {events events' : List Event}
    (h : CanonicalStep a u s) (k : CanonicalStep b u' s)
    (rest : LegalTrace events u t) (rest' : LegalTrace events' u' t')
    (hn : (forestSupport s).Nodup) (hs : (originInventory s).Nodup)
    (he : ∀ o, (terminalDestinations t).lookup o = (terminalDestinations t').lookup o) :
    a.adjointDecision = b.adjointDecision := by
  have hnode := h.same_scheduled_node k
  have hclass := h.same_redexClass k (liveTags_nodup_of_support s hn)
  cases a <;> cases b <;>
    simp_all [Event.node, Event.redexClass, Event.adjointDecision]
  · have hh := h.score_destination_none rest hs
    obtain ⟨_, _, _, d, hd, _⟩ := k.legal.ibp_destination_owner rest' hs
    have heq : none = some d := hh.symm.trans ((he _).trans hd)
    contradiction
  · have hh := k.score_destination_none rest' hs
    obtain ⟨_, _, _, d, hd, _⟩ := h.legal.ibp_destination_owner rest hs
    have heq : some d = none := hd.symm.trans ((he _).trans hh)
    contradiction
  · exact h.legal.ibp_recipient_eq_of_destinations k.legal rest rest' hn hs (he _)


/-- Equal endpoint destination lookups alone recover an independently legal
terminal trace, including all silent syntax steps and adjoint choices. -/
theorem LegalTrace.events_eq_of_destinations
    {events events' : List Event} {s t t' : List (TaggedPending σ)}
    (h : LegalTrace events s t) (k : LegalTrace events' s t')
    (hn : (forestSupport s).Nodup) (hs : (originInventory s).Nodup)
    (ht : ∀ p ∈ t, p.activeNode = none) (ht' : ∀ p ∈ t', p.activeNode = none)
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
      have hedec := first.adjointDecision_eq_of_destinations first' rest rest' hn hs hd
      have he := first.event_eq_of_terminal_lookups first' hl hs hedec rest rest' hd
      subst b
      have hu := first.legal.deterministic first'.legal hn
      subst u'
      exact congrArg (List.cons a) (ih rest' (first.legal.support_nodup hn)
        (first.legal.inventory_nodup hs) ht ht' hd)

/-- Both the chronological event list and actual terminal forest are reconstructed. -/
theorem LegalTrace.reconstruct_of_destinations
    {events events' : List Event} {s t t' : List (TaggedPending σ)}
    (h : LegalTrace events s t) (k : LegalTrace events' s t')
    (hn : (forestSupport s).Nodup) (hs : (originInventory s).Nodup)
    (ht : ∀ p ∈ t, p.activeNode = none) (ht' : ∀ p ∈ t', p.activeNode = none)
    (hd : ∀ o, (terminalDestinations t).lookup o = (terminalDestinations t').lookup o) :
    events = events' ∧ t = t' := by
  have he := h.events_eq_of_destinations k hn hs ht ht' hd
  refine ⟨he, ?_⟩
  subst events'
  exact h.deterministic_of_events k hn

/-- Destination-only fixed-order encoding; no event or adjoint-choice field. -/
def destinationArray (origins : List LabelOrigin) (t : List (TaggedPending σ)) :
    List (Option Destination) := origins.map (fun o => (terminalDestinations t).lookup o)

@[simp] theorem destinationArray_eq_encodeFixed_destinations (origins : List LabelOrigin)
    (nodes : List NodeAddress) (events : List Event) (t : List (TaggedPending σ)) :
    destinationArray origins t = (encodeFixed origins nodes events t).destinations := rfl

theorem LegalTrace.destination_lookups_eq_of_array {events events' s t u}
    (h : LegalTrace (σ := σ) events s t) (k : LegalTrace events' s u)
    (origins : List LabelOrigin) (ho : ∀ o ∈ originInventory s, o ∈ origins)
    (he : destinationArray origins t = destinationArray origins u) :
    ∀ o, (terminalDestinations t).lookup o = (terminalDestinations u).lookup o := by
  intro o
  by_cases ha : o ∈ origins
  · exact List.map_inj_left.mp he o ha
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

theorem LegalTrace.reconstruct_of_destination_array
    {events events' : List Event} {s t t' : List (TaggedPending σ)}
    (h : LegalTrace events s t) (k : LegalTrace events' s t')
    (hn : (forestSupport s).Nodup) (hs : (originInventory s).Nodup)
    (ht : ∀ p ∈ t, p.activeNode = none) (ht' : ∀ p ∈ t', p.activeNode = none)
    (origins : List LabelOrigin) (ho : ∀ o ∈ originInventory s, o ∈ origins)
    (he : destinationArray origins t = destinationArray origins t') :
    events = events' ∧ t = t' :=
  h.reconstruct_of_destinations k hn hs ht ht'
    (h.destination_lookups_eq_of_array k origins ho he)

/-- Original syntax supplies all invariants and indices for destination-only replay. -/
theorem LegalTrace.reconstruct_of_initial_destinations
    {r q : ℕ} (e : Expr σ r) (f : Expr σ q) (j k : ℕ)
    {events events' : List Event} {t t' : List (TaggedPending σ)}
    (h : LegalTrace events (initialTwoFormulas e f j k) t)
    (h' : LegalTrace events' (initialTwoFormulas e f j k) t')
    (ht : ∀ p ∈ t, p.activeNode = none) (ht' : ∀ p ∈ t', p.activeNode = none)
    (he : destinationArray (initialOriginOrder e f j k) t =
      destinationArray (initialOriginOrder e f j k) t') :
    events = events' ∧ t = t' := by
  apply h.reconstruct_of_destination_array h' (initialTwoFormulas_support_nodup e f j k)
    (initialTwoFormulas_inventory_nodup e f j k) ht ht'
    (initialOriginOrder e f j k) ?_ he
  intro o ho
  rw [← initialOriginOrder_coe e f j k] at ho
  exact ho


end AcceleratedLogConcave.Tensor.AdjointReduction.ReductionRecords
