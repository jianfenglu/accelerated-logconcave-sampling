import AcceleratedLogConcave.Tensor.ReductionCount

/-! The literal local branch lists and their terminal expansion multiplicities. -/

namespace AcceleratedLogConcave.Tensor.AdjointReduction

/-- Mapping symbolic origins preserves the entire ordered route list, including
multiplicities when distinct origins have equal interpreted values. -/
theorem routes_map_exact {L M : Type*} (f : L → M) (J : List L) :
    routes (J.map f) = (routes J).map (fun p => (p.1.map f, p.2.map f)) := by
  induction J with
  | nil => simp [routes]
  | cons i J ih => simp [routes, ih, List.map_map, Function.comp_def]

/-- The nonempty-score route list also commutes exactly with arbitrary erasure;
no injectivity of the value map is assumed. -/
theorem scoreRoutes_map_exact {L M : Type*} (f : L → M) (J : List L) :
    scoreRoutes (J.map f) = (scoreRoutes J).map (fun p => (p.1.map f, p.2.map f)) := by
  induction J with
  | nil => simp [scoreRoutes]
  | cons i J ih => simp [scoreRoutes, ih, routes_map_exact, List.map_map, Function.comp_def]

end AcceleratedLogConcave.Tensor.AdjointReduction

namespace AcceleratedLogConcave.Tensor.AdjointReduction

/-- Distinct symbolic origins make positional route enumeration duplicate-free;
this deliberately imposes no condition on their later numeric interpretation. -/
theorem routes_nodup_of_nodup {L : Type*} {J : List L} (hJ : J.Nodup) :
    (routes J).Nodup := by
  induction J with
  | nil => simp [routes]
  | cons i J ih =>
    obtain ⟨hi, hJ⟩ := List.nodup_cons.mp hJ
    rw [routes]
    apply List.nodup_append.mpr
    refine ⟨(ih hJ).map ?_, (ih hJ).map ?_, ?_⟩
    · intro p q he
      apply Prod.ext
      · simpa using congrArg (fun z : List L × List L => z.1) he
      · exact List.cons.inj (congrArg Prod.snd he) |>.2
    · intro p q he
      apply Prod.ext
      · exact List.cons.inj (congrArg Prod.fst he) |>.2
      · simpa using congrArg (fun z : List L × List L => z.2) he
    · intro p hp q hq he
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hq
      have he' : x.1 = i :: y.1 := congrArg Prod.fst he
      have hm : i ∈ x.1 := by rw [he']; simp
      exact hi ((route_sublists J x hx).1.subset hm)

theorem scoreRoutes_nodup_of_nodup {L : Type*} {J : List L} (hJ : J.Nodup) :
    (scoreRoutes J).Nodup := by
  have hh := routes_nodup_of_nodup hJ
  rw [routes_eq] at hh
  exact (List.nodup_cons.mp hh).2

end AcceleratedLogConcave.Tensor.AdjointReduction

namespace AcceleratedLogConcave.Tensor.AdjointReduction.ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name}

/-- Each contract route occupies exactly one local event slot. -/
theorem contract_events_nodup (a : NodeAddress) {J : List LabelOrigin} (hJ : J.Nodup) :
    ((routes J).map (fun p => Event.contract a p.1 p.2)).Nodup := by
  apply (routes_nodup_of_nodup hJ).map
  intro p q h
  exact Prod.ext (Event.contract.inj h).2.1 (Event.contract.inj h).2.2

/-- Score route multiplicity is likewise positional before numeric erasure. -/
theorem score_events_nodup (a : NodeAddress) {J : List LabelOrigin} (hJ : J.Nodup) :
    ((scoreRoutes J).map (fun p => Event.score a p.1 p.2)).Nodup := by
  apply (scoreRoutes_nodup_of_nodup hJ).map
  intro p q h
  exact Prod.ext (Event.score.inj h).2.1 (Event.score.inj h).2.2

/-- Enumerating distinct old recipient occurrences cannot duplicate an IBP event. -/
theorem ibp_events_nodup (a : NodeAddress) (recipients : List (TaggedPending σ))
    (hn : (recipients.map TaggedPending.tag).Nodup) :
    (recipients.map (fun p => Event.ibp a p.tag)).Nodup := by
  have hh := hn.map (fun _ _ he => (Event.ibp.inj he).2)
    (f := Event.ibp a)
  simpa only [List.map_map, Function.comp_def] using hh

/-- Score and IBP slots form disjoint branches even if erased tensor values coincide. -/
theorem adjoint_events_nodup (a : NodeAddress) {J : List LabelOrigin} (hJ : J.Nodup)
    (recipients : List (TaggedPending σ)) (hn : (recipients.map TaggedPending.tag).Nodup) :
    (((scoreRoutes J).map (fun p => Event.score a p.1 p.2)) ++
      recipients.map (fun p => Event.ibp a p.tag)).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨score_events_nodup a hJ, ibp_events_nodup a recipients hn, ?_⟩
  intro x hx y hy he
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hy
  cases he

end AcceleratedLogConcave.Tensor.AdjointReduction.ReductionRecords
namespace AcceleratedLogConcave.Tensor.AdjointReduction.ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name}

def pendingEvents (s : List (TaggedPending σ)) : TaggedPending σ → List Event
  | .formula a (.permute ..) _ => [.permute a]
  | .formula a (.derivative ..) _ => [.derivative a]
  | .formula a (.contract ..) J => (routes J).map (fun p => .contract a p.1 p.2)
  | .formula a (.adjoint ..) J =>
      (scoreRoutes J).map (fun p => .score a p.1 p.2) ++
        (s.filter (fun q => q.tag != .formula a)).map (fun q => .ibp a q.tag)
  | _ => []

def localEvents (s : List (TaggedPending σ)) : List Event :=
  s.flatMap (fun p => if p.activeNode = firstNonterminal s then pendingEvents s p else [])

theorem TaggedStep.event_mem_pending {event : Event} {s t : List (TaggedPending σ)}
    (h : TaggedStep event t s) (hn : (s.map TaggedPending.tag).Nodup) :
    ∃ p ∈ s, event ∈ pendingEvents s p ∧ p.activeNode = some event.node := by
  cases h with
  | permute a perm e J before after =>
    exact ⟨.formula a (.permute perm e) J, by simp, by simp [pendingEvents], rfl⟩
  | derivative a e J before after =>
    exact ⟨.formula a (.derivative e) J, by simp, by simp [pendingEvents], rfl⟩
  | contract a e f i j J A B route before after =>
    refine ⟨.formula a (.contract e f i j) J, by simp, ?_, rfl⟩
    exact List.mem_map.mpr ⟨(A,B), route, rfl⟩
  | score a e i J A B route before after =>
    refine ⟨.formula a (.adjoint i e) J, by simp, ?_, rfl⟩
    exact List.mem_append_left _ (List.mem_map.mpr ⟨(A,B), route, rfl⟩)
  | ibpAfter a e i J other before between after =>
    have hne := (TaggedStep.ibpAfter a e i J other before between after).ibp_recipient_ne_redex hn
    refine ⟨.formula a (.adjoint i e) J, by simp, ?_, rfl⟩
    apply List.mem_append_right
    apply List.mem_map.mpr
    refine ⟨other, ?_, rfl⟩
    simp [hne]
  | ibpBefore a e i J other before between after =>
    have hne := (TaggedStep.ibpBefore a e i J other before between after).ibp_recipient_ne_redex hn
    refine ⟨.formula a (.adjoint i e) J, by simp, ?_, rfl⟩
    apply List.mem_append_right
    apply List.mem_map.mpr
    refine ⟨other, ?_, rfl⟩
    simp [hne]

theorem CanonicalStep.event_mem_localEvents {event : Event} {s t : List (TaggedPending σ)}
    (h : CanonicalStep event t s) (hn : (s.map TaggedPending.tag).Nodup) :
    event ∈ localEvents s := by
  obtain ⟨p,hp,he,ha⟩ := h.legal.event_mem_pending hn
  apply List.mem_flatMap.mpr
  refine ⟨p,hp,?_⟩
  simp [ha, h.scheduled, he]


theorem ibp_step_of_recipient {r : ℕ} (a : NodeAddress) (e : Expr σ (r+2))
    (i : Fin (r+2)) (J : List LabelOrigin) {s : List (TaggedPending σ)}
    (hp : TaggedPending.formula a (.adjoint i e) J ∈ s) {other : TaggedPending σ}
    (hq : other ∈ s) (hne : other.tag ≠ .formula a) :
    ∃ t, TaggedStep (.ibp a other.tag) t s := by
  obtain ⟨before, after, rfl⟩ := List.mem_iff_append.mp hp
  simp only [List.mem_append, List.mem_cons] at hq
  rcases hq with hq | he | hq
  · obtain ⟨left, middle, rfl⟩ := List.mem_iff_append.mp hq
    refine ⟨left ++ [other.decorate (.ibp a)] ++ middle ++
      [.formula (a.child false) e J] ++ after, ?_⟩
    simpa [List.append_assoc] using TaggedStep.ibpBefore a e i J other left middle after
  · exact False.elim (hne (by rw [he]; rfl))
  · obtain ⟨middle, right, rfl⟩ := List.mem_iff_append.mp hq
    refine ⟨before ++ [.formula (a.child false) e J] ++ middle ++
      [other.decorate (.ibp a)] ++ right, ?_⟩
    simpa [List.append_assoc] using TaggedStep.ibpAfter a e i J other before middle right

theorem pendingEvents_sound {s : List (TaggedPending σ)} {p : TaggedPending σ} {event : Event}
    (hp : p ∈ s) (he : event ∈ pendingEvents s p) :
    p.activeNode = some event.node ∧ ∃ t, TaggedStep event t s := by
  cases p with
  | score => simp [pendingEvents] at he
  | formula a e J =>
    cases e with
    | coefficient => simp [pendingEvents] at he
    | permute perm e =>
      have he' : event = .permute a := by simpa [pendingEvents] using he
      subst event
      refine ⟨rfl, ?_⟩
      obtain ⟨before,after,rfl⟩ := List.mem_iff_append.mp hp
      exact ⟨_, by simpa using TaggedStep.permute a perm e J before after⟩
    | derivative e =>
      have he' : event = .derivative a := by simpa [pendingEvents] using he
      subst event
      refine ⟨rfl, ?_⟩
      obtain ⟨before,after,rfl⟩ := List.mem_iff_append.mp hp
      exact ⟨_, by simpa using TaggedStep.derivative a e J before after⟩
    | contract e f i j =>
      obtain ⟨⟨A,B⟩,hr,rfl⟩ := List.mem_map.mp he
      refine ⟨rfl, ?_⟩
      obtain ⟨before,after,rfl⟩ := List.mem_iff_append.mp hp
      exact ⟨_, by simpa using TaggedStep.contract a e f i j J A B hr before after⟩
    | adjoint i e =>
      rcases List.mem_append.mp he with he | he
      · obtain ⟨⟨A,B⟩,hr,rfl⟩ := List.mem_map.mp he
        refine ⟨rfl, ?_⟩
        obtain ⟨before,after,rfl⟩ := List.mem_iff_append.mp hp
        exact ⟨_, by simpa using TaggedStep.score a e i J A B hr before after⟩
      · obtain ⟨other,hm,rfl⟩ := List.mem_map.mp he
        obtain ⟨hq,hne⟩ := List.mem_filter.mp hm
        refine ⟨rfl, ibp_step_of_recipient a e i J hp hq ?_⟩
        simpa using hne

theorem localEvents_sound {s : List (TaggedPending σ)} {event : Event}
    (he : event ∈ localEvents s) : ∃ t, CanonicalStep event t s := by
  obtain ⟨p,hp,he⟩ := List.mem_flatMap.mp he
  split_ifs at he with ha
  · obtain ⟨hc,t,ht⟩ := pendingEvents_sound hp he
    exact ⟨t,ht,ha.symm.trans hc⟩
  · simp at he

theorem TaggedPending.activeNode_tag {p : TaggedPending σ} {a : NodeAddress}
    (h : p.activeNode = some a) : p.tag = .formula a := by
  cases p with
  | score => simp [TaggedPending.activeNode] at h
  | formula b e J => cases e <;> simp_all [TaggedPending.activeNode, TaggedPending.tag]

theorem pendingEvents_nodup {s : List (TaggedPending σ)} {p : TaggedPending σ}
    (hp : p ∈ s) (hn : (s.map TaggedPending.tag).Nodup)
    (hs : (originInventory s).Nodup) : (pendingEvents s p).Nodup := by
  have hlabels : p.labels.Nodup := by
    have hall : (attachedOrigins s).Nodup := Multiset.coe_nodup.mp (Multiset.nodup_add.mp hs).1
    exact (List.nodup_flatMap.mp hall).1 p hp
  cases p with
  | score => simp [pendingEvents]
  | formula a e J =>
    cases e with
    | coefficient => simp [pendingEvents]
    | permute => simp [pendingEvents]
    | derivative => simp [pendingEvents]
    | contract => exact contract_events_nodup a hlabels
    | adjoint =>
      apply adjoint_events_nodup a hlabels
      exact hn.sublist ((List.filter_sublist).map TaggedPending.tag)

theorem localEvents_nodup {s : List (TaggedPending σ)}
    (hn : (s.map TaggedPending.tag).Nodup) (hs : (originInventory s).Nodup) :
    (localEvents s).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro p hp
    split_ifs
    · exact pendingEvents_nodup hp hn hs
    · simp
  · have hpair : s.Pairwise (fun p q => p.tag ≠ q.tag) := List.pairwise_map.mp hn
    apply hpair.imp_of_mem
    intro p q hp hq hne
    change List.Disjoint (if p.activeNode = firstNonterminal s then pendingEvents s p else [])
      (if q.activeNode = firstNonterminal s then pendingEvents s q else [])
    split_ifs with hpa hqa
    · intro event hep heq
      have hp' := (pendingEvents_sound hp hep).1
      have hq' := (pendingEvents_sound hq heq).1
      exact hne ((TaggedPending.activeNode_tag hp').trans (TaggedPending.activeNode_tag hq').symm)
    all_goals simp

/-- Concrete target list: no deduplication or quotienting of expansion branches. -/
def nextBranches (s : List (TaggedPending σ)) : List (Event × List (TaggedPending σ)) :=
  (localEvents s).map (fun event => (event, interpretEvent event s))

theorem nextBranches_legal {s : List (TaggedPending σ)}
    (hn : (s.map TaggedPending.tag).Nodup) :
    ∀ edge ∈ nextBranches s, CanonicalStep edge.1 edge.2 s := by
  intro edge he
  obtain ⟨event,hm,rfl⟩ := List.mem_map.mp he
  obtain ⟨t,ht⟩ := localEvents_sound hm
  rw [ht.legal.interpret hn]
  exact ht

theorem nextBranches_complete {s : List (TaggedPending σ)}
    (hn : (s.map TaggedPending.tag).Nodup) {event : Event} {t : List (TaggedPending σ)}
    (h : CanonicalStep event t s) : (event,t) ∈ nextBranches s := by
  exact List.mem_map.mpr ⟨event,h.event_mem_localEvents hn,by rw [h.legal.interpret hn]⟩

theorem nextBranches_unique {s : List (TaggedPending σ)}
    (hn : (s.map TaggedPending.tag).Nodup) (hs : (originInventory s).Nodup) :
    ((nextBranches s).map Prod.fst).Nodup := by
  simpa [nextBranches, List.map_map, Function.comp_def] using localEvents_nodup hn hs

/-- A finite exhaustive ordered expansion tree. The only distinctness premise is
local event uniqueness, not uniqueness of terminal outputs or full paths. -/
inductive ExpansionTree : List (TaggedPending σ) → Type _
  | leaf {s : List (TaggedPending σ)} (terminal : ∀ p ∈ s, p.activeNode = none) : ExpansionTree s
  | node {s : List (TaggedPending σ)}
      (active : firstNonterminal s ≠ none)
      (edges : List (Event × List (TaggedPending σ)))
      (legal : ∀ edge ∈ edges, CanonicalStep edge.1 edge.2 s)
      (complete : ∀ event target, CanonicalStep event target s → (event,target) ∈ edges)
      (unique : (edges.map Prod.fst).Nodup)
      (child : ∀ edge, edge ∈ edges → ExpansionTree edge.2) : ExpansionTree s

/-- Literal leaf expansion: event-prefixing and concatenation, with no deduplication. -/
def ExpansionTree.branches {s : List (TaggedPending σ)} : ExpansionTree s →
    List (List Event × List (TaggedPending σ))
  | .leaf _ => [([],s)]
  | .node _ edges _ _ _ child => edges.attach.flatMap (fun edge =>
      ((child edge.val edge.property).branches).map (fun run => (edge.val.1 :: run.1, run.2)))

private theorem prefixBranch_injective (event : Event) :
    Function.Injective (fun run : List Event × List (TaggedPending σ) => (event :: run.1, run.2)) := by
  intro x y he
  apply Prod.ext
  · exact (List.cons.inj (congrArg Prod.fst he)).2
  · have hh := congrArg Prod.snd he
    exact hh

/-- Every enumerated leaf is an independently legal terminal branch. -/
theorem ExpansionTree.branch_sound {s : List (TaggedPending σ)} (tree : ExpansionTree s)
    (run : List Event × List (TaggedPending σ)) (hr : run ∈ tree.branches) :
    LegalTrace run.1 s run.2 ∧ ∀ p ∈ run.2, p.activeNode = none := by
  induction tree generalizing run with
  | @leaf s terminal =>
    have he : run = ([], s) := by simpa [ExpansionTree.branches] using hr
    subst run
    exact ⟨LegalTrace.nil _, terminal⟩
  | node active edges legal complete unique child ih =>
    obtain ⟨edge, _, hrun⟩ := List.mem_flatMap.mp hr
    obtain ⟨tail, ht, he⟩ := List.mem_map.mp hrun
    subst run
    obtain ⟨hl, hterm⟩ := ih edge.val edge.property tail ht
    exact ⟨LegalTrace.cons (legal _ edge.property) hl, hterm⟩

/-- Local branch uniqueness propagates to full paths; equal endpoint forests remain separate. -/
theorem ExpansionTree.branches_nodup {s : List (TaggedPending σ)} (tree : ExpansionTree s) :
    tree.branches.Nodup := by
  induction tree with
  | leaf => simp [ExpansionTree.branches]
  | node active edges legal complete unique child ih =>
    apply List.nodup_flatMap.mpr
    constructor
    · intro edge _
      exact (ih edge.val edge.property).map (prefixBranch_injective edge.val.1)
    · apply List.pairwise_iff_get.mpr
      intro i j hij run hi hj
      obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hi
      obtain ⟨y, hy, hye⟩ := List.mem_map.mp hj
      have he : (edges.attach.get i).val.1 = (edges.attach.get j).val.1 :=
        (List.cons.inj (congrArg Prod.fst (hxe.trans hye.symm))).1
      have hi' : i.val < (edges.map Prod.fst).length := by simpa using i.isLt
      have hj' : j.val < (edges.map Prod.fst).length := by simpa using j.isLt
      have hget : (edges.map Prod.fst).get ⟨i.val,hi'⟩ =
          (edges.map Prod.fst).get ⟨j.val,hj'⟩ := by simpa using he
      have heq := unique.injective_get hget
      have hv := congrArg Fin.val heq
      change i.val = j.val at hv
      exact (Nat.ne_of_lt hij) hv

/-- A local grammar listing, complete for the relation and without repeated event alternatives. -/
structure CanonicalListing (s : List (TaggedPending σ)) where
  edges : List (Event × List (TaggedPending σ))
  legal : ∀ edge ∈ edges, CanonicalStep edge.1 edge.2 s
  complete : ∀ event target, CanonicalStep event target s → (event,target) ∈ edges
  unique : (edges.map Prod.fst).Nodup

def ExpansionTree.ofListing {s : List (TaggedPending σ)} (listing : CanonicalListing s)
    (active : firstNonterminal s ≠ none)
    (child : ∀ edge, edge ∈ listing.edges → ExpansionTree edge.2) : ExpansionTree s :=
  .node active listing.edges listing.legal listing.complete listing.unique child

/-- Completeness follows the independent local relation, including every ordered route. -/
theorem ExpansionTree.branch_complete {s : List (TaggedPending σ)} (tree : ExpansionTree s)
    {events : List Event} {t : List (TaggedPending σ)}
    (h : LegalTrace events s t) (ht : ∀ p ∈ t, p.activeNode = none) :
    (events,t) ∈ tree.branches := by
  induction tree generalizing events t with
  | @leaf s terminal =>
    cases h with
    | nil => simp [ExpansionTree.branches]
    | cons first rest =>
      have hh := (firstNonterminal_eq_none s).mpr terminal
      rw [first.scheduled] at hh
      contradiction
  | @node s active edges legal complete unique child ih =>
    cases h with
    | nil =>
      exact False.elim (active ((firstNonterminal_eq_none s).mpr ht))
    | @cons event events _ target t first rest =>
      have hm := complete event target first
      apply List.mem_flatMap.mpr
      refine ⟨⟨(event,target),hm⟩, List.mem_attach _ _, ?_⟩
      apply List.mem_map.mpr
      exact ⟨(events,t), ih _ hm rest ht, rfl⟩

def ExpansionTree.branchAt {s : List (TaggedPending σ)} (tree : ExpansionTree s)
    (i : Fin tree.branches.length) : TerminalRun s :=
  let run := tree.branches.get i
  let hs := tree.branch_sound run (List.get_mem _ _)
  ⟨run.1, run.2, hs.1, hs.2⟩

theorem ExpansionTree.branchAt_injective {s : List (TaggedPending σ)} (tree : ExpansionTree s) :
    Function.Injective tree.branchAt := by
  intro i j he
  apply tree.branches_nodup.injective_get
  apply Prod.ext
  · exact congrArg TerminalRun.events he
  · exact congrArg TerminalRun.terminal he

theorem ExpansionTree.branchAt_surjective {s : List (TaggedPending σ)} (tree : ExpansionTree s) :
    Function.Surjective tree.branchAt := by
  intro run
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp (tree.branch_complete run.legal run.terminality)
  refine ⟨i, ?_⟩
  apply TerminalRun.ext
  · exact congrArg Prod.fst hi
  · exact congrArg Prod.snd hi

/-- Concrete expansion multiplicity is exactly the cardinality of full legal terminal runs. -/
theorem ExpansionTree.branches_length_eq_card {s : List (TaggedPending σ)}
    (tree : ExpansionTree s) : tree.branches.length = Nat.card (TerminalRun s) := by
  let eqv : Fin tree.branches.length ≃ TerminalRun s :=
    Equiv.ofBijective tree.branchAt ⟨tree.branchAt_injective, tree.branchAt_surjective⟩
  simpa only [Nat.card_fin] using Nat.card_congr eqv

theorem ExpansionTree.branches_length_le_destination_count {s : List (TaggedPending σ)}
    (tree : ExpansionTree s) (origins : List LabelOrigin) (alphabet : List Destination)
    (hmem : ∀ (run : TerminalRun s) o d, o ∈ origins →
      (terminalDestinations run.terminal).lookup o = some d → d ∈ alphabet)
    (hinj : Function.Injective (TerminalRun.destinationList (s := s) origins)) :
    tree.branches.length ≤ (alphabet.length + 1) ^ origins.length := by
  rw [tree.branches_length_eq_card]
  exact TerminalRun.card_le_of_destinationList origins alphabet hmem hinj

/-- The verified literal route and recipient enumeration packages the local interface. -/
def canonicalListing (s : List (TaggedPending σ))
    (hn : (forestSupport s).Nodup) (hs : (originInventory s).Nodup) : CanonicalListing s where
  edges := nextBranches s
  legal := nextBranches_legal (liveTags_nodup_of_support s hn)
  complete := fun _ _ h => nextBranches_complete (liveTags_nodup_of_support s hn) h
  unique := nextBranches_unique (liveTags_nodup_of_support s hn) hs

/-- Recursion follows the exact strictly decreasing syntax rank. Every listed
alternative is retained, even if two interpretations happen to have equal values. -/
noncomputable def ExpansionTree.build (s : List (TaggedPending σ))
    (hn : (forestSupport s).Nodup) (hs : (originInventory s).Nodup) : ExpansionTree s := by
  classical
  apply canonical_wellFounded.fix
    (C := fun s => (forestSupport s).Nodup → (originInventory s).Nodup → ExpansionTree s)
    (fun s rec hn hs => ?_) s hn hs
  by_cases ht : firstNonterminal s = none
  · exact .leaf ((firstNonterminal_eq_none s).mp ht)
  · let listing := canonicalListing s hn hs
    exact listing |> fun listing => ExpansionTree.ofListing listing ht
      (fun edge he => rec edge.2 ⟨edge.1, listing.legal edge he⟩
        ((listing.legal edge he).legal.support_nodup hn)
        ((listing.legal edge he).legal.inventory_nodup hs))

/-- Literal canonical expansion, with full event paths and endpoints retained. -/
noncomputable def terminalBranches (s : List (TaggedPending σ))
    (hn : (forestSupport s).Nodup) (hs : (originInventory s).Nodup) :=
  (ExpansionTree.build s hn hs).branches

theorem terminalBranches_length_eq_card (s : List (TaggedPending σ))
    (hn : (forestSupport s).Nodup) (hs : (originInventory s).Nodup) :
    (terminalBranches s hn hs).length = Nat.card (TerminalRun s) :=
  (ExpansionTree.build s hn hs).branches_length_eq_card

/-- The actual literal two-copy expansion has the stated dimension-free multiplicity. -/
theorem terminalBranches_twoCopy_bound {r : ℕ} (e : Expr σ r) (j : ℕ) :
    (terminalBranches (initialTwoFormulas e e j j)
      (initialTwoFormulas_support_nodup e e j j)
      (initialTwoFormulas_inventory_nodup e e j j)).length ≤
      (e.size + 2) ^ (2 * (j + e.weightedOperationCount)) := by
  rw [terminalBranches_length_eq_card]
  exact TerminalRun.twoCopy_card_bound e j

theorem terminalBranches_twoCopy_le_size_power {r : ℕ} (e : Expr σ r) (j : ℕ) :
    (terminalBranches (initialTwoFormulas e e j j)
      (initialTwoFormulas_support_nodup e e j j)
      (initialTwoFormulas_inventory_nodup e e j j)).length ≤
      (2 * (e.size + j)) ^ (2 * (e.size + j)) := by
  rw [terminalBranches_length_eq_card]
  exact TerminalRun.twoCopy_card_le_size_power e j

end AcceleratedLogConcave.Tensor.AdjointReduction.ReductionRecords
