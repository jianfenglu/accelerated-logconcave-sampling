import AcceleratedLogConcave.Oracle.Execution
import Mathlib.Algebra.BigOperators.Fin

/-!
# Exact work of finite original-gradient programs

Counts are computed from syntax and proved equal to the actually executed
transcript for every oracle, input, environment and exact tape. No probability
law, almost-sure restriction or correctness certificate is assumed. Repeated
points, unused suppliers and zero coefficients receive no work discount.
This foundation does not assert the recursive compiler's source inventory bound.
-/

namespace AcceleratedLogConcave.Oracle

/-- Three different resource counts; a Gaussian block need not be a scalar. -/
@[ext] structure Counts where
  queries : ℕ
  gaussianBlocks : ℕ
  uniformScalars : ℕ
  deriving DecidableEq, Repr

/-- Count one specified instruction category. -/
def instructionCount (kind : EventKind) (instr : Instr c Γ τ) : ℕ :=
  if instr.eventKind = some kind then 1 else 0

/-- Count all occurrences structurally, including each batch child and tail. -/
def syntaxCount (kind : EventKind) : Prog c Γ τ → ℕ
  | .ret _ => 0
  | .step _ instr next => instructionCount kind instr + syntaxCount kind next
  | .batch _ children next =>
      (List.ofFn fun j => syntaxCount kind (children j)).sum + syntaxCount kind next

def syntaxCounts (p : Prog c Γ τ) : Counts :=
  ⟨syntaxCount .gradient p, syntaxCount .gaussian p, syntaxCount .uniform p⟩

/-- Event counting ignores provenance metadata but not event multiplicity. -/
def shapeCount (kind : EventKind) (events : List (EventKind × Origin)) : ℕ :=
  events.countP fun event => decide (event.1 = kind)

def shapeCounts (events : List (EventKind × Origin)) : Counts :=
  ⟨shapeCount .gradient events, shapeCount .gaussian events, shapeCount .uniform events⟩

def traceCounts (events : List (Event d)) : Counts :=
  shapeCounts (events.map Event.erase)

/-- Public oracle work counts executed calls, not distinct queried locations. -/
def queryCount (p : Prog c Γ τ) : ℕ := (syntaxCounts p).queries

/-- The source's eventual leaf-query plus Gaussian-block bookkeeping quantity. -/
def bookkeepingWork (p : Prog c Γ τ) : ℕ :=
  (syntaxCounts p).queries + (syntaxCounts p).gaussianBlocks

@[simp] theorem shapeCount_append (kind : EventKind)
    (xs ys : List (EventKind × Origin)) :
    shapeCount kind (xs ++ ys) = shapeCount kind xs + shapeCount kind ys :=
  List.countP_append

@[simp] theorem shapeCount_prefix (kind : EventKind) (origin : Origin)
    (xs : List (EventKind × Origin)) :
    shapeCount kind (prefixStaticTrace origin xs) = shapeCount kind xs := by
  simp [shapeCount, prefixStaticTrace, List.countP_map, Function.comp_def]

@[simp] theorem shapeCount_flatten (kind : EventKind)
    (xs : List (List (EventKind × Origin))) :
    shapeCount kind xs.flatten = (xs.map (shapeCount kind)).sum :=
  List.countP_flatten

@[simp] theorem shapeCount_instr (kind : EventKind) (origin : Origin)
    (instr : Instr c Γ τ) :
    shapeCount kind (instr.staticTrace origin) = instructionCount kind instr := by
  cases instr <;> cases kind <;> rfl

theorem shapeCount_staticTrace (kind : EventKind) (p : Prog c Γ τ) :
    shapeCount kind (staticTrace p) = syntaxCount kind p := by
  induction p with
  | ret r => rfl
  | step origin instr next ih =>
      simp only [staticTrace, shapeCount_append, shapeCount_instr, ih, syntaxCount]
  | batch origin children next ihChildren ihNext =>
      simp only [staticTrace, shapeCount_prefix, shapeCount_append, shapeCount_flatten,
        List.map_ofFn, Function.comp_def, ihChildren, ihNext, syntaxCount]

@[simp] theorem map_erase_prefix (origin : Origin) (xs : List (Event d)) :
    (xs.map (Event.withPrefix origin)).map Event.erase =
      prefixStaticTrace origin (xs.map Event.erase) := by
  induction xs with
  | nil => rfl
  | cons event xs ih =>
      cases event <;> simp [Event.erase, Event.withPrefix, prefixStaticTrace, ih]

@[simp] theorem evalInstr_trace_shape (origin : Origin) (instr : Instr c Γ τ)
    (G : Point d → Point d) (i : Inputs d c) (ρ : Env d Γ) (ω : instr.Tape d) :
    (evalInstr origin instr G i ρ ω).trace.map Event.erase = instr.staticTrace origin := by
  cases instr <;> rfl

/-- The complete event-kind/provenance sequence is fixed before oracle replies. -/
theorem run_trace_shape (p : Prog c Γ τ) :
    ∀ (G : Point d → Point d) (i : Inputs d c) (ρ : Env d Γ) (ω : Tape d p),
      (run p G i ρ ω).trace.map Event.erase = staticTrace p := by
  induction p with
  | ret r => intro G i ρ ω; rfl
  | step origin instr next ih =>
      intro G i ρ ω
      simp only [run, List.map_append, evalInstr_trace_shape, ih, staticTrace]
  | batch origin children next ihChildren ihNext =>
      intro G i ρ ω
      simp only [run]
      rw [map_erase_prefix]
      simp only [staticTrace]
      congr 1
      simp only [List.map_append, List.map_flatten, List.map_ofFn, Function.comp_def,
        ihChildren, ihNext]

/-- Exact counts of executed instructions, for every tape, without a law premise. -/
theorem run_counts (p : Prog c Γ τ) (G : Point d → Point d)
    (i : Inputs d c) (ρ : Env d Γ) (ω : Tape d p) :
    traceCounts (run p G i ρ ω).trace = syntaxCounts p := by
  unfold traceCounts
  rw [run_trace_shape]
  apply Counts.ext <;> exact shapeCount_staticTrace _ p

theorem run_query_count_independent (p : Prog c Γ τ)
    (G₁ G₂ : Point d → Point d) (i₁ i₂ : Inputs d c)
    (ρ₁ ρ₂ : Env d Γ) (ω₁ ω₂ : Tape d p) :
    (traceCounts (run p G₁ i₁ ρ₁ ω₁).trace).queries =
      (traceCounts (run p G₂ i₂ ρ₂ ω₂).trace).queries := by
  rw [run_counts, run_counts]

@[simp] theorem queryCount_ret (r : Ref Γ τ) : queryCount (Prog.ret (c := c) r) = 0 := rfl

@[simp] theorem queryCount_step (origin : Origin) (instr : Instr c Γ σ)
    (next : Prog c (σ :: Γ) τ) :
    queryCount (.step origin instr next) = instr.queryCount + queryCount next := by
  cases instr <;> rfl

theorem queryCount_batch (origin : Origin) (children : Fin n → Prog c Γ .point)
    (next : Prog c (List.replicate n .point ++ Γ) τ) :
    queryCount (.batch origin children next) =
      (∑ j, queryCount (children j)) + queryCount next := by
  exact congrArg (fun q => q + queryCount next) (Fin.sum_ofFn _)

theorem syntaxCount_batch (kind : EventKind) (origin : Origin)
    (children : Fin n → Prog c Γ .point)
    (next : Prog c (List.replicate n .point ++ Γ) τ) :
    syntaxCount kind (.batch origin children next) =
      (∑ j, syntaxCount kind (children j)) + syntaxCount kind next := by
  exact congrArg (fun q => q + syntaxCount kind next) (Fin.sum_ofFn _)

theorem gaussianCount_batch (origin : Origin) (children : Fin n → Prog c Γ .point)
    (next : Prog c (List.replicate n .point ++ Γ) τ) :
    (syntaxCounts (.batch origin children next)).gaussianBlocks =
      (∑ j, (syntaxCounts (children j)).gaussianBlocks) + (syntaxCounts next).gaussianBlocks :=
  syntaxCount_batch .gaussian origin children next

theorem uniformCount_batch (origin : Origin) (children : Fin n → Prog c Γ .point)
    (next : Prog c (List.replicate n .point ++ Γ) τ) :
    (syntaxCounts (.batch origin children next)).uniformScalars =
      (∑ j, (syntaxCounts (children j)).uniformScalars) + (syntaxCounts next).uniformScalars :=
  syntaxCount_batch .uniform origin children next

theorem staticTrace_batch (origin : Origin) (children : Fin n → Prog c Γ .point)
    (next : Prog c (List.replicate n .point ++ Γ) τ) :
    staticTrace (.batch origin children next) = prefixStaticTrace origin
      ((List.ofFn fun j => staticTrace (children j)).flatten ++ staticTrace next) := rfl

theorem bookkeepingWork_batch (origin : Origin) (children : Fin n → Prog c Γ .point)
    (next : Prog c (List.replicate n .point ++ Γ) τ) :
    bookkeepingWork (.batch origin children next) =
      (∑ j, bookkeepingWork (children j)) + bookkeepingWork next := by
  unfold bookkeepingWork
  change queryCount (.batch origin children next) +
    (syntaxCounts (.batch origin children next)).gaussianBlocks = _
  rw [queryCount_batch, gaussianCount_batch, Finset.sum_add_distrib]
  simp only [queryCount]
  omega

theorem gaussianCount_eq_tapeShape (p : Prog c Γ τ) :
    (syntaxCounts p).gaussianBlocks = (tapeShape p).gaussianBlocks := by
  change syntaxCount .gaussian p = (tapeShape p).gaussianBlocks
  induction p with
  | ret r => rfl
  | step origin instr next ih =>
      cases instr <;> simp [syntaxCount, instructionCount, Instr.eventKind,
        tapeShape, Instr.gaussianCount, ih]
  | batch origin children next ihChildren ihNext =>
      simp only [syntaxCount, tapeShape, ihChildren, ihNext]

theorem uniformCount_eq_tapeShape (p : Prog c Γ τ) :
    (syntaxCounts p).uniformScalars = (tapeShape p).uniformScalars := by
  change syntaxCount .uniform p = (tapeShape p).uniformScalars
  induction p with
  | ret r => rfl
  | step origin instr next ih =>
      cases instr <;> simp [syntaxCount, instructionCount, Instr.eventKind,
        tapeShape, Instr.uniformCount, ih]
  | batch origin children next ihChildren ihNext =>
      simp only [syntaxCount, tapeShape, ihChildren, ihNext]

/-- A concrete event has a truthful original-gradient answer, if it is a query. -/
def Event.answers (G : Point d → Point d) : Event d → Prop
  | .gradient _ x a => a = G x
  | _ => True

@[simp] theorem Event.answers_withPrefix (G : Point d → Point d)
    (origin : Origin) (event : Event d) :
    (event.withPrefix origin).answers G ↔ event.answers G := by
  cases event <;> rfl

theorem evalInstr_answers (origin : Origin) (instr : Instr c Γ τ)
    (G : Point d → Point d) (i : Inputs d c) (ρ : Env d Γ) (ω : instr.Tape d) :
    ∀ event ∈ (evalInstr origin instr G i ρ ω).trace, event.answers G := by
  cases instr <;> simp [evalInstr, Event.answers]

theorem run_event_answers (p : Prog c Γ τ) :
    ∀ (G : Point d → Point d) (i : Inputs d c) (ρ : Env d Γ) (ω : Tape d p),
      ∀ event ∈ (run p G i ρ ω).trace, event.answers G := by
  induction p with
  | ret r => intro G i ρ ω; simp [run]
  | step origin instr next ih =>
      intro G i ρ ω event he
      change event ∈ (evalInstr origin instr G i ρ ω.1).trace ++ _ at he
      rcases List.mem_append.mp he with he | he
      · exact evalInstr_answers origin instr G i ρ ω.1 event he
      · exact ih G i _ ω.2 event he
  | batch origin children next ihChildren ihNext =>
      intro G i ρ ω event he
      simp only [run, List.mem_map] at he
      obtain ⟨event', he', rfl⟩ := he
      apply (Event.answers_withPrefix G origin event').mpr
      rcases List.mem_append.mp he' with he' | he'
      · obtain ⟨events, hEvents, hEvent⟩ := List.mem_flatten.mp he'
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hEvents
        exact ihChildren j G i ρ (ω.1 j) event' hEvent
      · exact ihNext G i _ ω.2 event' he'

/-- Every recorded answer is the supplied original oracle at its recorded point. -/
theorem run_answers (p : Prog c Γ τ) (G : Point d → Point d)
    (i : Inputs d c) (ρ : Env d Γ) (ω : Tape d p) :
    ∀ origin x a, Event.gradient origin x a ∈ (run p G i ρ ω).trace → a = G x := by
  intro origin x a he
  exact run_event_answers p G i ρ ω (.gradient origin x a) he

theorem evalInstr_zero_query (origin : Origin) (instr : Instr c Γ τ)
    (h : instr.queryCount = 0) (G₁ G₂ : Point d → Point d)
    (i : Inputs d c) (ρ : Env d Γ) (ω : instr.Tape d) :
    evalInstr origin instr G₁ i ρ ω = evalInstr origin instr G₂ i ρ ω := by
  cases instr <;> simp_all [Instr.queryCount, evalInstr]

/-- A zero-query program's result is oracle-independent, with inputs/tape fixed.
Programs with queries can have oracle-dependent values and query locations. -/
theorem run_zero_query (p : Prog c Γ τ) :
    queryCount p = 0 → ∀ (G₁ G₂ : Point d → Point d) (i : Inputs d c)
      (ρ : Env d Γ) (ω : Tape d p),
      (run p G₁ i ρ ω).value = (run p G₂ i ρ ω).value := by
  induction p with
  | ret r => intro hp G₁ G₂ i ρ ω; rfl
  | step origin instr next ih =>
      intro hp G₁ G₂ i ρ ω
      rw [queryCount_step] at hp
      obtain ⟨hi, hn⟩ := Nat.add_eq_zero_iff.mp hp
      have he := evalInstr_zero_query origin instr hi G₁ G₂ i ρ ω.1
      simp only [run]
      rw [he]
      exact ih hn G₁ G₂ i _ ω.2
  | batch origin children next ihChildren ihNext =>
      intro hp G₁ G₂ i ρ ω
      rw [queryCount_batch] at hp
      obtain ⟨hc, hn⟩ := Nat.add_eq_zero_iff.mp hp
      have hz (j : Fin _) : queryCount (children j) = 0 :=
        (Finset.sum_eq_zero_iff.mp hc) j (Finset.mem_univ j)
      have he : (fun j => (run (children j) G₁ i ρ (ω.1 j)).value) =
          (fun j => (run (children j) G₂ i ρ (ω.1 j)).value) :=
        funext fun j => ihChildren j (hz j) G₁ G₂ i ρ (ω.1 j)
      simp only [run]
      rw [he]
      exact ihNext hn G₁ G₂ i _ ω.2

/-- Dimension metadata of actual Gaussian events, retaining zero-dimensional blocks. -/
def gaussianDimensions (events : List (Event d)) : List ℕ :=
  events.filterMap Event.gaussianDimension

theorem gaussianDimensions_length (events : List (Event d)) :
    (gaussianDimensions events).length = (traceCounts events).gaussianBlocks := by
  induction events with
  | nil => rfl
  | cons event events ih =>
      cases event <;> simp_all [gaussianDimensions, Event.gaussianDimension, traceCounts,
        shapeCounts, shapeCount, Event.erase, List.filterMap_cons, Nat.add_comm]

theorem gaussianDimensions_sum (events : List (Event d)) :
    (gaussianDimensions events).sum = d * (traceCounts events).gaussianBlocks := by
  induction events with
  | nil => simp [gaussianDimensions, traceCounts, shapeCounts, shapeCount]
  | cons event events ih =>
      cases event <;> simp_all [gaussianDimensions, Event.gaussianDimension, traceCounts,
        shapeCounts, shapeCount, Event.erase, List.filterMap_cons, Nat.mul_add, Nat.add_comm]

theorem run_gaussian_scalar_coordinates (p : Prog c Γ τ) (G : Point d → Point d)
    (i : Inputs d c) (ρ : Env d Γ) (ω : Tape d p) :
    (gaussianDimensions (run p G i ρ ω).trace).sum = d * (tapeShape p).gaussianBlocks := by
  rw [gaussianDimensions_sum, run_counts, gaussianCount_eq_tapeShape]

end AcceleratedLogConcave.Oracle
