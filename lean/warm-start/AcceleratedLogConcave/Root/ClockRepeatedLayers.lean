import AcceleratedLogConcave.Root.ClockPublicSetup
import AcceleratedLogConcave.Oracle.RecursiveMeanOperational

/-! Public split, one initialization, and the existing continuation-preserving
loop at a fixed outer clock. No final child calls or retained correction. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Root.ClockRepeatedLayers
open Oracle Oracle.AffineLowering Oracle.NoisyLayer Oracle.TapeLowering
open Oracle.RecursiveMeanProgram Oracle.RecursiveMeanContinuation
open ClockNoisyLayer
open scoped BigOperators

variable (P : SourceSchedule)
abbrev entryCtx : Ctx := replyCtx (N P) (replyCtx (N P) (ClockPublicSetup.readyCtx P))
def oldRef (i : Index P) : Ref (entryCtx P) .point := batchRef i
def directRef (i : Index P) : Ref (entryCtx P) .point :=
  RefMap.shiftMany (N P) (RefMap.shiftMany (N P) (ClockPublicSetup.directRef P i))
def retained : RefMap (ClockPublicSetup.readyCtx P) (entryCtx P) :=
  fun r => RefMap.shiftMany (N P) (RefMap.shiftMany (N P) r)
def momentumRef : Ref (entryCtx P) .point := retained P (ClockPublicSetup.saved P ClockPublicSetup.pRef)
def initialCenters {d : ℕ} (clock : ClockLaw.Clock) (xF momentum E0 : Point d) (Z0 : Index P → Point d) : Index P → Point d :=
  fun i => b P clock xF (ClockPublicSetup.splitValues momentum E0 0) i+rhoC P • Z0 i
def entryEnv {d : ℕ} (clock : ClockLaw.Clock) (xF momentum E0 : Point d) (Z0 : Index P → Point d) : Env d (entryCtx P) :=
  Env.prepend (initialCenters P clock xF momentum E0 Z0) (Env.prepend Z0 (ClockPublicSetup.readyEnv P clock xF momentum E0))

theorem entry_old {d : ℕ} (clock : ClockLaw.Clock) (xF momentum E0 : Point d) (Z0 : Index P → Point d) (i : Index P) :
    storedPoint (entryEnv P clock xF momentum E0 Z0) (oldRef P i) = initialCenters P clock xF momentum E0 Z0 i := prepend_batchRef _ _ _
theorem entry_retained {d : ℕ} (clock : ClockLaw.Clock) (xF momentum E0 : Point d) (Z0 : Index P → Point d)
    (r : Ref (ClockPublicSetup.readyCtx P) .point) :
    storedPoint (entryEnv P clock xF momentum E0 Z0) (retained P r) = storedPoint (ClockPublicSetup.readyEnv P clock xF momentum E0) r := by
  exact (prepend_shiftMany _ _ _).trans (prepend_shiftMany _ _ _)
theorem entry_direct {d : ℕ} (clock : ClockLaw.Clock) (xF momentum E0 : Point d) (Z0 : Index P → Point d) (i : Index P) :
    storedPoint (entryEnv P clock xF momentum E0 Z0) (directRef P i) = b P clock xF (ClockPublicSetup.splitValues momentum E0 0) i :=
  (entry_retained P clock xF momentum E0 Z0 _).trans (ClockPublicSetup.ready_direct P clock xF momentum E0 i)
theorem entry_momentum {d : ℕ} (clock : ClockLaw.Clock) (xF momentum E0 : Point d) (Z0 : Index P → Point d) :
    storedPoint (entryEnv P clock xF momentum E0 Z0) (momentumRef P) = momentum :=
  (entry_retained P clock xF momentum E0 Z0 _).trans (ClockPublicSetup.ready_saved P clock xF momentum E0 _)

/-- The executable uses remaining-depth labels; metadata uses chronological ones. -/
def chronological (D remaining : ℕ) : ℕ := D-1-remaining

theorem chronological_at (D k : ℕ) (hk : k < D) : chronological D (D-1-k) = k := by unfold chronological;omega
theorem chronological_first (D : ℕ) : chronological (D+1) D = 0 := by unfold chronological;omega

def designated (D remaining : ℕ) (i : Index P) : Origin := [⟨.publicSampling,.samplingLayer,0,chronological D remaining,i.val⟩]
def residual (D remaining : ℕ) (i : Index P) : Origin := [⟨.publicSampling,.samplingLayer,1,chronological D remaining,i.val⟩]

variable (hR : P.R ≤ 1/2) (hc : 0 < P.csch) (hsmall : P.csch < 1/160) (clock : ClockLaw.Clock)
local notation "c₀" => c P hR hc hsmall clock
local notation "p₀" => p P hR hc hsmall clock
local notation "e₀" => e P hR hc hsmall clock
local notation "C₀" => ClockPublicSetup.size P hR hc hsmall clock
local notation "table₀" => ClockPublicSetup.table P hR hc hsmall clock

def slots : Fin (tableSize P hR hc hsmall clock) → Fin C₀ :=
  ClockPublicSetup.oldSlot P hR hc hsmall clock ∘ ClockInitialLayer.oldSlot P hR hc hsmall clock
def rhoSlot : Fin C₀ := ClockPublicSetup.oldSlot P hR hc hsmall clock (ClockInitialLayer.rhoSlot P hR hc hsmall clock)
def auxiliary (D remaining : ℕ) (i : Index P) (j : Fin (g P hR hc hsmall clock i)) : Origin :=
  [⟨.publicSampling,.samplingLayer,j.val+2,chronological D remaining,i.val⟩]

theorem table_slots : table₀ ∘ slots P hR hc hsmall clock = table P hR hc hsmall clock := by
  funext i
  exact (ClockPublicSetup.table_old P hR hc hsmall clock _).trans (ClockInitialLayer.table_old P hR hc hsmall clock i)
theorem table_rho : table₀ (rhoSlot P hR hc hsmall clock) = rhoC P := ClockPublicSetup.table_rho P hR hc hsmall clock

abbrev Finish (τ : Ty) := ∀ {Δ : Ctx}, (Index P → Ref Δ .point) → (Index P → Ref Δ .point) → RefMap (entryCtx P) Δ → Prog C₀ Δ τ

def loop {τ : Ty} (D : ℕ) (finish : Finish P hR hc hsmall clock τ) : Prog C₀ (entryCtx P) τ :=
  iterateThen c₀ p₀ (slots P hR hc hsmall clock) e₀ (fun _ => []) (designated P D) (residual P D)
    (auxiliary P hR hc hsmall clock D) finish D (oldRef P) (directRef P) (fun r => r)

def initialized {τ : Ty} (ell D : ℕ) (finish : Finish P hR hc hsmall clock τ) : Prog C₀ (ClockPublicSetup.readyCtx P) τ :=
  initializeCenters (rhoSlot P hR hc hsmall clock) (ClockPublicSetup.directRef P) [] (ClockInitialLayer.initialOrigin P ell)
    (loop P hR hc hsmall clock D finish)

def code {τ : Ty} (ell D : ℕ) (finish : Finish P hR hc hsmall clock τ) : Program C₀ τ :=
  ClockPublicSetup.code P hR hc hsmall clock ell (initialized P hR hc hsmall clock ell D finish)

/-- The prescribed outer count is K+4, separate from the internal sourceLayers. -/
def prescribed {τ : Ty} (ell : ℕ) (finish : Finish P hR hc hsmall clock τ) : Program C₀ τ :=
  code P hR hc hsmall clock ell (P.K+4) finish

abbrev Data {τ : Ty} (D : ℕ) (finish : Finish P hR hc hsmall clock τ) (d : ℕ) :=
  Point d × ((Index P → Point d) × RawData c₀ p₀ finish d D (oldRef P) (directRef P) (fun r => r))

def targetEquiv {d : ℕ} {τ : Ty} (ell D : ℕ) (finish : Finish P hR hc hsmall clock τ) :
    Tape d (code P hR hc hsmall clock ell D finish) ≃ Data P hR hc hsmall clock D finish d :=
  (ClockPublicSetup.tapeEquiv P hR hc hsmall clock ell (initialized P hR hc hsmall clock ell D finish)).trans
    (Equiv.prodCongr (Equiv.refl _)
      ((initialTapeEquiv (rhoSlot P hR hc hsmall clock) (ClockPublicSetup.directRef P) [] (ClockInitialLayer.initialOrigin P ell)
        (loop P hR hc hsmall clock D finish)).trans
        (Equiv.prodCongr (Equiv.refl _)
          (rawTapeEquiv c₀ p₀ (slots P hR hc hsmall clock) e₀ (fun _ => []) (designated P D) (residual P D)
            (auxiliary P hR hc hsmall clock D) finish d D (oldRef P) (directRef P) (fun r => r)))))

theorem target_roundtrip {d : ℕ} {τ : Ty} (ell D : ℕ) (finish : Finish P hR hc hsmall clock τ)
    (tape : Tape d (code P hR hc hsmall clock ell D finish)) :
    (targetEquiv P hR hc hsmall clock ell D finish).symm (targetEquiv P hR hc hsmall clock ell D finish tape) = tape := Equiv.symm_apply_apply _ _

/-- Actual initialization at Ready, retaining all public setup values. -/
theorem run_initialized {d : ℕ} {τ : Ty} (ell D : ℕ) (finish : Finish P hR hc hsmall clock τ)
    (G : Point d → Point d) (xF momentum E0 : Point d) (Z0 : Index P → Point d)
    (tape : Tape d (loop P hR hc hsmall clock D finish)) :
    let input : Inputs d C₀ := ⟨table₀,xF,momentum⟩
    let tail := run (loop P hR hc hsmall clock D finish) G input (entryEnv P clock xF momentum E0 Z0) tape
    run (initialized P hR hc hsmall clock ell D finish) G input (ClockPublicSetup.readyEnv P clock xF momentum E0)
      (packInitialTape (rhoSlot P hR hc hsmall clock) (ClockPublicSetup.directRef P) [] (ClockInitialLayer.initialOrigin P ell)
        (loop P hR hc hsmall clock D finish) (Z0,tape)) =
      ⟨tail.value,ClockInitialLayer.initialTrace P d ell ++ tail.trace⟩ := by
  have hh := run_initialize (rhoSlot P hR hc hsmall clock) (ClockPublicSetup.directRef P) [] (ClockInitialLayer.initialOrigin P ell)
    (loop P hR hc hsmall clock D finish) G (⟨table₀,xF,momentum⟩ : Inputs d C₀) (ClockPublicSetup.readyEnv P clock xF momentum E0)
    (packInitialTape (rhoSlot P hR hc hsmall clock) (ClockPublicSetup.directRef P) [] (ClockInitialLayer.initialOrigin P ell)
      (loop P hR hc hsmall clock D finish) (Z0,tape))
  simp only [packInitialTape,ClockPublicSetup.ready_direct,table_rho,prefix_nil] at hh
  exact hh

/-- This is the existing finalState of the actual initialized loop tape. -/
def state {d : ℕ} {τ : Ty} (D : ℕ) (finish : Finish P hR hc hsmall clock τ) (G : Point d → Point d)
    (xF momentum : Point d) (data : Data P hR hc hsmall clock D finish d) : FinalState C₀ (N P) d (entryCtx P) τ finish :=
  finalState c₀ p₀ (slots P hR hc hsmall clock) e₀ (fun _ => []) (designated P D) (residual P D)
    (auxiliary P hR hc hsmall clock D) finish G ⟨table₀,xF,momentum⟩ D (oldRef P) (directRef P) (fun r => r)
    (entryEnv P clock xF momentum data.1 data.2.1)
    ((rawTapeEquiv c₀ p₀ (slots P hR hc hsmall clock) e₀ (fun _ => []) (designated P D) (residual P D)
      (auxiliary P hR hc hsmall clock D) finish d D (oldRef P) (directRef P) (fun r => r)).symm data.2.2)

def loopTrace {d : ℕ} {τ : Ty} (D : ℕ) (finish : Finish P hR hc hsmall clock τ) (G : Point d → Point d)
    (xF momentum : Point d) (data : Data P hR hc hsmall clock D finish d) : List (Event d) :=
  executionTrace c₀ p₀ (slots P hR hc hsmall clock) e₀ (fun _ => []) (designated P D) (residual P D)
    (auxiliary P hR hc hsmall clock D) finish G ⟨table₀,xF,momentum⟩ D (oldRef P) (directRef P) (fun r => r)
    (entryEnv P clock xF momentum data.1 data.2.1)
    ((rawTapeEquiv c₀ p₀ (slots P hR hc hsmall clock) e₀ (fun _ => []) (designated P D) (residual P D)
      (auxiliary P hR hc hsmall clock D) finish d D (oldRef P) (directRef P) (fun r => r)).symm data.2.2)

theorem run_packed {d : ℕ} {τ : Ty} (ell D : ℕ) (finish : Finish P hR hc hsmall clock τ)
    (G : Point d → Point d) (xF momentum : Point d) (data : Data P hR hc hsmall clock D finish d) :
    let st := state P hR hc hsmall clock D finish G xF momentum data
    let tail := run (finish st.old st.direct st.saved) G ⟨table₀,xF,momentum⟩ st.env st.tape
    run (code P hR hc hsmall clock ell D finish) G ⟨table₀,xF,momentum⟩ Env.empty
      ((targetEquiv P hR hc hsmall clock ell D finish).symm data) =
      ⟨tail.value,Event.gaussian (ClockPublicSetup.origin ell)::(ClockInitialLayer.initialTrace P d ell ++
        loopTrace P hR hc hsmall clock D finish G xF momentum data)⟩ := by
  let tape := (rawTapeEquiv c₀ p₀ (slots P hR hc hsmall clock) e₀ (fun _ => []) (designated P D) (residual P D)
    (auxiliary P hR hc hsmall clock D) finish d D (oldRef P) (directRef P) (fun r => r)).symm data.2.2
  have hl := run_iterateThen_result c₀ p₀ (slots P hR hc hsmall clock) e₀ (fun _ => []) (designated P D) (residual P D)
    (auxiliary P hR hc hsmall clock D) finish G (⟨table₀,xF,momentum⟩ : Inputs d C₀) D (oldRef P) (directRef P) (fun r => r)
    (entryEnv P clock xF momentum data.1 data.2.1) tape
  have hi := run_initialized P hR hc hsmall clock ell D finish G xF momentum data.1 data.2.1 tape
  have hp := ClockPublicSetup.run_packed P hR hc hsmall clock ell (initialized P hR hc hsmall clock ell D finish) G xF momentum data.1
    (packInitialTape (rhoSlot P hR hc hsmall clock) (ClockPublicSetup.directRef P) [] (ClockInitialLayer.initialOrigin P ell)
      (loop P hR hc hsmall clock D finish) (data.2.1,tape))
  dsimp only at hp hi hl ⊢
  rw [hi] at hp
  change run (loop P hR hc hsmall clock D finish) G _ _ tape = _ at hl
  rw [hl] at hp
  exact hp

theorem run_every_tape {d : ℕ} {τ : Ty} (ell D : ℕ) (finish : Finish P hR hc hsmall clock τ)
    (G : Point d → Point d) (xF momentum : Point d) (tape : Tape d (code P hR hc hsmall clock ell D finish)) :
    let data := targetEquiv P hR hc hsmall clock ell D finish tape
    let st := state P hR hc hsmall clock D finish G xF momentum data
    let tail := run (finish st.old st.direct st.saved) G ⟨table₀,xF,momentum⟩ st.env st.tape
    run (code P hR hc hsmall clock ell D finish) G ⟨table₀,xF,momentum⟩ Env.empty tape =
      ⟨tail.value,Event.gaussian (ClockPublicSetup.origin ell)::(ClockInitialLayer.initialTrace P d ell ++
        loopTrace P hR hc hsmall clock D finish G xF momentum data)⟩ := by
  have hh := run_packed P hR hc hsmall clock ell D finish G xF momentum (targetEquiv P hR hc hsmall clock ell D finish tape)
  rw [Equiv.symm_apply_apply] at hh
  exact hh

theorem state_saved {d : ℕ} {τ : Ty} (D : ℕ) (finish : Finish P hR hc hsmall clock τ)
    (G : Point d → Point d) (xF momentum : Point d) (data : Data P hR hc hsmall clock D finish d) (r : Ref (entryCtx P) .point) :
    let st := state P hR hc hsmall clock D finish G xF momentum data
    storedPoint st.env (st.saved r) = storedPoint (entryEnv P clock xF momentum data.1 data.2.1) r :=
  finalState_saved c₀ p₀ (slots P hR hc hsmall clock) e₀ (fun _ => []) (designated P D) (residual P D)
    (auxiliary P hR hc hsmall clock D) finish G ⟨table₀,xF,momentum⟩ D (oldRef P) (directRef P) (fun r => r)
    (entryEnv P clock xF momentum data.1 data.2.1) _ r

/-- Generic finish costs are paid in addition to setup and every layer. -/
theorem executed_counts {d : ℕ} {τ : Ty} (ell D : ℕ) (finish : Finish P hR hc hsmall clock τ)
    (kind : EventKind) (finalCount : ℕ)
    (hfinish : ∀ {Δ : Ctx} (old direct : Index P → Ref Δ .point) (saved : RefMap (entryCtx P) Δ), syntaxCount kind (finish old direct saved) = finalCount)
    (G : Point d → Point d) (input : Inputs d C₀) (tape : Tape d (code P hR hc hsmall clock ell D finish)) :
    shapeCount kind ((run (code P hR hc hsmall clock ell D finish) G input Env.empty tape).trace.map Event.erase) =
      (if kind=.gaussian then 1+N P else 0)+D*layerInventory kind c₀ p₀+finalCount := by
  rw [run_trace_shape,shapeCount_staticTrace]
  unfold code
  rw [ClockPublicSetup.syntaxCount_code]
  unfold initialized loop
  rw [syntaxCount_initialize,syntaxCount_iterateThen _ _ _ _ _ _ _ _ _ _ _ hfinish]
  cases kind <;> simp only [ite_true,ite_false,reduceCtorEq] <;> omega

def finishSaved (r : Ref (entryCtx P) .point) : Finish P hR hc hsmall clock .point := fun _ _ saved => .ret (saved r)

theorem finishSaved_count (kind : EventKind) (r : Ref (entryCtx P) .point) {Δ : Ctx}
    (old direct : Index P → Ref Δ .point) (saved : RefMap (entryCtx P) Δ) :
    syntaxCount kind (finishSaved P hR hc hsmall clock r old direct saved) = 0 := rfl

theorem state_direct {d : ℕ} {τ : Ty} (D : ℕ) (finish : Finish P hR hc hsmall clock τ)
    (G : Point d → Point d) (xF momentum : Point d) (data : Data P hR hc hsmall clock D finish d) (j : Index P) :
    let st := state P hR hc hsmall clock D finish G xF momentum data
    storedPoint st.env (st.direct j) = b P clock xF (ClockPublicSetup.splitValues momentum data.1 0) j :=
  (finalState_direct c₀ p₀ (slots P hR hc hsmall clock) e₀ (fun _ => []) (designated P D) (residual P D)
    (auxiliary P hR hc hsmall clock D) finish G ⟨table₀,xF,momentum⟩ D (oldRef P) (directRef P) (fun r => r)
    (entryEnv P clock xF momentum data.1 data.2.1) _ j).trans (entry_direct P clock xF momentum data.1 data.2.1 j)

theorem state_momentum {d : ℕ} {τ : Ty} (D : ℕ) (finish : Finish P hR hc hsmall clock τ)
    (G : Point d → Point d) (xF momentum : Point d) (data : Data P hR hc hsmall clock D finish d) :
    let st := state P hR hc hsmall clock D finish G xF momentum data
    storedPoint st.env (st.saved (momentumRef P)) = momentum :=
  (state_saved P hR hc hsmall clock D finish G xF momentum data (momentumRef P)).trans
    (entry_momentum P clock xF momentum data.1 data.2.1)

/-- The exact fixed main-mean family at each reached local context. -/
theorem run_layer_step {d : ℕ} {τ : Ty} (D depth : ℕ) (finish : Finish P hR hc hsmall clock τ)
    {Γ : Ctx} (old direct : Index P → Ref Γ .point) (saved : RefMap (entryCtx P) Γ) (env : Env d Γ)
    (G : Point d → Point d) (xF momentum : Point d)
    (data : RawData c₀ p₀ finish d (depth+1) old direct saved) :
    let input : Inputs d C₀ := ⟨table₀,xF,momentum⟩
    let src := fun i => run (p₀ i) G ⟨coeff P hR hc hsmall clock i,storedPoint env (old i),(data.1.1 i).1⟩ Env.empty
      (transformedSourceTape (p₀ i) (e₀ i) (T P hR hc hsmall clock i) (data.1.1 i).2.1 (data.1.1 i).2.2)
    let Q : Index P → Point d := fun i => (src i).value
    let X := fun j => storedPoint env (direct j)+(∑ i, A P clock j i • Q i)+∑ k, C P clock j k • data.1.2 k
    let tail := run (iterateThen c₀ p₀ (slots P hR hc hsmall clock) e₀ (fun _ => []) (designated P D) (residual P D)
      (auxiliary P hR hc hsmall clock D) finish depth batchRef (fun j => preserveDirect (direct j)) (fun r => preserveDirect (saved r)))
      G input (Env.prepend X (Env.prepend data.1.2 (Env.prepend Q env)))
      ((rawTapeEquiv c₀ p₀ (slots P hR hc hsmall clock) e₀ (fun _ => []) (designated P D) (residual P D)
        (auxiliary P hR hc hsmall clock D) finish d depth batchRef (fun j => preserveDirect (direct j)) (fun r => preserveDirect (saved r))).symm data.2)
    run (iterateThen c₀ p₀ (slots P hR hc hsmall clock) e₀ (fun _ => []) (designated P D) (residual P D)
      (auxiliary P hR hc hsmall clock D) finish (depth+1) old direct saved) G input env
      ((rawTapeEquiv c₀ p₀ (slots P hR hc hsmall clock) e₀ (fun _ => []) (designated P D) (residual P D)
        (auxiliary P hR hc hsmall clock D) finish d (depth+1) old direct saved).symm data) =
      ⟨tail.value,(List.ofFn (fun i => [Event.gaussian (designated P D depth i)] ++
        List.ofFn (fun j => Event.gaussian (auxiliary P hR hc hsmall clock D depth i j)) ++ (src i).trace.filter keepNonGaussian)).flatten ++
        List.ofFn (fun i => Event.gaussian (residual P D depth i)) ++ tail.trace⟩ := by
  simpa only [prefix_nil] using run_raw_succ c₀ p₀ (slots P hR hc hsmall clock) e₀ (fun _ => []) (designated P D) (residual P D)
    (auxiliary P hR hc hsmall clock D) finish (A P clock) (C P clock) (T P hR hc hsmall clock) (coeff P hR hc hsmall clock)
    G (⟨table₀,xF,momentum⟩ : Inputs d C₀) (table_slots P hR hc hsmall clock) depth old direct saved env data

theorem finishSaved_counts {d : ℕ} (ell D : ℕ) (r : Ref (entryCtx P) .point)
    (G : Point d → Point d) (input : Inputs d C₀) (tape : Tape d (code P hR hc hsmall clock ell D (finishSaved P hR hc hsmall clock r))) :
    let events := (run (code P hR hc hsmall clock ell D (finishSaved P hR hc hsmall clock r)) G input Env.empty tape).trace.map Event.erase
    shapeCount .gaussian events = 1+N P+D*(2*N P+∑ i, g P hR hc hsmall clock i) ∧
    shapeCount .gradient events = D*(∑ i,syntaxCount .gradient (p₀ i)) ∧
    shapeCount .uniform events = D*(∑ i,syntaxCount .uniform (p₀ i)) := by
  have hh (kind : EventKind) := executed_counts P hR hc hsmall clock ell D (finishSaved P hR hc hsmall clock r) kind 0
    (fun _ _ _ => rfl) G input tape
  have hn : N P+(∑ i,g P hR hc hsmall clock i)+N P = 2*N P+∑ i,g P hR hc hsmall clock i := by omega
  refine ⟨?_,?_,?_⟩
  · simpa only [layerInventory,ite_true,Nat.add_zero,hn] using hh .gaussian
  · simpa only [layerInventory,reduceCtorEq,ite_false,Nat.add_zero,Nat.zero_add] using hh .gradient
  · simpa only [layerInventory,reduceCtorEq,ite_false,Nat.add_zero,Nat.zero_add] using hh .uniform

theorem prescribed_counts {d : ℕ} (ell : ℕ) (r : Ref (entryCtx P) .point)
    (G : Point d → Point d) (input : Inputs d C₀) (tape : Tape d (prescribed P hR hc hsmall clock ell (finishSaved P hR hc hsmall clock r))) :
    let events := (run (prescribed P hR hc hsmall clock ell (finishSaved P hR hc hsmall clock r)) G input Env.empty tape).trace.map Event.erase
    shapeCount .gaussian events = 1+N P+(P.K+4)*(2*N P+∑ i, g P hR hc hsmall clock i) ∧
    shapeCount .gradient events = (P.K+4)*(∑ i,syntaxCount .gradient (p₀ i)) ∧
    shapeCount .uniform events = (P.K+4)*(∑ i,syntaxCount .uniform (p₀ i)) :=
  finishSaved_counts P hR hc hsmall clock ell (P.K+4) r G input tape

end AcceleratedLogConcave.Root.ClockRepeatedLayers
