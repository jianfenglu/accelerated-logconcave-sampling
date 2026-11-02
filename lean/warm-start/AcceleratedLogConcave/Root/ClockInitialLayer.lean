import AcceleratedLogConcave.Root.ClockNoisyLayerRun
import AcceleratedLogConcave.Oracle.SourceMeanLayerTape

/-! Literal-b initialization followed by one routed outer layer. The starting
store already contains b; public momentum/setup and the full loop are absent. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Root.ClockInitialLayer
open Oracle Oracle.TapeLowering Oracle.AffineLowering Oracle.NoisyLayer Oracle.SourceMeanLayer
open ClockNoisyLayer
open scoped BigOperators
variable (P : SourceSchedule)
abbrev baseCtx : Ctx := replyCtx (N P) []
abbrev initialCtx : Ctx := replyCtx (N P) (replyCtx (N P) (baseCtx P))
abbrev finalCtx : Ctx := nextCtx (N P) (initialCtx P)
def baseDirect (i : Index P) : Ref (baseCtx P) .point := batchRef i
def oldRef (i : Index P) : Ref (initialCtx P) .point := batchRef i
/-- Both the X0 and Z0 batches must be skipped to recover literal b. -/
def directRef (i : Index P) : Ref (initialCtx P) .point := RefMap.shiftMany (N P) (RefMap.shiftMany (N P) (batchRef i))
def baseEnv {d : ℕ} (clock : ClockLaw.Clock) (xF Y0 : Point d) : Env d (baseCtx P) :=
  Env.prepend (b P clock xF Y0) Env.empty
def initialValues {d : ℕ} (clock : ClockLaw.Clock) (xF Y0 : Point d) (Z0 : Index P → Point d) : Index P → Point d :=
  fun i => b P clock xF Y0 i+rhoC P • Z0 i
def initialEnv {d : ℕ} (clock : ClockLaw.Clock) (xF Y0 : Point d) (Z0 : Index P → Point d) : Env d (initialCtx P) :=
  Env.prepend (initialValues P clock xF Y0 Z0) (Env.prepend Z0 (baseEnv P clock xF Y0))
def initialOrigin (ell : ℕ) (i : Index P) : Origin := [⟨.publicSampling,.setup,0,ell,i.val⟩]
def initialTrace (d ell : ℕ) : List (Event d) := List.ofFn (fun i => Event.gaussian (initialOrigin P ell i))

theorem base_lookup {d : ℕ} (clock : ClockLaw.Clock) (xF Y0 : Point d) (i : Index P) :
    storedPoint (baseEnv P clock xF Y0) (baseDirect P i) = b P clock xF Y0 i := prepend_batchRef _ _ _
theorem initial_old {d : ℕ} (clock : ClockLaw.Clock) (xF Y0 : Point d) (Z0 : Index P → Point d) (i : Index P) :
    storedPoint (initialEnv P clock xF Y0 Z0) (oldRef P i) = initialValues P clock xF Y0 Z0 i := prepend_batchRef _ _ _
theorem initial_direct {d : ℕ} (clock : ClockLaw.Clock) (xF Y0 : Point d) (Z0 : Index P → Point d) (i : Index P) :
    storedPoint (initialEnv P clock xF Y0 Z0) (directRef P i) = b P clock xF Y0 i := by
  change Env.prepend _ (Env.prepend _ (baseEnv P clock xF Y0))
    (RefMap.shiftMany (N P) (RefMap.shiftMany (N P) (batchRef i))) = _
  rw [prepend_shiftMany,prepend_shiftMany]
  exact prepend_batchRef _ _ _

variable (hR : P.R ≤ 1/2) (hc : 0 < P.csch) (hsmall : P.csch < 1/160) (clock : ClockLaw.Clock)
local notation "c₀" => c P hR hc hsmall clock
local notation "p₀" => p P hR hc hsmall clock
local notation "e₀" => e P hR hc hsmall clock
local notation "T₀" => T P hR hc hsmall clock
local notation "coeff₀" => coeff P hR hc hsmall clock
local notation "L" => tableSize P hR hc hsmall clock
abbrev extendedSize : ℕ := L+1
def oldSlot (i : Fin L) : Fin (extendedSize P hR hc hsmall clock) := Fin.castAdd 1 i
def rhoSlot : Fin (extendedSize P hR hc hsmall clock) := Fin.natAdd L (0 : Fin 1)
def extendedTable : Fin (extendedSize P hR hc hsmall clock) → ℝ :=
  Fin.append (table P hR hc hsmall clock) (fun _ : Fin 1 => rhoC P)

theorem table_old (i : Fin L) : extendedTable P hR hc hsmall clock (oldSlot P hR hc hsmall clock i) = table P hR hc hsmall clock i := by
  simp only [extendedTable,oldSlot,Fin.append_left]
theorem table_rho : extendedTable P hR hc hsmall clock (rhoSlot P hR hc hsmall clock) = rhoC P := by
  simp only [extendedTable,rhoSlot,Fin.append_right]
theorem oldSlot_injective : Function.Injective (oldSlot P hR hc hsmall clock) := by
  intro i j h
  exact Fin.ext (congrArg (fun z : Fin (extendedSize P hR hc hsmall clock) => z.val) h)
theorem oldSlot_ne_rho (i : Fin L) : oldSlot P hR hc hsmall clock i ≠ rhoSlot P hR hc hsmall clock := by
  intro h
  have hv := congrArg Fin.val h
  change i.val = L+0 at hv
  have := i.isLt
  omega
theorem table_restrict : extendedTable P hR hc hsmall clock ∘ oldSlot P hR hc hsmall clock = table P hR hc hsmall clock :=
  funext (table_old P hR hc hsmall clock)
theorem child_table_unchanged (i : Index P) (k : Fin (childSize (p₀ i))) :
    extendedTable P hR hc hsmall clock (oldSlot P hR hc hsmall clock (childSlot c₀ p₀ i k)) = matrixTable (T₀ i) (coeff₀ i) k :=
  (table_old P hR hc hsmall clock _).trans (table_child P hR hc hsmall clock i k)
theorem original_coefficient_unchanged (i : Index P) (k : Fin (c₀ i)) :
    extendedTable P hR hc hsmall clock (oldSlot P hR hc hsmall clock (childSlot c₀ p₀ i
      (Fin.natAdd (g P hR hc hsmall clock i*g P hR hc hsmall clock i) k))) = coeff₀ i k :=
  (table_old P hR hc hsmall clock _).trans (table_original P hR hc hsmall clock i k)

def routed {τ : Ty} (ell : ℕ) (next : Prog (extendedSize P hR hc hsmall clock) (finalCtx P) τ) :
    Prog (extendedSize P hR hc hsmall clock) (initialCtx P) τ :=
  layerAt c₀ p₀ (oldSlot P hR hc hsmall clock) e₀ (oldRef P) (directRef P) (outerOrigin ell)
    (designated P ell) (residual P ell) (auxiliary P hR hc hsmall clock ell) next

/-- Empty initial outer prefix leaves the entire following layer untagged as setup. -/
def initialized {τ : Ty} (ell : ℕ) (next : Prog (extendedSize P hR hc hsmall clock) (finalCtx P) τ) :
    Prog (extendedSize P hR hc hsmall clock) (baseCtx P) τ :=
  initializeCenters (rhoSlot P hR hc hsmall clock) (baseDirect P) [] (initialOrigin P ell)
    (routed P hR hc hsmall clock ell next)

abbrev Data {τ : Ty} (next : Prog (extendedSize P hR hc hsmall clock) (finalCtx P) τ) (d : ℕ) :=
  (Index P → Point d) × LayerAtData c₀ p₀ next d

def targetEquiv {d : ℕ} {τ : Ty} (ell : ℕ) (next : Prog (extendedSize P hR hc hsmall clock) (finalCtx P) τ) :
    Tape d (initialized P hR hc hsmall clock ell next) ≃ Data P hR hc hsmall clock next d :=
  (initialTapeEquiv (rhoSlot P hR hc hsmall clock) (baseDirect P) [] (initialOrigin P ell)
    (routed P hR hc hsmall clock ell next)).trans
      (Equiv.prodCongr (Equiv.refl _) (layerAtTapeEquiv c₀ p₀ (oldSlot P hR hc hsmall clock) e₀ (oldRef P) (directRef P)
        (outerOrigin ell) (designated P ell) (residual P ell) (auxiliary P hR hc hsmall clock ell) next))

theorem target_roundtrip {d : ℕ} {τ : Ty} (ell : ℕ) (next : Prog (extendedSize P hR hc hsmall clock) (finalCtx P) τ)
    (tape : Tape d (initialized P hR hc hsmall clock ell next)) :
    (targetEquiv P hR hc hsmall clock ell next).symm (targetEquiv P hR hc hsmall clock ell next tape) = tape :=
  Equiv.symm_apply_apply _ _

def finalEnv {d : ℕ} (xF Y0 : Point d) (Z0 Q Z1 : Index P → Point d) : Env d (finalCtx P) :=
  Env.prepend (updated P clock xF Y0 Q Z1) (Env.prepend Z1 (Env.prepend Q (initialEnv P clock xF Y0 Z0)))

theorem all_new_centers {d : ℕ} (xF Y0 : Point d) (Z0 Q Z1 : Index P → Point d) (i : Index P) :
    storedPoint (finalEnv P clock xF Y0 Z0 Q Z1) (batchRef i) = updated P clock xF Y0 Q Z1 i := prepend_batchRef _ _ _

theorem run_routed_packed {d : ℕ} {τ : Ty} (ell : ℕ) (next : Prog (extendedSize P hR hc hsmall clock) (finalCtx P) τ)
    (G : Point d → Point d) (hostX hostP xF Y0 : Point d) (Z0 : Index P → Point d) (data : LayerAtData c₀ p₀ next d) :
    let input : Inputs d (extendedSize P hR hc hsmall clock) := ⟨extendedTable P hR hc hsmall clock,hostX,hostP⟩
    let src := sources P hR hc hsmall clock G (initialValues P clock xF Y0 Z0) data.1
    let tail := run next G input (finalEnv P clock xF Y0 Z0 (fun i => (src i).value) data.2.1) data.2.2
    run (routed P hR hc hsmall clock ell next) G input (initialEnv P clock xF Y0 Z0)
      (packLayerAtTape c₀ p₀ (oldSlot P hR hc hsmall clock) e₀ (oldRef P) (directRef P)
        (outerOrigin ell) (designated P ell) (residual P ell) (auxiliary P hR hc hsmall clock ell) next data) =
      ⟨tail.value,fullTrace P hR hc hsmall clock ell src tail.trace⟩ := by
  have hh := run_layerAt_packed c₀ p₀ (oldSlot P hR hc hsmall clock) e₀ (oldRef P) (directRef P)
    (outerOrigin ell) (designated P ell) (residual P ell) (auxiliary P hR hc hsmall clock ell) next
    (A P clock) (C P clock) T₀ coeff₀ G ⟨extendedTable P hR hc hsmall clock,hostX,hostP⟩
    (initialEnv P clock xF Y0 Z0) (table_restrict P hR hc hsmall clock) data
  simp only [initial_old,initial_direct] at hh
  exact hh

theorem run_initial_prefix {d : ℕ} {τ : Ty} (ell : ℕ) (next : Prog (extendedSize P hR hc hsmall clock) (finalCtx P) τ)
    (G : Point d → Point d) (hostX hostP xF Y0 : Point d) (Z0 : Index P → Point d)
    (tape : Tape d (routed P hR hc hsmall clock ell next)) :
    let input : Inputs d (extendedSize P hR hc hsmall clock) := ⟨extendedTable P hR hc hsmall clock,hostX,hostP⟩
    let tail := run (routed P hR hc hsmall clock ell next) G input (initialEnv P clock xF Y0 Z0) tape
    run (initialized P hR hc hsmall clock ell next) G input (baseEnv P clock xF Y0)
      (packInitialTape (rhoSlot P hR hc hsmall clock) (baseDirect P) [] (initialOrigin P ell)
        (routed P hR hc hsmall clock ell next) ⟨Z0,tape⟩) =
      ⟨tail.value, initialTrace P d ell ++ tail.trace⟩ := by
  have hh := run_initialize (rhoSlot P hR hc hsmall clock) (baseDirect P) [] (initialOrigin P ell)
    (routed P hR hc hsmall clock ell next) G ⟨extendedTable P hR hc hsmall clock,hostX,hostP⟩
    (baseEnv P clock xF Y0) (packInitialTape (rhoSlot P hR hc hsmall clock) (baseDirect P) [] (initialOrigin P ell)
      (routed P hR hc hsmall clock ell next) ⟨Z0,tape⟩)
  simp only [packInitialTape,base_lookup,table_rho,prefix_nil] at hh
  exact hh

/-- All six center/noise/reply batches are passed to the actual continuation. -/
theorem run_initialized_packed {d : ℕ} {τ : Ty} (ell : ℕ) (next : Prog (extendedSize P hR hc hsmall clock) (finalCtx P) τ)
    (G : Point d → Point d) (hostX hostP xF Y0 : Point d) (data : Data P hR hc hsmall clock next d) :
    let input : Inputs d (extendedSize P hR hc hsmall clock) := ⟨extendedTable P hR hc hsmall clock,hostX,hostP⟩
    let src := sources P hR hc hsmall clock G (initialValues P clock xF Y0 data.1) data.2.1
    let tail := run next G input (finalEnv P clock xF Y0 data.1 (fun i => (src i).value) data.2.2.1) data.2.2.2
    run (initialized P hR hc hsmall clock ell next) G input (baseEnv P clock xF Y0)
      ((targetEquiv P hR hc hsmall clock ell next).symm data) =
      ⟨tail.value,initialTrace P d ell ++ fullTrace P hR hc hsmall clock ell src tail.trace⟩ := by
  have hh := run_initial_prefix P hR hc hsmall clock ell next G hostX hostP xF Y0 data.1
    (packLayerAtTape c₀ p₀ (oldSlot P hR hc hsmall clock) e₀ (oldRef P) (directRef P)
      (outerOrigin ell) (designated P ell) (residual P ell) (auxiliary P hR hc hsmall clock ell) next data.2)
  dsimp only at hh
  erw [run_routed_packed] at hh
  exact hh

theorem run_initialized_every_tape {d : ℕ} {τ : Ty} (ell : ℕ) (next : Prog (extendedSize P hR hc hsmall clock) (finalCtx P) τ)
    (G : Point d → Point d) (hostX hostP xF Y0 : Point d) (tape : Tape d (initialized P hR hc hsmall clock ell next)) :
    let data := targetEquiv P hR hc hsmall clock ell next tape
    let input : Inputs d (extendedSize P hR hc hsmall clock) := ⟨extendedTable P hR hc hsmall clock,hostX,hostP⟩
    let src := sources P hR hc hsmall clock G (initialValues P clock xF Y0 data.1) data.2.1
    let tail := run next G input (finalEnv P clock xF Y0 data.1 (fun i => (src i).value) data.2.2.1) data.2.2.2
    run (initialized P hR hc hsmall clock ell next) G input (baseEnv P clock xF Y0) tape =
      ⟨tail.value,initialTrace P d ell ++ fullTrace P hR hc hsmall clock ell src tail.trace⟩ := by
  have hh := run_initialized_packed P hR hc hsmall clock ell next G hostX hostP xF Y0
    (targetEquiv P hR hc hsmall clock ell next tape)
  erw [Equiv.symm_apply_apply] at hh
  exact hh

def selectRow (j : Index P) : Prog (extendedSize P hR hc hsmall clock) (finalCtx P) .point := .ret (batchRef j)
def rowProgram (ell : ℕ) (j : Index P) : Prog (extendedSize P hR hc hsmall clock) (baseCtx P) .point :=
  initialized P hR hc hsmall clock ell (selectRow P hR hc hsmall clock j)

theorem run_selectRow {d : ℕ} (j : Index P) (G : Point d → Point d) (input : Inputs d (extendedSize P hR hc hsmall clock))
    (xF Y0 : Point d) (Z0 Q Z1 : Index P → Point d) (tape : Tape d (selectRow P hR hc hsmall clock j)) :
    run (selectRow P hR hc hsmall clock j) G input (finalEnv P clock xF Y0 Z0 Q Z1) tape =
      pointResult (updated P clock xF Y0 Q Z1 j) [] := by
  change pointResult (storedPoint (finalEnv P clock xF Y0 Z0 Q Z1) (batchRef j)) [] = _
  rw [all_new_centers]

theorem run_row_every_tape {d : ℕ} (ell : ℕ) (j : Index P) (G : Point d → Point d)
    (hostX hostP xF Y0 : Point d) (tape : Tape d (rowProgram P hR hc hsmall clock ell j)) :
    let data := targetEquiv P hR hc hsmall clock ell (selectRow P hR hc hsmall clock j) tape
    let src := sources P hR hc hsmall clock G (initialValues P clock xF Y0 data.1) data.2.1
    run (rowProgram P hR hc hsmall clock ell j) G ⟨extendedTable P hR hc hsmall clock,hostX,hostP⟩
      (baseEnv P clock xF Y0) tape =
      ⟨updated P clock xF Y0 (fun i => (src i).value) data.2.2.1 j,
        initialTrace P d ell ++ fullTrace P hR hc hsmall clock ell src []⟩ := by
  have hh := run_initialized_every_tape P hR hc hsmall clock ell (selectRow P hR hc hsmall clock j) G hostX hostP xF Y0 tape
  dsimp only at hh
  erw [run_selectRow P hR hc hsmall clock j G ⟨extendedTable P hR hc hsmall clock,hostX,hostP⟩ xF Y0] at hh
  exact hh

theorem executed_counts {d : ℕ} {τ : Ty} (ell : ℕ) (next : Prog (extendedSize P hR hc hsmall clock) (finalCtx P) τ)
    (kind : EventKind) (G : Point d → Point d) (input : Inputs d (extendedSize P hR hc hsmall clock)) (env : Env d (baseCtx P))
    (tape : Tape d (initialized P hR hc hsmall clock ell next)) :
    shapeCount kind ((run (initialized P hR hc hsmall clock ell next) G input env tape).trace.map Event.erase) =
      (if kind = .gaussian then 3*N P+∑ i, g P hR hc hsmall clock i else ∑ i, syntaxCount kind (p₀ i)) + syntaxCount kind next := by
  rw [run_trace_shape,shapeCount_staticTrace]
  unfold initialized routed
  rw [syntaxCount_initialize,syntaxCount_layerAt]
  cases kind with
  | gaussian =>
    change N P+((N P+(∑ i, g P hR hc hsmall clock i)+N P)+syntaxCount .gaussian next) =
      (3*N P+∑ i, g P hR hc hsmall clock i)+syntaxCount .gaussian next
    omega
  | gradient =>
    have hk : EventKind.gradient ≠ .gaussian := by decide
    simp only [hk,ite_false,Nat.zero_add]
  | uniform =>
    have hk : EventKind.uniform ≠ .gaussian := by decide
    simp only [hk,ite_false,Nat.zero_add]

theorem executed_row_counts {d : ℕ} (ell : ℕ) (j : Index P) (kind : EventKind) (G : Point d → Point d)
    (input : Inputs d (extendedSize P hR hc hsmall clock)) (env : Env d (baseCtx P))
    (tape : Tape d (rowProgram P hR hc hsmall clock ell j)) :
    shapeCount kind ((run (rowProgram P hR hc hsmall clock ell j) G input env tape).trace.map Event.erase) =
      if kind = .gaussian then 3*N P+∑ i, g P hR hc hsmall clock i else ∑ i, syntaxCount kind (p₀ i) := by
  simpa only [rowProgram,selectRow,syntaxCount,Nat.add_zero] using
    executed_counts P hR hc hsmall clock ell (selectRow P hR hc hsmall clock j) kind G input env tape
end AcceleratedLogConcave.Root.ClockInitialLayer
