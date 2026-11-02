import AcceleratedLogConcave.Root.ClockInitialLayer
import AcceleratedLogConcave.Oracle.MeanExecutablePrefix
import AcceleratedLogConcave.Kinetic.MomentumSplit

/-! Public retained momentum split and direct-center prefix. The input center is
already normalized. The continuation is arbitrary and keeps every setup value. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Root.ClockPublicSetup
open Oracle Oracle.AffineLowering Oracle.NoisyLayer Oracle.MeanExecutablePrefix
open ClockNoisyLayer
open scoped BigOperators

def s : ℝ := 1/2
def noise : ℝ := Real.sqrt 3/2
def splitValues {d : ℕ} (momentum E0 : Point d) : Fin 2 → Point d :=
  ![s • momentum + noise • E0, noise • momentum + (-s) • E0]

theorem split_eq_gaussianSplit {d : ℕ} (momentum E0 : Point d) :
    (splitValues momentum E0 0, splitValues momentum E0 1) =
      Kinetic.gaussianSplit s noise (momentum,E0) := rfl

abbrev rawCtx : Ctx := [.point,.point,.point]
abbrev splitCtx : Ctx := replyCtx 2 rawCtx
abbrev readyCtx (P : SourceSchedule) : Ctx := replyCtx (N P) splitCtx

def rawEnv {d : ℕ} (xF momentum E0 : Point d) : Env d rawCtx :=
  Env.cons (d := d) (τ := .point) E0 (Env.cons (d := d) (τ := .point) momentum (Env.cons (d := d) (τ := .point) xF Env.empty))
def splitEnv {d : ℕ} (xF momentum E0 : Point d) : Env d splitCtx :=
  Env.prepend (splitValues momentum E0) (rawEnv xF momentum E0)
def readyEnv (P : SourceSchedule) {d : ℕ} (clock : ClockLaw.Clock) (xF momentum E0 : Point d) : Env d (readyCtx P) :=
  Env.prepend (b P clock xF (splitValues momentum E0 0)) (splitEnv xF momentum E0)

def yRef : Ref splitCtx .point := .here
def hRef : Ref splitCtx .point := .there .here
def eRef : Ref splitCtx .point := .there (.there .here)
def pRef : Ref splitCtx .point := .there (.there (.there .here))
def xRef : Ref splitCtx .point := .there (.there (.there (.there .here)))
def directRef (P : SourceSchedule) (i : Index P) : Ref (readyCtx P) .point := batchRef i
def saved (P : SourceSchedule) : RefMap splitCtx (readyCtx P) := RefMap.shiftMany (N P)

theorem split_y {d : ℕ} (xF momentum E0 : Point d) : storedPoint (splitEnv xF momentum E0) yRef = splitValues momentum E0 0 := rfl
theorem split_h {d : ℕ} (xF momentum E0 : Point d) : storedPoint (splitEnv xF momentum E0) hRef = splitValues momentum E0 1 := rfl
theorem split_e {d : ℕ} (xF momentum E0 : Point d) : storedPoint (splitEnv xF momentum E0) eRef = E0 := rfl
theorem split_p {d : ℕ} (xF momentum E0 : Point d) : storedPoint (splitEnv xF momentum E0) pRef = momentum := rfl
theorem split_x {d : ℕ} (xF momentum E0 : Point d) : storedPoint (splitEnv xF momentum E0) xRef = xF := rfl

theorem ready_direct (P : SourceSchedule) {d : ℕ} (clock : ClockLaw.Clock) (xF momentum E0 : Point d) (i : Index P) :
    storedPoint (readyEnv P clock xF momentum E0) (directRef P i) = b P clock xF (splitValues momentum E0 0) i := prepend_batchRef _ _ _
theorem ready_saved (P : SourceSchedule) {d : ℕ} (clock : ClockLaw.Clock) (xF momentum E0 : Point d) (r : Ref splitCtx .point) :
    storedPoint (readyEnv P clock xF momentum E0) (saved P r) = storedPoint (splitEnv xF momentum E0) r := prepend_shiftMany _ _ _

def origin (ell : ℕ) : Origin := [⟨.publicSampling,.setup,1,ell,0⟩]

theorem origin_ne_initial (P : SourceSchedule) (ell k : ℕ) (i : Index P) :
    origin ell ≠ ClockInitialLayer.initialOrigin P k i := by
  simp [origin,ClockInitialLayer.initialOrigin]

private theorem castAdd_ne_natAdd {a b : ℕ} (i : Fin a) (j : Fin b) :
    Fin.castAdd b i ≠ Fin.natAdd a j := by
  intro h
  have hv := congrArg (fun k : Fin (a+b) => k.val) h
  change i.val = a+j.val at hv
  omega

variable (P : SourceSchedule) (hR : P.R ≤ 1/2) (hc : 0 < P.csch) (hsmall : P.csch < 1/160) (clock : ClockLaw.Clock)
local notation "L" => ClockInitialLayer.extendedSize P hR hc hsmall clock
abbrev size : ℕ := L+(N P+3)
def oldSlot (i : Fin L) : Fin (size P hR hc hsmall clock) := Fin.castAdd (N P+3) i
def slopeSlot (i : Index P) : Fin (size P hR hc hsmall clock) := Fin.natAdd L (Fin.castAdd 3 i)
def sharedSlot (i : Fin 3) : Fin (size P hR hc hsmall clock) := Fin.natAdd L (Fin.natAdd (N P) i)
def slopes (i : Index P) : ℝ := ClockCollocation.rF P.delta * ClockCollocation.u P.delta P.K clock i
def table : Fin (size P hR hc hsmall clock) → ℝ :=
  Fin.append (ClockInitialLayer.extendedTable P hR hc hsmall clock)
    (Fin.append (slopes P clock) ![s,noise,-s])

theorem table_old (i : Fin L) : table P hR hc hsmall clock (oldSlot P hR hc hsmall clock i) =
    ClockInitialLayer.extendedTable P hR hc hsmall clock i := by simp [table,oldSlot]
theorem table_slope (i : Index P) : table P hR hc hsmall clock (slopeSlot P hR hc hsmall clock i) = slopes P clock i := by simp [table,slopeSlot]
theorem table_shared (i : Fin 3) : table P hR hc hsmall clock (sharedSlot P hR hc hsmall clock i) = ![s,noise,-s] i := by simp [table,sharedSlot]
theorem table_restrict : table P hR hc hsmall clock ∘ oldSlot P hR hc hsmall clock = ClockInitialLayer.extendedTable P hR hc hsmall clock := funext (table_old P hR hc hsmall clock)
theorem oldSlot_injective : Function.Injective (oldSlot P hR hc hsmall clock) := Fin.castAdd_injective _ _
theorem oldSlot_ne_slope (i : Fin L) (j : Index P) : oldSlot P hR hc hsmall clock i ≠ slopeSlot P hR hc hsmall clock j := by
  exact castAdd_ne_natAdd i (Fin.castAdd 3 j)
theorem oldSlot_ne_shared (i : Fin L) (j : Fin 3) : oldSlot P hR hc hsmall clock i ≠ sharedSlot P hR hc hsmall clock j := by
  exact castAdd_ne_natAdd i (Fin.natAdd (N P) j)
theorem table_rho : table P hR hc hsmall clock (oldSlot P hR hc hsmall clock (ClockInitialLayer.rhoSlot P hR hc hsmall clock)) = rhoC P := by
  rw [table_old,ClockInitialLayer.table_rho]

def splitSlots (j : Fin 2) : Fin (1*1+1) → Fin (size P hR hc hsmall clock) :=
  if j=0 then ![sharedSlot P hR hc hsmall clock 1,sharedSlot P hR hc hsmall clock 0]
  else ![sharedSlot P hR hc hsmall clock 2,sharedSlot P hR hc hsmall clock 1]
def splitRow (j : Fin 2) : Prog (size P hR hc hsmall clock) rawCtx .point :=
  MeanGaussianSetup.row (splitSlots P hR hc hsmall clock j) (Γ := [.point,.point]) .here 0

def directRow (i : Index P) : Prog (size P hR hc hsmall clock) splitCtx .point :=
  affineRow [] xRef [(slopeSlot P hR hc hsmall clock i,yRef)]

def code {τ : Ty} (ell : ℕ) (next : Prog (size P hR hc hsmall clock) (readyCtx P) τ) : Program (size P hR hc hsmall clock) τ :=
  .step [] .center (.step [] .momentum (.step (origin ell) .gaussian
    (.batch [] (splitRow P hR hc hsmall clock) (.batch [] (directRow P hR hc hsmall clock) next))))

theorem run_splitRow {d : ℕ} (j : Fin 2) (G : Point d → Point d) (xF momentum E0 : Point d)
    (tape : Tape d (splitRow P hR hc hsmall clock j)) :
    run (splitRow P hR hc hsmall clock j) G ⟨table P hR hc hsmall clock,xF,momentum⟩ (rawEnv xF momentum E0) tape =
      pointResult (splitValues momentum E0 j) [] := by
  have hh := run_assemblyRow (splitSlots P hR hc hsmall clock j) (Γ := [.point,.point]) .here 0 G
    (⟨table P hR hc hsmall clock,xF,momentum⟩ : Inputs d (size P hR hc hsmall clock))
    (Env.cons (d := d) (τ := .point) momentum (Env.cons (d := d) (τ := .point) xF Env.empty)) (fun _ : Fin 1 => E0) tape
  have hp : storedPoint (Env.cons (d := d) (τ := .point) momentum (Env.cons (d := d) (τ := .point) xF Env.empty))
      (.here : Ref [.point,.point] .point) = momentum := rfl
  rw [hp] at hh
  have hm : matrixIndex 1 (0 : Fin 1) 0 = (0 : Fin 2) := rfl
  fin_cases j <;> simpa [splitRow,assemblyValues,splitSlots,splitValues,table_shared,hm,storedPoint,rawEnv,Env.prepend] using hh

theorem run_directRow {d : ℕ} (i : Index P) (G : Point d → Point d) (xF momentum E0 : Point d)
    (tape : Tape d (directRow P hR hc hsmall clock i)) :
    run (directRow P hR hc hsmall clock i) G ⟨table P hR hc hsmall clock,xF,momentum⟩ (splitEnv xF momentum E0) tape =
      pointResult (b P clock xF (splitValues momentum E0 0) i) [] := by
  have hh := run_affineRow [] xRef [(slopeSlot P hR hc hsmall clock i,yRef)] G
    (⟨table P hR hc hsmall clock,xF,momentum⟩ : Inputs d (size P hR hc hsmall clock)) (splitEnv xF momentum E0) tape
  simpa only [directRow,b,ClockCollocation.graph,slopes,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,table_slope,split_x,split_y] using hh


def splitTape (d : ℕ) (j : Fin 2) : Tape d (splitRow P hR hc hsmall clock j) :=
  ⟨PUnit.unit,PUnit.unit,rowTape d [] (List.ofFn fun k : Fin 1 =>
    (splitSlots P hR hc hsmall clock j (matrixIndex 1 0 k), .there (.there (batchRef k)))) (fun r => r) .here⟩

theorem splitTape_unique {d : ℕ} (j : Fin 2) (tape : Tape d (splitRow P hR hc hsmall clock j)) :
    tape = splitTape P hR hc hsmall clock d j := by
  rcases tape with ⟨⟨⟩,⟨⟩,tail⟩
  exact congrArg (fun t => (PUnit.unit,PUnit.unit,t)) (rowTape_unique [] _ (fun r => r) .here tail)

def directTape (d : ℕ) (i : Index P) : Tape d (directRow P hR hc hsmall clock i) :=
  rowTape d [] [(slopeSlot P hR hc hsmall clock i,yRef)] (fun r => r) xRef

theorem directTape_unique {d : ℕ} (i : Index P) (tape : Tape d (directRow P hR hc hsmall clock i)) :
    tape = directTape P hR hc hsmall clock d i := rowTape_unique [] _ (fun r => r) xRef tape

def packTape {d : ℕ} {τ : Ty} (ell : ℕ) (next : Prog (size P hR hc hsmall clock) (readyCtx P) τ)
    (data : Point d × Tape d next) : Tape d (code P hR hc hsmall clock ell next) :=
  ⟨PUnit.unit,PUnit.unit,data.1,splitTape P hR hc hsmall clock d,directTape P hR hc hsmall clock d,data.2⟩

def unpackTape {d : ℕ} {τ : Ty} (ell : ℕ) (next : Prog (size P hR hc hsmall clock) (readyCtx P) τ)
    (tape : Tape d (code P hR hc hsmall clock ell next)) : Point d × Tape d next :=
  ⟨tape.2.2.1,tape.2.2.2.2.2⟩

theorem unpack_packTape {d : ℕ} {τ : Ty} (ell : ℕ) (next : Prog (size P hR hc hsmall clock) (readyCtx P) τ)
    (data : Point d × Tape d next) : unpackTape P hR hc hsmall clock ell next (packTape P hR hc hsmall clock ell next data) = data := rfl

theorem pack_unpackTape {d : ℕ} {τ : Ty} (ell : ℕ) (next : Prog (size P hR hc hsmall clock) (readyCtx P) τ)
    (tape : Tape d (code P hR hc hsmall clock ell next)) : packTape P hR hc hsmall clock ell next (unpackTape P hR hc hsmall clock ell next tape) = tape := by
  rcases tape with ⟨⟨⟩,⟨⟩,E0,rows,direct,tail⟩
  have hr : rows = splitTape P hR hc hsmall clock d := funext (fun j => splitTape_unique P hR hc hsmall clock j (rows j))
  have hd : direct = directTape P hR hc hsmall clock d := funext (fun i => directTape_unique P hR hc hsmall clock i (direct i))
  subst rows direct
  rfl

def tapeEquiv {d : ℕ} {τ : Ty} (ell : ℕ) (next : Prog (size P hR hc hsmall clock) (readyCtx P) τ) :
    Tape d (code P hR hc hsmall clock ell next) ≃ Point d × Tape d next where
  toFun := unpackTape P hR hc hsmall clock ell next
  invFun := packTape P hR hc hsmall clock ell next
  left_inv := pack_unpackTape P hR hc hsmall clock ell next
  right_inv := unpack_packTape P hR hc hsmall clock ell next

theorem run_packed {d : ℕ} {τ : Ty} (ell : ℕ) (next : Prog (size P hR hc hsmall clock) (readyCtx P) τ)
    (G : Point d → Point d) (xF momentum E0 : Point d) (tailTape : Tape d next) :
    let input : Inputs d (size P hR hc hsmall clock) := ⟨table P hR hc hsmall clock,xF,momentum⟩
    let tail := run next G input (readyEnv P clock xF momentum E0) tailTape
    run (code P hR hc hsmall clock ell next) G input Env.empty
      (packTape P hR hc hsmall clock ell next (E0,tailTape)) =
      ⟨tail.value,Event.gaussian (origin ell)::tail.trace⟩ := by
  have hd := run_pureBatch (directRow P hR hc hsmall clock) (b P clock xF (splitValues momentum E0 0)) next G
    (⟨table P hR hc hsmall clock,xF,momentum⟩ : Inputs d (size P hR hc hsmall clock)) (splitEnv xF momentum E0)
    (directTape P hR hc hsmall clock d,tailTape)
    (fun i => run_directRow P hR hc hsmall clock i G xF momentum E0 (directTape P hR hc hsmall clock d i))
  have hs := run_pureBatch (splitRow P hR hc hsmall clock) (splitValues momentum E0)
    (.batch [] (directRow P hR hc hsmall clock) next) G
    (⟨table P hR hc hsmall clock,xF,momentum⟩ : Inputs d (size P hR hc hsmall clock)) (rawEnv xF momentum E0)
    (splitTape P hR hc hsmall clock d,directTape P hR hc hsmall clock d,tailTape)
    (fun j => run_splitRow P hR hc hsmall clock j G xF momentum E0 (splitTape P hR hc hsmall clock d j))
  change run (.batch [] (splitRow P hR hc hsmall clock) (.batch [] (directRow P hR hc hsmall clock) next)) G _ _ _ =
    run (.batch [] (directRow P hR hc hsmall clock) next) G _ (splitEnv xF momentum E0) _ at hs
  rw [hd] at hs
  exact congrArg (fun r : Result d τ => (⟨r.value,Event.gaussian (origin ell)::r.trace⟩ : Result d τ)) hs


theorem run_every_tape {d : ℕ} {τ : Ty} (ell : ℕ) (next : Prog (size P hR hc hsmall clock) (readyCtx P) τ)
    (G : Point d → Point d) (xF momentum : Point d) (tape : Tape d (code P hR hc hsmall clock ell next)) :
    let data := tapeEquiv P hR hc hsmall clock ell next tape
    let input : Inputs d (size P hR hc hsmall clock) := ⟨table P hR hc hsmall clock,xF,momentum⟩
    let tail := run next G input (readyEnv P clock xF momentum data.1) data.2
    run (code P hR hc hsmall clock ell next) G input Env.empty tape =
      ⟨tail.value,Event.gaussian (origin ell)::tail.trace⟩ := by
  have hh := run_packed P hR hc hsmall clock ell next G xF momentum
    (tapeEquiv P hR hc hsmall clock ell next tape).1 (tapeEquiv P hR hc hsmall clock ell next tape).2
  change run _ _ _ _ ((tapeEquiv P hR hc hsmall clock ell next).symm (tapeEquiv P hR hc hsmall clock ell next tape)) = _ at hh
  rw [Equiv.symm_apply_apply] at hh
  exact hh

theorem syntaxCount_code {τ : Ty} (ell : ℕ) (next : Prog (size P hR hc hsmall clock) (readyCtx P) τ) (kind : EventKind) :
    syntaxCount kind (code P hR hc hsmall clock ell next) = (if kind=.gaussian then 1 else 0)+syntaxCount kind next := by
  cases kind <;> simp [code,syntaxCount,instructionCount,Instr.eventKind,splitRow,MeanGaussianSetup.syntaxCount_row,directRow,syntaxCount_affineRow]

theorem executed_counts {d : ℕ} {τ : Ty} (ell : ℕ) (next : Prog (size P hR hc hsmall clock) (readyCtx P) τ)
    (kind : EventKind) (G : Point d → Point d) (input : Inputs d (size P hR hc hsmall clock))
    (tape : Tape d (code P hR hc hsmall clock ell next)) :
    shapeCount kind ((run (code P hR hc hsmall clock ell next) G input Env.empty tape).trace.map Event.erase) =
      (if kind=.gaussian then 1 else 0)+syntaxCount kind next := by
  rw [run_trace_shape,shapeCount_staticTrace,syntaxCount_code]


def splitTapeEquiv {d : ℕ} (j : Fin 2) : Tape d (splitRow P hR hc hsmall clock j) ≃ PUnit where
  toFun _ := PUnit.unit
  invFun _ := splitTape P hR hc hsmall clock d j
  left_inv t := (splitTape_unique P hR hc hsmall clock j t).symm
  right_inv t := by cases t; rfl

def directTapeEquiv {d : ℕ} (i : Index P) : Tape d (directRow P hR hc hsmall clock i) ≃ PUnit where
  toFun _ := PUnit.unit
  invFun _ := directTape P hR hc hsmall clock d i
  left_inv t := (directTape_unique P hR hc hsmall clock i t).symm
  right_inv t := by cases t; rfl

end AcceleratedLogConcave.Root.ClockPublicSetup
