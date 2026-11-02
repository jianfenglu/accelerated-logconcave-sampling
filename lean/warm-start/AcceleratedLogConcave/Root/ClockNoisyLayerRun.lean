import AcceleratedLogConcave.Root.ClockNoisyLayer

/-! Exact one-layer execution from a populated center store. The residual C Z
and complete provenance remain; this is not an initialized root program. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Root.ClockNoisyLayer
open Oracle Oracle.TapeLowering Oracle.AffineLowering Oracle.NoisyLayer
open scoped BigOperators

def outerOrigin (layer : ℕ) : Origin := [⟨.publicSampling,.mainLayer,0,layer,0⟩]
def drawOrigin (layer node occurrence : ℕ) : Origin := [⟨.publicSampling,.samplingLayer,occurrence,layer,node⟩]

theorem drawOrigin_injective (layer : ℕ) :
    Function.Injective (fun key : ℕ × ℕ => drawOrigin layer key.1 key.2) := by
  intro x y h
  have hf := List.singleton_injective h
  exact Prod.ext (congrArg Frame.node hf) (congrArg Frame.occurrence hf)

variable (P : SourceSchedule)
abbrev storeCtx : Ctx := replyCtx (N P) (replyCtx (N P) [])
def oldRef (i : Index P) : Ref (storeCtx P) .point := batchRef i
def directRef (i : Index P) : Ref (storeCtx P) .point := RefMap.shiftMany (N P) (batchRef i)
def stored {d : ℕ} (clock : ClockLaw.Clock) (xF Y0 : Point d) (oldCenters : Index P → Point d) : Env d (storeCtx P) :=
  Env.prepend oldCenters (Env.prepend (b P clock xF Y0) Env.empty)

theorem stored_old {d : ℕ} (clock : ClockLaw.Clock) (xF Y0 : Point d) (oldCenters : Index P → Point d) (i : Index P) :
    storedPoint (stored P clock xF Y0 oldCenters) (oldRef P i) = oldCenters i := prepend_batchRef _ _ _
theorem stored_direct {d : ℕ} (clock : ClockLaw.Clock) (xF Y0 : Point d) (oldCenters : Index P → Point d) (i : Index P) :
    storedPoint (stored P clock xF Y0 oldCenters) (directRef P i) = b P clock xF Y0 i := by
  change Env.prepend oldCenters (Env.prepend (b P clock xF Y0) Env.empty) (RefMap.shiftMany (N P) (batchRef i)) = _
  rw [prepend_shiftMany]
  exact prepend_batchRef _ _ _

def designated (layer : ℕ) (i : Index P) : Origin := drawOrigin layer i.val 0
def residual (layer : ℕ) (i : Index P) : Origin := drawOrigin layer i.val 1

variable (hR : P.R ≤ 1/2) (hc : 0 < P.csch) (hsmall : P.csch < 1/160) (clock : ClockLaw.Clock)
local notation "c₀" => c P hR hc hsmall clock
local notation "p₀" => p P hR hc hsmall clock
local notation "e₀" => e P hR hc hsmall clock
local notation "T₀" => T P hR hc hsmall clock
local notation "coeff₀" => coeff P hR hc hsmall clock
local notation "size₀" => tableSize P hR hc hsmall clock

def auxiliary (layer : ℕ) (i : Index P) (k : Fin (g P hR hc hsmall clock i)) : Origin :=
  drawOrigin layer i.val (k.val+2)

theorem designated_ne_residual (layer : ℕ) (i j : Index P) : designated P layer i ≠ residual P layer j := by
  intro h
  have ho := congrArg Prod.snd (@drawOrigin_injective layer (i.val,0) (j.val,1) h)
  contradiction
theorem designated_ne_auxiliary (layer : ℕ) (i j : Index P) (k : Fin (g P hR hc hsmall clock j)) :
    designated P layer i ≠ auxiliary P hR hc hsmall clock layer j k := by
  intro h
  have ho := congrArg Prod.snd (@drawOrigin_injective layer (i.val,0) (j.val,k.val+2) h)
  change 0 = k.val+2 at ho
  omega
theorem residual_ne_auxiliary (layer : ℕ) (i j : Index P) (k : Fin (g P hR hc hsmall clock j)) :
    residual P layer i ≠ auxiliary P hR hc hsmall clock layer j k := by
  intro h
  have ho := congrArg Prod.snd (@drawOrigin_injective layer (i.val,1) (j.val,k.val+2) h)
  change 1 = k.val+2 at ho
  omega

/-- General continuation is retained to expose its actual additional counts. -/
def layer {τ : Ty} (ell : ℕ) (next : Prog size₀ (nextCtx (N P) (storeCtx P)) τ) : Prog size₀ (storeCtx P) τ :=
  noisyLayer c₀ p₀ e₀ (oldRef P) (directRef P) (outerOrigin ell) (designated P ell) (residual P ell)
    (auxiliary P hR hc hsmall clock ell) next

def returnRow (j : Index P) : Prog size₀ (nextCtx (N P) (storeCtx P)) .point := .ret (batchRef j)
def rowProgram (ell : ℕ) (j : Index P) : Prog size₀ (storeCtx P) .point :=
  layer P hR hc hsmall clock ell (returnRow P hR hc hsmall clock j)

theorem run_returnRow {d : ℕ} (j : Index P) (G : Point d → Point d) (input : Inputs d size₀)
    (new : Index P → Point d) (env : Env d (noiseCtx (N P) (storeCtx P)))
    (tape : Tape d (returnRow P hR hc hsmall clock j)) :
    run (returnRow P hR hc hsmall clock j) G input (Env.prepend new env) tape = pointResult (new j) [] := by
  change pointResult (storedPoint (Env.prepend new env) (batchRef j)) [] = _
  rw [prepend_batchRef]

def tapeEquiv {d : ℕ} {τ : Ty} (ell : ℕ) (next : Prog size₀ (nextCtx (N P) (storeCtx P)) τ) :
    Tape d (layer P hR hc hsmall clock ell next) ≃ LayerData c₀ p₀ next d :=
  NoisyLayer.layerTapeEquiv c₀ p₀ e₀ (oldRef P) (directRef P) (outerOrigin ell) (designated P ell) (residual P ell)
    (auxiliary P hR hc hsmall clock ell) next

/-- Every TARGET raw tape is packed. No inverse of the child matrix is asserted. -/
theorem pack_every_tape {d : ℕ} {τ : Ty} (ell : ℕ) (next : Prog size₀ (nextCtx (N P) (storeCtx P)) τ)
    (tape : Tape d (layer P hR hc hsmall clock ell next)) :
    (tapeEquiv P hR hc hsmall clock ell next).symm (tapeEquiv P hR hc hsmall clock ell next tape) = tape :=
  Equiv.symm_apply_apply _ _

abbrev ChildData (d : ℕ) := ∀ i : Index P, Point d × ((Fin (g P hR hc hsmall clock i) → Point d) × ResidualTape (p₀ i))

/-- Actual unchanged child runs, on the transformed full source tapes. -/
def sources {d : ℕ} (G : Point d → Point d) (oldCenters : Index P → Point d)
    (data : ChildData P hR hc hsmall clock d) : Index P → Result d .point :=
  fun i => run (p₀ i) G ⟨coeff₀ i,oldCenters i,(data i).1⟩ Env.empty
    (transformedSourceTape (p₀ i) (e₀ i) (T₀ i) (data i).2.1 (data i).2.2)

def updated {d : ℕ} (xF Y0 : Point d) (Q Z : Index P → Point d) (j : Index P) : Point d :=
  b P clock xF Y0 j + (∑ i, A P clock j i • Q i) + ∑ k, C P clock j k • Z k

def fullTrace (ell : ℕ) {d : ℕ} (source : Index P → Result d .point) (tail : List (Event d)) : List (Event d) :=
  ((List.ofFn (fun i => [Event.gaussian (designated P ell i)] ++
      List.ofFn (fun j => Event.gaussian (auxiliary P hR hc hsmall clock ell i j)) ++
      (source i).trace.filter keepNonGaussian)).flatten ++
    List.ofFn (fun j => Event.gaussian (residual P ell j)) ++ tail).map (Event.withPrefix (outerOrigin ell))

theorem run_packed {d : ℕ} {τ : Ty} (ell : ℕ) (next : Prog size₀ (nextCtx (N P) (storeCtx P)) τ)
    (G : Point d → Point d) (hostX hostP xF Y0 : Point d) (oldCenters : Index P → Point d)
    (data : LayerData c₀ p₀ next d) :
    let input : Inputs d size₀ := ⟨table P hR hc hsmall clock,hostX,hostP⟩
    let src := sources P hR hc hsmall clock G oldCenters data.1
    let Q := fun i => (src i).value
    let tail := run next G input (Env.prepend (updated P clock xF Y0 Q data.2.1)
      (Env.prepend data.2.1 (Env.prepend Q (stored P clock xF Y0 oldCenters)))) data.2.2
    run (layer P hR hc hsmall clock ell next) G input (stored P clock xF Y0 oldCenters)
      ((tapeEquiv P hR hc hsmall clock ell next).symm data) =
      ⟨tail.value,fullTrace P hR hc hsmall clock ell src tail.trace⟩ := by
  have hh := run_noisyLayer_packed c₀ p₀ e₀ (oldRef P) (directRef P) (outerOrigin ell) (designated P ell) (residual P ell)
      (auxiliary P hR hc hsmall clock ell) next (A P clock) (C P clock) T₀ coeff₀ hostX hostP G
      (stored P clock xF Y0 oldCenters) data
  simp only [stored_old, stored_direct] at hh
  exact hh

theorem run_row_packed {d : ℕ} (ell : ℕ) (j : Index P) (G : Point d → Point d)
    (hostX hostP xF Y0 : Point d) (oldCenters : Index P → Point d)
    (data : ChildData P hR hc hsmall clock d) (Z : Index P → Point d)
    (continuationTape : Tape d (returnRow P hR hc hsmall clock j)) :
    let src := sources P hR hc hsmall clock G oldCenters data
    run (rowProgram P hR hc hsmall clock ell j) G ⟨table P hR hc hsmall clock,hostX,hostP⟩
      (stored P clock xF Y0 oldCenters)
      ((tapeEquiv P hR hc hsmall clock ell (returnRow P hR hc hsmall clock j)).symm ⟨data,Z,continuationTape⟩) =
      ⟨updated P clock xF Y0 (fun i => (src i).value) Z j,fullTrace P hR hc hsmall clock ell src []⟩ := by
  have hh := run_packed P hR hc hsmall clock ell (returnRow P hR hc hsmall clock j)
    G hostX hostP xF Y0 oldCenters ⟨data,Z,continuationTape⟩
  simpa only [rowProgram, run_returnRow, pointResult] using hh

theorem run_row_every_tape {d : ℕ} (ell : ℕ) (j : Index P) (G : Point d → Point d)
    (hostX hostP xF Y0 : Point d) (oldCenters : Index P → Point d)
    (tape : Tape d (rowProgram P hR hc hsmall clock ell j)) :
    let data := tapeEquiv P hR hc hsmall clock ell (returnRow P hR hc hsmall clock j) tape
    let src := sources P hR hc hsmall clock G oldCenters data.1
    run (rowProgram P hR hc hsmall clock ell j) G ⟨table P hR hc hsmall clock,hostX,hostP⟩
      (stored P clock xF Y0 oldCenters) tape =
      ⟨updated P clock xF Y0 (fun i => (src i).value) data.2.1 j,fullTrace P hR hc hsmall clock ell src []⟩ := by
  let data := tapeEquiv P hR hc hsmall clock ell (returnRow P hR hc hsmall clock j) tape
  have hh := run_row_packed P hR hc hsmall clock ell j G hostX hostP xF Y0 oldCenters data.1 data.2.1 data.2.2
  change run (rowProgram P hR hc hsmall clock ell j) G _ _
    ((tapeEquiv P hR hc hsmall clock ell (returnRow P hR hc hsmall clock j)).symm
      (tapeEquiv P hR hc hsmall clock ell (returnRow P hR hc hsmall clock j) tape)) = _ at hh
  erw [Equiv.symm_apply_apply] at hh
  exact hh

/-- Counts are for all children and all residual blocks, including a one-row return. -/
theorem executed_counts {d : ℕ} {τ : Ty} (ell : ℕ) (next : Prog size₀ (nextCtx (N P) (storeCtx P)) τ)
    (kind : EventKind) (G : Point d → Point d) (input : Inputs d size₀) (env : Env d (storeCtx P))
    (tape : Tape d (layer P hR hc hsmall clock ell next)) :
    shapeCount kind ((run (layer P hR hc hsmall clock ell next) G input env tape).trace.map Event.erase) =
      (if kind = .gaussian then 2*N P + ∑ i, g P hR hc hsmall clock i else ∑ i, syntaxCount kind (p₀ i)) +
        syntaxCount kind next := by
  have hh := executedCount_noisyLayer c₀ p₀ e₀ (oldRef P) (directRef P) (outerOrigin ell)
    (designated P ell) (residual P ell) (auxiliary P hR hc hsmall clock ell) next kind G input env tape
  refine hh.trans ?_
  cases kind with
  | gaussian =>
    change (N P + (∑ i, g P hR hc hsmall clock i) + N P) + syntaxCount .gaussian next =
      (2*N P + ∑ i, g P hR hc hsmall clock i) + syntaxCount .gaussian next
    omega
  | gradient => rfl
  | uniform => rfl

theorem executed_row_counts {d : ℕ} (ell : ℕ) (j : Index P) (kind : EventKind)
    (G : Point d → Point d) (input : Inputs d size₀) (env : Env d (storeCtx P))
    (tape : Tape d (rowProgram P hR hc hsmall clock ell j)) :
    shapeCount kind ((run (rowProgram P hR hc hsmall clock ell j) G input env tape).trace.map Event.erase) =
      if kind = .gaussian then 2*N P + ∑ i, g P hR hc hsmall clock i else ∑ i, syntaxCount kind (p₀ i) := by
  simpa only [rowProgram, returnRow, syntaxCount, Nat.add_zero] using
    executed_counts P hR hc hsmall clock ell (returnRow P hR hc hsmall clock j) kind G input env tape

/-- Gradient and uniform counts equal the sums of the actual decoded source runs. -/
theorem executed_source_counts {d : ℕ} (ell : ℕ) (j : Index P) (kind : EventKind) (hk : kind ≠ .gaussian)
    (G : Point d → Point d) (hostX hostP xF Y0 : Point d) (oldCenters : Index P → Point d)
    (tape : Tape d (rowProgram P hR hc hsmall clock ell j)) :
    let data := tapeEquiv P hR hc hsmall clock ell (returnRow P hR hc hsmall clock j) tape
    let src := sources P hR hc hsmall clock G oldCenters data.1
    shapeCount kind ((run (rowProgram P hR hc hsmall clock ell j) G
      ⟨table P hR hc hsmall clock,hostX,hostP⟩ (stored P clock xF Y0 oldCenters) tape).trace.map Event.erase) =
      ∑ i, shapeCount kind ((src i).trace.map Event.erase) := by
  have hh := executed_row_counts P hR hc hsmall clock ell j kind G
    ⟨table P hR hc hsmall clock,hostX,hostP⟩ (stored P clock xF Y0 oldCenters) tape
  simp only [hk, ite_false] at hh
  refine hh.trans ?_
  apply Finset.sum_congr rfl
  intro i _
  simp only [sources, run_trace_shape, shapeCount_staticTrace]
end AcceleratedLogConcave.Root.ClockNoisyLayer
