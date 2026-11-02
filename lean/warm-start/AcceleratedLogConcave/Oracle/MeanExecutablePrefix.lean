import AcceleratedLogConcave.Oracle.MeanGaussianSetup
import AcceleratedLogConcave.Oracle.PrefixDirect

/-! Executable incoming prefix for a nonterminal mean. It pays for the private
sampling program, scales its returned position, retains the original momentum,
assembles all designated inputs, draws the conditional-flow seeds, and stores
the literal direct rows. The continuation performs center initialization.
The sampling program remains an explicit recursive supplier, to be instantiated
by the source recursive constructor; this file does not certify that supplier. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.MeanExecutablePrefix
open AffineLowering NoisyLayer
open AcceleratedLogConcave.Numerics.AffineGraph
open scoped BigOperators

abbrev scaledCtx (Γ : Ctx) := replyCtx 1 (replyCtx 1 Γ)
abbrev assemblyCtx (f : ℕ) (Γ : Ctx) := replyCtx f (replyCtx f (scaledCtx Γ))
abbrev seedCtx (f h : ℕ) (Γ : Ctx) := replyCtx h (assemblyCtx f Γ)
abbrev readyCtx (n f h : ℕ) (Γ : Ctx) := replyCtx n (seedCtx f h Γ)

abbrev scaleRow (slot : Fin C) : Prog C (replyCtx 1 Γ) .point :=
  .step [] (.pure (.publicScalar slot)) <|
  .step [] (.pure (.smul .here (.there (batchRef 0)))) (.ret .here)

theorem run_scaleRow (slot : Fin C) (G : Point d → Point d)
    (input : Inputs d C) (env : Env d Γ) (Y : Point d)
    (tape : Tape d (scaleRow (Γ := Γ) slot)) :
    run (scaleRow slot) G input (Env.prepend (fun _ : Fin 1 => Y) env) tape =
      pointResult (input.coefficient slot • Y) [] := by
  rfl

theorem stored_shiftMany (values : Fin k → Point d) (env : Env d Γ)
    (r : Ref Γ .point) :
    storedPoint (Env.prepend values env) (RefMap.shiftMany k r) = storedPoint env r :=
  prepend_shiftMany values env r

def savedSeed : RefMap Γ (seedCtx f h Γ) :=
  fun r => RefMap.shiftMany h (RefMap.shiftMany f (RefMap.shiftMany f
    (RefMap.shiftMany 1 (RefMap.shiftMany 1 r))))

def saved : RefMap Γ (readyCtx n f h Γ) := fun r => RefMap.shiftMany n (savedSeed r)
def designated (i : Fin m) : Ref (readyCtx n (m+1) h Γ) .point :=
  RefMap.shiftMany n (RefMap.shiftMany h (batchRef i.succ))
def direct (j : Fin n) : Ref (readyCtx n f h Γ) .point := batchRef j

/-- Position and score are cached separately from all conditional-flow draws. -/
def anchorRef (M : MeanGeometry order) (anchors : Fin a ≃ M.Anchor)
    (seeds : Fin h ≃ Fin order × M.Kernel) (k : Fin a) :
    Ref (seedCtx (m+1) h Γ) .point :=
  match anchors k with
  | .inl _ => RefMap.shiftMany h (RefMap.shiftMany (m+1)
      (RefMap.shiftMany (m+1) (batchRef 0)))
  | .inr (.inl _) => RefMap.shiftMany h (batchRef 0)
  | .inr (.inr z) => batchRef (seeds.symm z)

/-- No initialization draw is hidden here: initializeCenters belongs to the
nonterminal continuation and receives the stored direct rows produced below. -/
def code (M : MeanGeometry order) (anchors : Fin a ≃ M.Anchor)
    (seeds : Fin h ≃ Fin order × M.Kernel)
    (privateC : ℕ) (sampling : Program privateC .point)
    (privateSlots : Fin privateC → Fin C) (scaleSlot : Fin C)
    (x P : Ref Γ .point)
    (assemblySlots : Fin ((m+1)*(m+1)+(m+1)) → Fin C)
    (assemblyOrigins : Fin (m+1) → Origin) (flowOrigins : Fin h → Origin)
    (directSlots : Fin (n*a) → Fin C)
    (next : Prog C (readyCtx n (m+1) h Γ) τ) : Prog C Γ τ :=
  .batch [] (fun _ : Fin 1 => sampling.embed privateSlots x P)
    (.batch [] (fun _ : Fin 1 => scaleRow scaleSlot)
      (MeanGaussianSetup.setup assemblySlots (RefMap.shiftMany 1 (RefMap.shiftMany 1 P))
        assemblyOrigins
        (.batch [] (fun k => residualDraw (flowOrigins k))
          (.batch [] (PrefixDirect.row directSlots (savedSeed x) (anchorRef M anchors seeds)) next))))

theorem syntaxCount_code (kind : EventKind) (M : MeanGeometry order)
    (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin order × M.Kernel)
    (privateC : ℕ) (sampling : Program privateC .point)
    (privateSlots : Fin privateC → Fin C) (scaleSlot : Fin C)
    (x P : Ref Γ .point)
    (assemblySlots : Fin ((m+1)*(m+1)+(m+1)) → Fin C)
    (assemblyOrigins : Fin (m+1) → Origin) (flowOrigins : Fin h → Origin)
    (directSlots : Fin (n*a) → Fin C)
    (next : Prog C (readyCtx n (m+1) h Γ) τ) :
    syntaxCount kind (code M anchors seeds privateC sampling privateSlots scaleSlot x P
      assemblySlots assemblyOrigins flowOrigins directSlots next) =
      syntaxCount kind sampling + (if kind = .gaussian then m+1+h else 0) +
        syntaxCount kind next := by
  unfold code
  rw [syntaxCount_batch]
  simp only [Program.embed, syntaxCount_lower, Finset.sum_const, smul_eq_mul]
  rw [syntaxCount_batch]
  simp only [syntaxCount, instructionCount, Instr.eventKind]
  rw [MeanGaussianSetup.syntaxCount_setup]
  cases kind <;> simp [syntaxCount, PrefixDirect.syntaxCount_row, residualDraw,
    instructionCount, Instr.eventKind, Nat.add_assoc]

/-- Literal assembly arithmetic, before identifying its public table with the
positive square root construction. -/
def assemblyValues (slots : Fin (f*f+f) → Fin C) (input : Inputs d C)
    (P : Point d) (Z : Fin f → Point d) (i : Fin f) : Point d :=
  input.coefficient (slots (Fin.natAdd (f*f) i)) • P +
    ∑ j, input.coefficient (slots (matrixIndex f i j)) • Z j

theorem run_assemblyRow (slots : Fin (f*f+f) → Fin C) (P : Ref Γ .point)
    (i : Fin f) (G : Point d → Point d) (input : Inputs d C)
    (env : Env d Γ) (Z : Fin f → Point d)
    (tape : Tape d (MeanGaussianSetup.row slots P i)) :
    run (MeanGaussianSetup.row slots P i) G input (Env.prepend Z env) tape =
      pointResult (assemblyValues slots input (storedPoint env P) Z i) [] := by
  simp only [MeanGaussianSetup.row, run, evalInstr, evalPure]
  rw [run_affineRow_ofFn]
  change pointResult (input.coefficient (slots (Fin.natAdd (f*f) i)) •
    storedPoint (Env.prepend Z env) (RefMap.shiftMany f P) +
    ∑ j, input.coefficient (slots (matrixIndex f i j)) •
      storedPoint (Env.prepend Z env) (batchRef j)) [] = _
  rw [show storedPoint (Env.prepend Z env) (RefMap.shiftMany f P) =
    storedPoint env P from prepend_shiftMany Z env P]
  simp only [prepend_batchRef]
  rfl

/-- Values of the cached anchors, with each independent flow seed selected by
its occurrence enumeration. -/
def anchorValues (M : MeanGeometry order) (anchors : Fin a ≃ M.Anchor)
    (seeds : Fin h ≃ Fin order × M.Kernel)
    (Y G0 : Point d) (Z : Fin h → Point d) (k : Fin a) : Point d :=
  match anchors k with
  | .inl _ => Y
  | .inr (.inl _) => G0
  | .inr (.inr z) => Z (seeds.symm z)

theorem stored_anchorRef (M : MeanGeometry order) (anchors : Fin a ≃ M.Anchor)
    (seeds : Fin h ≃ Fin order × M.Kernel) (env : Env d Γ)
    (U Y : Point d) (raw A : Fin (m+1) → Point d) (Z : Fin h → Point d)
    (k : Fin a) :
    storedPoint (Env.prepend Z (Env.prepend A (Env.prepend raw
      (Env.prepend (fun _ : Fin 1 => Y) (Env.prepend (fun _ : Fin 1 => U) env)))))
      (anchorRef M anchors seeds k) = anchorValues M anchors seeds Y (A 0) Z k := by
  unfold anchorRef anchorValues
  split <;> simp only [stored_shiftMany, prepend_batchRef]

theorem stored_savedSeed (env : Env d Γ) (U Y : Point d)
    (raw A : Fin f → Point d) (Z : Fin h → Point d) (r : Ref Γ τ) :
    Env.prepend Z (Env.prepend A (Env.prepend raw
      (Env.prepend (fun _ : Fin 1 => Y) (Env.prepend (fun _ : Fin 1 => U) env))))
      (savedSeed r) = env r := by
  simp only [savedSeed, prepend_shiftMany]

/-- The original input, including the parent's retained P, survives the prefix. -/
theorem stored_saved (env : Env d Γ) (U Y : Point d)
    (raw A : Fin f → Point d) (Z : Fin h → Point d) (D : Fin n → Point d)
    (r : Ref Γ τ) :
    Env.prepend D (Env.prepend Z (Env.prepend A (Env.prepend raw
      (Env.prepend (fun _ : Fin 1 => Y) (Env.prepend (fun _ : Fin 1 => U) env)))))
      (saved r) = env r := by
  unfold saved
  rw [prepend_shiftMany]
  exact stored_savedSeed env U Y raw A Z r

theorem stored_designated (env : Env d Γ) (U Y : Point d)
    (raw A : Fin (m+1) → Point d) (Z : Fin h → Point d) (D : Fin n → Point d)
    (i : Fin m) :
    storedPoint (Env.prepend D (Env.prepend Z (Env.prepend A (Env.prepend raw
      (Env.prepend (fun _ : Fin 1 => Y) (Env.prepend (fun _ : Fin 1 => U) env))))))
      (designated i) = A i.succ := by
  simp only [designated, stored_shiftMany, prepend_batchRef]

theorem stored_direct (env : Env d (seedCtx f h Γ)) (D : Fin n → Point d) (j : Fin n) :
    storedPoint (Env.prepend D env) (direct j) = D j :=
  prepend_batchRef D env j

/-- The direct arithmetic actually executed from all cached anchors. -/
def directValues (slots : Fin (n*a) → Fin C) (input : Inputs d C)
    (x : Point d) (values : Fin a → Point d) (j : Fin n) : Point d :=
  x + ∑ k, input.coefficient (slots (PrefixDirect.slot j k)) • values k


theorem run_pureBatch (rows : Fin n → Prog C Γ .point) (values : Fin n → Point d)
    (next : Prog C (replyCtx n Γ) τ) (G : Point d → Point d)
    (input : Inputs d C) (env : Env d Γ)
    (tape : Tape d (.batch [] rows next))
    (hrows : ∀ j, run (rows j) G input env (tape.1 j) = pointResult (values j) []) :
    run (.batch [] rows next) G input env tape =
      run next G input (Env.prepend values env) tape.2 := by
  rw [run]
  simp only [hrows, pointResult, List.ofFn_const, List.flatten_replicate_nil,
    List.nil_append, prefix_nil]

private theorem flatten_ofFn_singleton (f : Fin n → α) :
    (List.ofFn (fun j => [f j])).flatten = List.ofFn f := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.ofFn_succ,List.flatten_cons,List.singleton_append,ih]

theorem run_drawBatch (origins : Fin n → Origin)
    (next : Prog C (replyCtx n Γ) τ) (G : Point d → Point d)
    (input : Inputs d C) (env : Env d Γ)
    (tape : Tape d (.batch [] (fun i => residualDraw (origins i)) next)) :
    let values := fun i => (tape.1 i).1
    let tail := run next G input (Env.prepend values env) tape.2
    run (.batch [] (fun i => residualDraw (origins i)) next) G input env tape =
      ⟨tail.value, List.ofFn (fun i => Event.gaussian (origins i)) ++ tail.trace⟩ := by
  rw [run]
  simp only [residualDraw, run, evalInstr, List.append_nil, prefix_nil]
  rw [flatten_ofFn_singleton]
  rfl

theorem run_oneBatch (p : Prog C Γ .point)
    (next : Prog C (replyCtx 1 Γ) τ) (G : Point d → Point d)
    (input : Inputs d C) (env : Env d Γ)
    (tape : Tape d (.batch [] (fun _ : Fin 1 => p) next)) :
    let first := run p G input env (tape.1 0)
    let tail := run next G input (Env.prepend (fun _ : Fin 1 => first.value) env) tape.2
    run (.batch [] (fun _ : Fin 1 => p) next) G input env tape =
      ⟨tail.value, first.trace ++ tail.trace⟩ := by
  rw [run]
  have hv : (fun j : Fin 1 => (run p G input env (tape.1 j)).value) =
      (fun _ : Fin 1 => (run p G input env (tape.1 0)).value) := by
    funext j; exact congrArg (fun k => (run p G input env (tape.1 k)).value) (Fin.eq_zero j)
  simp only [hv, prefix_nil, List.ofFn_succ, List.ofFn_zero, List.flatten_cons,
    List.flatten_nil, List.append_nil]

theorem run_scaleBatch (slot : Fin C)
    (next : Prog C (replyCtx 1 (replyCtx 1 Γ)) τ) (G : Point d → Point d)
    (input : Inputs d C) (env : Env d Γ) (U : Point d)
    (tape : Tape d (.batch [] (fun _ : Fin 1 => scaleRow (Γ := Γ) slot) next)) :
    run (.batch [] (fun _ : Fin 1 => scaleRow (Γ := Γ) slot) next) G input
      (Env.prepend (fun _ : Fin 1 => U) env) tape =
      run next G input (Env.prepend (fun _ : Fin 1 => input.coefficient slot • U)
        (Env.prepend (fun _ : Fin 1 => U) env)) tape.2 := by
  apply run_pureBatch
  intro j
  exact run_scaleRow slot G input env U (tape.1 j)

theorem run_setup (slots : Fin (f*f+f) → Fin C) (P : Ref Γ .point)
    (origins : Fin f → Origin) (next : Prog C (replyCtx f (replyCtx f Γ)) τ)
    (G : Point d → Point d) (input : Inputs d C) (env : Env d Γ)
    (tape : Tape d (MeanGaussianSetup.setup slots P origins next)) :
    let raw := fun i => (tape.1 i).1
    let A := assemblyValues slots input (storedPoint env P) raw
    let tail := run next G input (Env.prepend A (Env.prepend raw env)) tape.2.2
    run (MeanGaussianSetup.setup slots P origins next) G input env tape =
      ⟨tail.value, List.ofFn (fun i => Event.gaussian (origins i)) ++ tail.trace⟩ := by
  unfold MeanGaussianSetup.setup
  erw [run_drawBatch]
  dsimp only
  have hb := run_pureBatch (MeanGaussianSetup.row slots P)
    (assemblyValues slots input (storedPoint env P) (fun i => (tape.1 i).1))
    next G input (Env.prepend (fun i => (tape.1 i).1) env) tape.2
    (fun j => run_assemblyRow slots P j G input env _ (tape.2.1 j))
  rw [hb]

theorem run_directBatch (M : MeanGeometry order) (anchors : Fin a ≃ M.Anchor)
    (seeds : Fin h ≃ Fin order × M.Kernel) (slots : Fin (n*a) → Fin C)
    (x : Ref Γ .point) (next : Prog C (readyCtx n (m+1) h Γ) τ)
    (G : Point d → Point d) (input : Inputs d C) (env : Env d Γ)
    (U Y : Point d) (raw A : Fin (m+1) → Point d) (Z : Fin h → Point d)
    (tape : Tape d (.batch [] (PrefixDirect.row slots (savedSeed x)
      (anchorRef M anchors seeds)) next)) :
    run (.batch [] (PrefixDirect.row slots (savedSeed x) (anchorRef M anchors seeds)) next)
      G input (Env.prepend Z (Env.prepend A (Env.prepend raw
        (Env.prepend (fun _ : Fin 1 => Y) (Env.prepend (fun _ : Fin 1 => U) env))))) tape =
      run next G input (Env.prepend (directValues slots input (storedPoint env x)
        (anchorValues M anchors seeds Y (A 0) Z))
        (Env.prepend Z (Env.prepend A (Env.prepend raw
          (Env.prepend (fun _ : Fin 1 => Y) (Env.prepend (fun _ : Fin 1 => U) env)))))) tape.2 := by
  apply run_pureBatch
  intro j
  rw [run_affineRow_ofFn]
  have hx := stored_savedSeed env U Y raw A Z x
  have ha (k : Fin a) := stored_anchorRef M anchors seeds env U Y raw A Z k
  change pointResult (storedPoint _ (savedSeed x) + ∑ k,
    input.coefficient (slots (PrefixDirect.slot j k)) •
      storedPoint _ (anchorRef M anchors seeds k)) [] = _
  change storedPoint _ (savedSeed x) = storedPoint env x at hx
  simp only [ha, hx, directValues]

/-- The executable direct arithmetic is exactly the source direct vector when
its public coefficients are the extracted graph table. -/
theorem directValues_eq_source (M : MeanGeometry order) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin order × M.Kernel)
    (r σ : ℝ) (slots : Fin (n*a) → Fin C) (input : Inputs d C)
    (htable : input.coefficient ∘ slots = PrefixDirect.table M nodes anchors r σ)
    (x Y G0 : Point d) (Z : Fin h → Point d) (j : Fin n) :
    directValues slots input x (anchorValues M anchors seeds Y G0 Z) j =
      M.direct r σ x Y G0 (fun b ρ => Z (seeds.symm (b,ρ))) (nodes j) := by
  have hs (k : Fin a) : input.coefficient (slots (PrefixDirect.slot j k)) =
      M.centerForm r σ (nodes j) (.inl (anchors k)) := by
    simpa [PrefixDirect.table, PrefixDirect.slot] using congrFun htable (PrefixDirect.slot j k)
  have ha (k : Fin a) : anchorValues M anchors seeds Y G0 Z k =
      M.anchorValues Y G0 (fun b ρ => Z (seeds.symm (b,ρ))) (anchors k) := by
    cases hk : anchors k with
    | inl u => simp only [anchorValues, MeanGeometry.anchorValues, hk]
    | inr z =>
      cases z with
      | inl u => simp only [anchorValues, MeanGeometry.anchorValues, hk]
      | inr z => simp only [anchorValues, MeanGeometry.anchorValues, hk]
  simp only [directValues, hs, ha, MeanGeometry.direct]
  congr 1
  exact anchors.sum_comp (fun k => M.centerForm r σ (nodes j) (.inl k) •
    M.anchorValues Y G0 (fun b ρ => Z (seeds.symm (b,ρ))) k)

/-- The executable assembly arithmetic is the retained-input Gaussian assembly
with the literal positive square root coefficients. -/
theorem assemblyValues_eq_active (a : Fin f → ℝ)
    (ha : AcceleratedLogConcave.Conditional.GaussianAssembly.mass a < 1)
    (slots : Fin (f*f+f) → Fin C) (input : Inputs d C)
    (htable : input.coefficient ∘ slots = MeanGaussianSetup.table a)
    (P : Point d) (Z : Fin f → Point d) (i : Fin f) :
    assemblyValues slots input P Z i =
      AcceleratedLogConcave.Conditional.GaussianAssembly.active a P Z i := by
  have hs (k : Fin (f*f+f)) : input.coefficient (slots k) = MeanGaussianSetup.table a k :=
    congrFun htable k
  have hextra : MeanGaussianSetup.table a (Fin.natAdd (f*f) i) = a i :=
    matrixTable_extra (MeanGaussianSetup.inputRoot a) a i
  have hentry (j : Fin f) : MeanGaussianSetup.table a (matrixIndex f i j) =
      MeanGaussianSetup.inputRoot a i j :=
    matrixTable_entry (MeanGaussianSetup.inputRoot a) a i j
  simp only [assemblyValues, hs, hextra, hentry]
  exact (AcceleratedLogConcave.Conditional.GaussianAssembly.active_eq_sqrt_sum ha P Z i).symm

set_option maxRecDepth 3000 in
set_option maxHeartbeats 800000 in
/-- Complete fixed-tape result of the incoming prefix, including every event
of the paid private sampler and both independent Gaussian arrays. -/
theorem run_code (M : MeanGeometry order) (anchors : Fin a ≃ M.Anchor)
    (seeds : Fin h ≃ Fin order × M.Kernel)
    (privateC : ℕ) (sampling : Program privateC .point)
    (privateSlots : Fin privateC → Fin C) (scaleSlot : Fin C)
    (x P : Ref Γ .point)
    (assemblySlots : Fin ((m+1)*(m+1)+(m+1)) → Fin C)
    (assemblyOrigins : Fin (m+1) → Origin) (flowOrigins : Fin h → Origin)
    (directSlots : Fin (n*a) → Fin C)
    (next : Prog C (readyCtx n (m+1) h Γ) τ)
    (G : Point d → Point d) (input : Inputs d C) (env : Env d Γ)
    (tape : Tape d (code M anchors seeds privateC sampling privateSlots scaleSlot x P
      assemblySlots assemblyOrigins flowOrigins directSlots next)) :
    let privateResult := run (sampling.embed privateSlots x P) G input env (tape.1 0)
    let U : Point d := privateResult.value
    let Y := input.coefficient scaleSlot • U
    let raw := fun i => (tape.2.2.1 i).1
    let A := assemblyValues assemblySlots input (storedPoint env P) raw
    let Z := fun k => (tape.2.2.2.2.1 k).1
    let D := directValues directSlots input (storedPoint env x)
      (anchorValues M anchors seeds Y (A 0) Z)
    let tail := run next G input (Env.prepend D (Env.prepend Z (Env.prepend A
      (Env.prepend raw (Env.prepend (fun _ : Fin 1 => Y)
        (Env.prepend (fun _ : Fin 1 => U) env)))))) tape.2.2.2.2.2.2
    run (code M anchors seeds privateC sampling privateSlots scaleSlot x P
      assemblySlots assemblyOrigins flowOrigins directSlots next) G input env tape =
      ⟨tail.value, privateResult.trace ++ List.ofFn (fun i => Event.gaussian (assemblyOrigins i)) ++
        List.ofFn (fun k => Event.gaussian (flowOrigins k)) ++ tail.trace⟩ := by
  unfold code
  erw [run_oneBatch]
  dsimp only
  erw [run_scaleBatch]
  erw [run_setup]
  dsimp only
  simp only [storedPoint, prepend_shiftMany]
  erw [run_drawBatch]
  dsimp only
  erw [run_directBatch]
  simp only [List.append_assoc]
  rfl

end AcceleratedLogConcave.Oracle.MeanExecutablePrefix
