import AcceleratedLogConcave.Oracle.PrivateSamplingProgram

noncomputable section
namespace AcceleratedLogConcave.Oracle.PrivateSamplingProgram
open AffineLowering TapeLowering NoisyLayer RecursiveMeanProgram RecursiveMeanContinuation
open PrivateSamplingFinal
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false in
/-- Complete Result identity for initialization and the literal finite loop.
Every initial Gaussian occurrence is retained alongside the continuation trace. -/
theorem run_body {c cf : Fin n → ℕ} {p : ∀ i, Program (c i) .point}
    {pf : ∀ i, Program (cf i) .point} (cfg : Config n C c cf p pf)
    (direct : Fin n → Ref Γ .point) (outputDirect : Ref Γ .point)
    (G : Point d → Point d) (input : Inputs d C) (env : Env d Γ)
    (tape : Tape d (body cfg direct outputDirect)) :
    let finisher := fun {Δ : Ctx} (old _ : Fin n → Ref Δ .point)
      (saved : RefMap Γ Δ) => finish cfg old (saved outputDirect)
    let Z : Fin n → Point d := fun i => (tape.1 i).1
    let initialEnv : Env d (replyCtx n (replyCtx n Γ)) := Env.prepend
      (fun j => storedPoint env (direct j) + input.coefficient cfg.noise • Z j)
      (Env.prepend Z env)
    let tail := run (iterateThen c p cfg.mainSlots cfg.mainEquiv cfg.layerOrigin
      cfg.mainDesignated cfg.mainResidual cfg.mainAuxiliary finisher cfg.layers batchRef
      (fun i => RefMap.shiftMany n (RefMap.shiftMany n (direct i)))
      (fun r => RefMap.shiftMany n (RefMap.shiftMany n r))) G input initialEnv tape.2.2
    run (body cfg direct outputDirect) G input env tape =
      ⟨tail.value, List.ofFn (fun i => Event.gaussian (cfg.initialOrigin i)) ++ tail.trace⟩ := by
  dsimp only [body] at tape ⊢
  rw [run_initialize]
  simp only [prefix_nil]

set_option backward.isDefEq.respectTransparency false in
/-- Final child values and the two last noise blocks are taken from the actual
finite execution's final store and tape. No terminal state is supplied. -/
theorem run_body_value {c cf : Fin n → ℕ} {p : ∀ i, Program (c i) .point}
    {pf : ∀ i, Program (cf i) .point} (cfg : Config n C c cf p pf)
    (direct : Fin n → Ref Γ .point) (outputDirect : Ref Γ .point)
    (G : Point d → Point d) (input : Inputs d C) (env : Env d Γ)
    (tape : Tape d (body cfg direct outputDirect)) :
    let finisher := fun {Δ : Ctx} (old _ : Fin n → Ref Δ .point)
      (saved : RefMap Γ Δ) => finish cfg old (saved outputDirect)
    let Z : Fin n → Point d := fun i => (tape.1 i).1
    let initialEnv : Env d (replyCtx n (replyCtx n Γ)) := Env.prepend
      (fun j => storedPoint env (direct j) + input.coefficient cfg.noise • Z j)
      (Env.prepend Z env)
    let state := finalState c p cfg.mainSlots cfg.mainEquiv cfg.layerOrigin
      cfg.mainDesignated cfg.mainResidual cfg.mainAuxiliary finisher G input cfg.layers
      batchRef (fun i => RefMap.shiftMany n (RefMap.shiftMany n (direct i)))
      (fun r => RefMap.shiftMany n (RefMap.shiftMany n r)) initialEnv tape.2.2
    let children := fun i => run
      (freshChild (pf i) (cfg.finalEquiv i) (cfg.finalSlots i) (state.old i)
        (cfg.finalDesignated i) (cfg.finalAuxiliary i)) G input state.env (state.tape.1 i)
    (run (body cfg direct outputDirect) G input env tape).value =
      storedPoint env outputDirect +
      (∑ i, input.coefficient (cfg.rowWeight i) • pointValue (children i)) +
      (input.coefficient cfg.beta • gaussianValue state.tape.2.1 +
        input.coefficient cfg.reserve • gaussianValue state.tape.2.2.1) := by
  dsimp only
  dsimp only [body] at tape ⊢
  rw [run_initialize, run_iterateThen_value]
  dsimp only [finish]
  erw [PrivateSamplingFinal.run_code]
  simp only [finalState_saved]
  let Z : Fin n → Point d := fun i => (tape.1 i).1
  let X : Fin n → Point d := fun j =>
    storedPoint env (direct j) + input.coefficient cfg.noise • Z j
  have hs (r : Ref Γ .point) :
      storedPoint (Env.prepend X (Env.prepend Z env))
        (RefMap.shiftMany n (RefMap.shiftMany n r)) = storedPoint env r :=
    (prepend_shiftMany X (Env.prepend Z env) (RefMap.shiftMany n r)).trans
      (prepend_shiftMany Z env r)
  dsimp only [X, Z] at hs
  simp only [hs]

/-- The complete setup store contains only the actual supplied x, the fresh Y₀,
and their literal arithmetic outputs. -/
def setupEnv {c cf : Fin n → ℕ} {p : ∀ i, Program (c i) .point}
    {pf : ∀ i, Program (cf i) .point} (cfg : Config n C c cf p pf)
    (input : Inputs d C) (Y₀ : Point d) :
    Env d (replyCtx n [.point,.scalar,.point,.point]) :=
  Env.prepend (fun i => input.center + input.coefficient (cfg.directWeight i) • Y₀)
    (Env.cons (d := d) (τ := .point) (input.coefficient cfg.invEnd • Y₀)
      (Env.cons (d := d) (τ := .scalar) (input.coefficient cfg.invEnd) (Env.cons (d := d) (τ := .point) Y₀
        (Env.cons (d := d) (τ := .point) input.center Env.empty))))

theorem setupEnv_direct {c cf : Fin n → ℕ} {p : ∀ i, Program (c i) .point}
    {pf : ∀ i, Program (cf i) .point} (cfg : Config n C c cf p pf)
    (input : Inputs d C) (Y₀ : Point d) (i : Fin n) :
    storedPoint (setupEnv cfg input Y₀) (batchRef i) =
      input.center + input.coefficient (cfg.directWeight i) • Y₀ :=
  prepend_batchRef _ _ i

set_option backward.isDefEq.respectTransparency false in
theorem setupEnv_output {c cf : Fin n → ℕ} {p : ∀ i, Program (c i) .point}
    {pf : ∀ i, Program (cf i) .point} (cfg : Config n C c cf p pf)
    (input : Inputs d C) (Y₀ : Point d) :
    storedPoint (setupEnv cfg input Y₀) (RefMap.shiftMany n .here) =
      input.coefficient cfg.invEnd • Y₀ := by
  exact prepend_shiftMany _ _ Ref.here

set_option backward.isDefEq.respectTransparency false in
/-- Exact Result correspondence for the executed setup, including the position
anchor draw and the continuation trace. The momentum input is never read. -/
theorem run_code_setup {c cf : Fin n → ℕ} {p : ∀ i, Program (c i) .point}
    {pf : ∀ i, Program (cf i) .point} (cfg : Config n C c cf p pf)
    (G : Point d → Point d) (input : Inputs d C) (tape : Tape d (code cfg)) :
    let Y₀ : Point d := tape.2.1
    let tail := run (body cfg batchRef (RefMap.shiftMany n .here)) G input
      (setupEnv cfg input Y₀) tape.2.2.2.2.2
    run (code cfg) G input Env.empty tape =
      ⟨tail.value, Event.gaussian cfg.positionOrigin :: tail.trace⟩ := by
  dsimp only
  dsimp only [code] at tape ⊢
  rcases tape with ⟨⟨⟩, Y₀, ⟨⟩, ⟨⟩, rows, tail⟩
  change Point d at Y₀
  dsimp only [run,evalInstr,evalPure]
  simp only [Env.cons_here, Env.cons_there]
  have hrow (i : Fin n) := run_affineRow []
    (Ref.there (Ref.there (Ref.there Ref.here)))
    [(cfg.directWeight i, Ref.there (Ref.there Ref.here))] G input
    (Env.cons (d := d) (τ := .point) (input.coefficient cfg.invEnd • Y₀)
      (Env.cons (d := d) (τ := .scalar) (input.coefficient cfg.invEnd)
        (Env.cons (d := d) (τ := .point) Y₀ (Env.cons (d := d) (τ := .point) input.center Env.empty)))) (rows i)
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
    storedPoint,Env.cons_there,Env.cons_here] at hrow
  simp only [hrow,pointResult,List.ofFn_const,List.flatten_replicate_nil,
    List.nil_append,prefix_nil]
  rfl

end AcceleratedLogConcave.Oracle.PrivateSamplingProgram
