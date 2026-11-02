import AcceleratedLogConcave.Oracle.NoisyLayer

/-! The paid sampling-only final row: all fresh mean suppliers, one residual,
and a separate reserve. The direct term is an already computed Y₀/ρₑ. -/
namespace AcceleratedLogConcave.Oracle.PrivateSamplingFinal
open AffineLowering TapeLowering NoisyLayer
open scoped BigOperators

def pointValue (v : Result d .point) : Point d := v.value
def gaussianValue (v : Instr.Tape d (Instr.gaussian (c := C) (Γ := Γ))) : Point d := v

def code (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (slots : ∀ i, Fin (childSize (p i)) → Fin C)
    (weight : Fin n → Fin C) (beta reserve : Fin C)
    (old : Fin n → Ref Γ .point) (direct : Ref Γ .point)
    (outer : Origin) (designated : Fin n → Origin)
    (auxiliary : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (residualOrigin reserveOrigin : Origin) : Prog C Γ .point :=
  .batch outer (fun i => freshChild (p i) (e i) (slots i) (old i)
      (designated i) (auxiliary i))
    (.step residualOrigin .gaussian
      (.step reserveOrigin .gaussian
        (affineRow [] (.there (.there (RefMap.shiftMany n direct)))
          ((List.ofFn fun i => (weight i, .there (.there (batchRef i)))) ++
            [(beta,.there .here),(reserve,.here)]))))

theorem syntaxCount_code (kind : EventKind)
    (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (slots : ∀ i, Fin (childSize (p i)) → Fin C)
    (weight : Fin n → Fin C) (beta reserve : Fin C)
    (old : Fin n → Ref Γ .point) (direct : Ref Γ .point)
    (outer : Origin) (designated : Fin n → Origin)
    (auxiliary : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (residualOrigin reserveOrigin : Origin) :
    syntaxCount kind (code c p e slots weight beta reserve old direct outer designated
      auxiliary residualOrigin reserveOrigin) =
      (if kind = .gaussian then n + ∑ i, (tapeShape (p i)).gaussianBlocks
        else ∑ i, syntaxCount kind (p i)) + (if kind = .gaussian then 2 else 0) := by
  simp only [code, syntaxCount, syntaxCount_freshChild, syntaxCount_affineRow]
  cases kind <;> simp [instructionCount, Instr.eventKind, Fin.sum_ofFn,
    Finset.sum_add_distrib, Nat.add_comm, Nat.add_left_comm]

set_option backward.isDefEq.respectTransparency false in
/-- Exact Result identity on every tape; both final Gaussian occurrences survive
in the trace even when their coefficients vanish. -/
theorem run_code (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (slots : ∀ i, Fin (childSize (p i)) → Fin C)
    (weight : Fin n → Fin C) (beta reserve : Fin C)
    (old : Fin n → Ref Γ .point) (direct : Ref Γ .point)
    (outer : Origin) (designated : Fin n → Origin)
    (auxiliary : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (residualOrigin reserveOrigin : Origin)
    (G : Point d → Point d) (input : Inputs d C) (env : Env d Γ)
    (tape : Tape d (code c p e slots weight beta reserve old direct outer designated
      auxiliary residualOrigin reserveOrigin)) :
    let children := fun i => run (freshChild (p i) (e i) (slots i) (old i)
      (designated i) (auxiliary i)) G input env (tape.1 i)
    run (code c p e slots weight beta reserve old direct outer designated auxiliary
      residualOrigin reserveOrigin) G input env tape =
      ⟨storedPoint env direct + (∑ i, input.coefficient (weight i) • pointValue (children i)) +
          (input.coefficient beta • gaussianValue tape.2.1 + input.coefficient reserve • gaussianValue tape.2.2.1),
        ((List.ofFn fun i => (children i).trace).flatten ++
          [Event.gaussian residualOrigin, Event.gaussian reserveOrigin]).map
          (Event.withPrefix outer)⟩ := by
  dsimp only
  dsimp only [code] at tape ⊢
  rcases tape with ⟨childTape, Z, W, rowTape⟩
  change Point d at Z W
  dsimp only [run,evalInstr]
  rw [run_affineRow]
  simp only [List.map_append, List.sum_append, List.map_ofFn, Function.comp_def,
    Fin.sum_ofFn, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    storedPoint, pointResult,
    List.append_nil]
  simp only [Env.cons_there, Env.cons_here, prepend_shiftMany,
    pointValue, gaussianValue, List.singleton_append]
  rw [add_assoc]
  congr 1
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact prepend_batchRef _ env i

end AcceleratedLogConcave.Oracle.PrivateSamplingFinal
