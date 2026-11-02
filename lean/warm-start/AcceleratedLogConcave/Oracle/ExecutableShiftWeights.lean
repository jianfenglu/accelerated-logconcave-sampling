import AcceleratedLogConcave.Oracle.LayerShift
import AcceleratedLogConcave.Oracle.RecursiveMeanContinuation

/-! Structural Gaussian-slot routing for actual executable compiler blocks.
Weights are attached to source syntax positions, including every occurrence of
an equal-code child. Lowering deletes only deterministic input reads; it never
introduces a new Gaussian slot. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.ExecutableShiftWeights
open TapeLowering AffineLowering NoisyLayer

/-- The literal source Gaussian position corresponding to a lowered position. -/
def lowerSlot (κ : Fin c → Fin c') (p : Prog c Γ τ) (f : RefMap Γ Δ)
    (center momentum : Ref Δ .point) :
    GaussianSlot (p.lower κ f center momentum) → GaussianSlot p :=
  match p with
  | .ret _ => fun s => nomatch s
  | .step _ (.pure _) next => fun s => match s with
    | .inl t => nomatch t
    | .inr t => .inr (lowerSlot κ next f.lift (.there center) (.there momentum) t)
  | .step _ .center next => fun s => .inr (lowerSlot κ next (f.bind center) center momentum s)
  | .step _ .momentum next => fun s => .inr (lowerSlot κ next (f.bind momentum) center momentum s)
  | .step _ (.grad _) next => fun s => match s with
    | .inl t => nomatch t
    | .inr t => .inr (lowerSlot κ next f.lift (.there center) (.there momentum) t)
  | .step _ .gaussian next => fun s => match s with
    | .inl t => .inl t
    | .inr t => .inr (lowerSlot κ next f.lift (.there center) (.there momentum) t)
  | .step _ .uniform next => fun s => match s with
    | .inl t => nomatch t
    | .inr t => .inr (lowerSlot κ next f.lift (.there center) (.there momentum) t)
  | .batch _ children next => fun s => match s with
    | .inl ⟨j,t⟩ => .inl ⟨j,lowerSlot κ (children j) f center momentum t⟩
    | .inr t => .inr (lowerSlot κ next (f.liftMany _) (RefMap.shiftMany _ center)
        (RefMap.shiftMany _ momentum) t)

/-- Transport actual source weights to its coefficient/reference lowering. -/
def lowerWeights (κ : Fin c → Fin c') (p : Prog c Γ τ) (f : RefMap Γ Δ)
    (center momentum : Ref Δ .point) (w : GaussianSlot p → ℝ) :
    GaussianSlot (p.lower κ f center momentum) → ℝ :=
  w ∘ lowerSlot κ p f center momentum

/-- A compiler raw block has its supplied weight; replay and pure rows get zero.
The replay has no Gaussian instructions, but assigning zero there also makes
this definition independent of a cardinality or emptiness transport. -/
def compiledWeights (p : Program c τ) (e : GaussianSlot p ≃ Fin N)
    (auxiliary : Fin N → Origin) (w : Fin N → ℝ) :
    GaussianSlot (compileWith p e auxiliary) → ℝ
  | .inr (.inr (.inl ⟨j,.inl _⟩)) => w j
  | _ => 0

/-- Main/final fresh children hold their new designated Gaussian fixed. -/
def freshWeights (p : Program c .point) (e : GaussianSlot p ≃ Fin N)
    (slots : Fin (N*N+c) → Fin C) (old : Ref Γ .point)
    (designated : Origin) (auxiliary : Fin N → Origin) (w : Fin N → ℝ) :
    GaussianSlot (freshChild p e slots old designated auxiliary) → ℝ :=
  Sum.elim (fun _ => 0)
    (lowerWeights slots (compileWith p e auxiliary) (fun r => nomatch r)
      (.there old) .here (compiledWeights p e auxiliary w))

/-- Literal layer weights: fresh designated and center-residual blocks stay fixed;
only each child compiler's raw auxiliary batch and the continuation can move. -/
def layerWeights (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (slots : Fin (publicSize c p) → Fin C)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (old direct : Fin n → Ref Γ .point) (outer : Origin)
    (designated residual : Fin n → Origin)
    (auxiliary : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (next : Prog C (nextCtx n Γ) τ)
    (w : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (tail : GaussianSlot next → ℝ) :
    GaussianSlot (SourceMeanLayer.layerAt c p slots e old direct outer designated residual auxiliary next) → ℝ :=
  Sum.elim (fun s => freshWeights (p s.1) (e s.1) (slots ∘ childSlot c p s.1)
      (old s.1) (designated s.1) (auxiliary s.1) (w s.1) s.2)
    (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) tail))

/-- Initial center residuals are held fixed, exactly as in the source shift. -/
def initializeWeights (rho : Fin C) (direct : Fin n → Ref Γ .point)
    (outer : Origin) (origin : Fin n → Origin)
    (next : Prog C (noiseCtx n Γ) τ) (tail : GaussianSlot next → ℝ) :
    GaussianSlot (initializeCenters rho direct outer origin next) → ℝ :=
  Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) tail)

/-- Finite synchronous layers retain separate raw weights at every occurrence. -/
def iterateWeights (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (slots : Fin (publicSize c p) → Fin C)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (outer : ℕ → Origin) (designated residual : ℕ → Fin n → Origin)
    (auxiliary : ℕ → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (finish : ∀ {Δ : Ctx}, (Fin n → Ref Δ .point) →
      (Fin n → Ref Δ .point) → RefMap Ξ Δ → Prog C Δ τ)
    (w : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (finishWeights : ∀ {Δ : Ctx} (old direct : Fin n → Ref Δ .point) (saved : RefMap Ξ Δ),
      GaussianSlot (finish old direct saved) → ℝ) :
    (N : ℕ) → {Γ : Ctx} → (old direct : Fin n → Ref Γ .point) → (saved : RefMap Ξ Γ) →
      GaussianSlot (RecursiveMeanContinuation.iterateThen c p slots e outer designated
        residual auxiliary finish N old direct saved) → ℝ
  | 0, _, old, direct, saved => finishWeights old direct saved
  | N+1, _, old, direct, saved =>
      layerWeights c p slots e old direct (outer N) (designated N) (residual N) (auxiliary N)
        _ w (iterateWeights c p slots e outer designated residual auxiliary finish w finishWeights
          N batchRef (fun j => RecursiveMeanProgram.preserveDirect (direct j))
          (fun r => RecursiveMeanProgram.preserveDirect (saved r)))

def translateInstr (i : Instr c Γ τ) (w : InstrGaussianSlot i → ℝ) (r : ℝ)
    (Δ : Point d) (tape : Instr.Tape d i) : Instr.Tape d i :=
  match i with
  | .gaussian => (show Point d from tape) + (w PUnit.unit/r) • Δ
  | .pure _ | .center | .momentum | .grad _ | .uniform => tape

/-- Literal translation of every Gaussian instruction; uniform/unit data survive. -/
def translate (p : Prog c Γ τ) (w : GaussianSlot p → ℝ) (r : ℝ)
    (Δ : Point d) (tape : Tape d p) : Tape d p :=
  match p with
  | .ret _ => tape
  | .step _ i next =>
      (translateInstr i (fun s => w (.inl s)) r Δ tape.1,
        translate next (fun s => w (.inr s)) r Δ tape.2)
  | .batch _ children next =>
      ((fun j => translate (children j) (fun s => w (.inl ⟨j,s⟩)) r Δ (tape.1 j)),
        translate next (fun s => w (.inr s)) r Δ tape.2)

/-- Structural translation is exactly the Gaussian-slot shift used by QueryShift. -/
theorem translate_joinTape (p : Prog c Γ τ) (w : GaussianSlot p → ℝ)
    (r : ℝ) (Δ : Point d) (z : GaussianSlot p → Point d) (rest : ResidualTape p) :
    translate p w r Δ (joinTape p z rest) =
      joinTape p (fun s => z s + (w s/r) • Δ) rest := by
  induction p with
  | ret a => rfl
  | step origin instr next ih =>
      cases instr <;> simp only [translate,translateInstr,joinTape,ih] <;> rfl
  | batch origin children next ihc ihn =>
      simp only [translate,joinTape,ihc,ihn]
      rfl

/-- Lowering commutes with the actual Gaussian translation, including all
removed deterministic input reads and every residual coordinate. -/
theorem lowerTape_translate (κ : Fin c → Fin c') (p : Prog c Γ τ)
    (f : RefMap Γ Ξ) (center momentum : Ref Ξ .point)
    (w : GaussianSlot p → ℝ) (r : ℝ) (Δ : Point d) (tape : Tape d p) :
    lowerTape κ p f center momentum (translate p w r Δ tape) =
      translate (p.lower κ f center momentum)
        (lowerWeights κ p f center momentum w) r Δ
        (lowerTape κ p f center momentum tape) := by
  induction p generalizing Ξ with
  | ret a => rfl
  | step origin instr next ih =>
      cases instr <;> simp only [Prog.lower,lowerTape,translate,lowerWeights,
        Function.comp_def,lowerSlot,translateInstr,ih] <;> rfl
  | batch origin children next ihc ihn =>
      simp only [Prog.lower,lowerTape,translate,lowerWeights,Function.comp_def,
        lowerSlot,ihc,ihn]
      rfl

end AcceleratedLogConcave.Oracle.ExecutableShiftWeights
