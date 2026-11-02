import AcceleratedLogConcave.Oracle.TapeLowering
import Mathlib.Algebra.BigOperators.Fin

/-! Closed synchronous Gaussian setup with literal public tables.
Covariance construction and probability laws are separate obligations. -/
namespace AcceleratedLogConcave.Oracle.NoisyLayer
open TapeLowering AffineLowering
open scoped BigOperators

/-- The exact auxiliary matrix plus original coefficient table width of a child. -/
abbrev childSize (p : Program c .point) : ℕ :=
  (tapeShape p).gaussianBlocks * (tapeShape p).gaussianBlocks + c

/-- Two literal square matrices followed by all child public tables. -/
def publicSize (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point) : ℕ :=
  n*n + (n*n + ∑ i, childSize (p i))

def aSlot (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point) (j k : Fin n) :
    Fin (publicSize c p) := Fin.castAdd _ (finProdFinEquiv (j,k))

def residualSlot (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point) (j k : Fin n) :
    Fin (publicSize c p) := Fin.natAdd (n*n) (Fin.castAdd _ (finProdFinEquiv (j,k)))

def childSlot (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point) (i : Fin n)
    (k : Fin (childSize (p i))) : Fin (publicSize c p) :=
  Fin.natAdd (n*n) (Fin.natAdd (n*n) (finSigmaFinEquiv ⟨i,k⟩))

/-- Matrix and child values are public inputs; the slot layout contains no oracle. -/
def layerTable (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (A C : Fin n → Fin n → ℝ)
    (T : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (coeff : ∀ i, Fin (c i) → ℝ) : Fin (publicSize c p) → ℝ :=
  Fin.append (fun k => A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
    (Fin.append (fun k => C (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
      (fun k => let pair := finSigmaFinEquiv.symm k
                matrixTable (T pair.1) (coeff pair.1) pair.2))

@[simp] theorem layerTable_a (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (A C : Fin n → Fin n → ℝ) (T : ∀ i, Fin (tapeShape (p i)).gaussianBlocks →
      Fin (tapeShape (p i)).gaussianBlocks → ℝ) (coeff : ∀ i, Fin (c i) → ℝ)
    (j k : Fin n) : layerTable c p A C T coeff (aSlot c p j k) = A j k := by
  simp only [layerTable,aSlot,Fin.append_left,Equiv.symm_apply_apply]

@[simp] theorem layerTable_residual (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (A C : Fin n → Fin n → ℝ) (T : ∀ i, Fin (tapeShape (p i)).gaussianBlocks →
      Fin (tapeShape (p i)).gaussianBlocks → ℝ) (coeff : ∀ i, Fin (c i) → ℝ)
    (j k : Fin n) : layerTable c p A C T coeff (residualSlot c p j k) = C j k := by
  simp only [layerTable,residualSlot,Fin.append_right,Fin.append_left,Equiv.symm_apply_apply]

@[simp] theorem layerTable_child (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (A C : Fin n → Fin n → ℝ) (T : ∀ i, Fin (tapeShape (p i)).gaussianBlocks →
      Fin (tapeShape (p i)).gaussianBlocks → ℝ) (coeff : ∀ i, Fin (c i) → ℝ)
    (i : Fin n) (k : Fin (childSize (p i))) :
    layerTable c p A C T coeff (childSlot c p i k) = matrixTable (T i) (coeff i) k := by
  simp only [layerTable,childSlot,Fin.append_right]
  erw [Equiv.symm_apply_apply]

/-- The original coefficient is after its child's complete auxiliary matrix. -/
theorem layerTable_original (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (A C : Fin n → Fin n → ℝ) (T : ∀ i, Fin (tapeShape (p i)).gaussianBlocks →
      Fin (tapeShape (p i)).gaussianBlocks → ℝ) (coeff : ∀ i, Fin (c i) → ℝ)
    (i : Fin n) (k : Fin (c i)) :
    layerTable c p A C T coeff (childSlot c p i
      (Fin.natAdd ((tapeShape (p i)).gaussianBlocks * (tapeShape (p i)).gaussianBlocks) k)) =
      coeff i k := by
  erw [layerTable_child,matrixTable_extra]


/-- One new designated input, followed by the actual auxiliary-tape compiler. -/
def freshChild (p : Program c .point) (e : GaussianSlot p ≃ Fin N)
    (κ : Fin (N*N+c) → Fin c') (old : Ref Γ .point)
    (designated : Origin) (auxiliary : Fin N → Origin) : Prog c' Γ .point :=
  .step designated .gaussian
    ((compileWith p e auxiliary).embed κ (.there old) .here)

/-- Every raw execution coordinate is represented, even under singular transforms. -/
def freshChildTapeEquiv (p : Program c .point) (e : GaussianSlot p ≃ Fin N)
    (κ : Fin (N*N+c) → Fin c') (old : Ref Γ .point)
    (designated : Origin) (auxiliary : Fin N → Origin) :
    Tape d (freshChild p e κ old designated auxiliary) ≃
      (Point d × ((Fin N → Point d) × ResidualTape p)) :=
  Equiv.prodCongr (Equiv.refl _)
    ((lowerTapeEquiv κ (compileWith p e auxiliary) (fun a => nomatch a)
      (.there old) .here).symm.trans (compiledTapeEquivWith p e auxiliary))

/-- Literal full execution at a stored old center and freshly sampled momentum. -/
theorem run_freshChild (p : Program c .point) (e : GaussianSlot p ≃ Fin N)
    (κ : Fin (N*N+c) → Fin c') (old : Ref Γ .point)
    (designated : Origin) (auxiliary : Fin N → Origin)
    (T : Fin N → Fin N → ℝ) (coeff : Fin c → ℝ)
    (G : Point d → Point d) (input : Inputs d c') (ρ : Env d Γ)
    (htable : input.coefficient ∘ κ = matrixTable T coeff)
    (ω : Tape d (freshChild p e κ old designated auxiliary)) :
    let data := freshChildTapeEquiv p e κ old designated auxiliary ω
    let source := run p G ⟨coeff,storedPoint ρ old,data.1⟩ Env.empty
      (transformedSourceTape p e T data.2.1 data.2.2)
    run (freshChild p e κ old designated auxiliary) G input ρ ω =
      ⟨source.value, [Event.gaussian designated] ++
        List.ofFn (fun j => Event.gaussian (auxiliary j)) ++
        source.trace.filter keepNonGaussian⟩ := by
  dsimp only [freshChild,run,evalInstr]
  rw [run_embed_every_tape]
  simp only [htable]
  change (let result := AcceleratedLogConcave.Oracle.run (compileWith p e auxiliary) G
                         (matrixInputs T coeff (storedPoint ρ old) ω.1) Env.empty
                         (restoreTape κ (compileWith p e auxiliary) (fun a => nomatch a)
                           (.there old) .here ω.2)
          (⟨result.value, [Event.gaussian designated] ++ result.trace⟩ : Result d .point)) = _
  erw [run_compileWith_every_tape]
  rfl

/-- All actual raw blocks are charged, including the designated input. -/
theorem syntaxCount_freshChild (kind : EventKind) (p : Program c .point)
    (e : GaussianSlot p ≃ Fin N) (κ : Fin (N*N+c) → Fin c')
    (old : Ref Γ .point) (designated : Origin) (auxiliary : Fin N → Origin) :
    syntaxCount kind (freshChild p e κ old designated auxiliary) =
      if kind = .gaussian then 1+N else syntaxCount kind p := by
  cases kind <;> simp [freshChild,syntaxCount,Program.embed,syntaxCount_lower,
    instructionCount,Instr.eventKind,syntaxCount_compileWith,Nat.add_comm]


abbrev replyCtx (n : ℕ) (Γ : Ctx) := List.replicate n Ty.point ++ Γ
abbrev noiseCtx (n : ℕ) (Γ : Ctx) := replyCtx n (replyCtx n Γ)
abbrev nextCtx (n : ℕ) (Γ : Ctx) := replyCtx n (noiseCtx n Γ)

/-- Residual blocks are separate actual instructions, independent of their values. -/
def residualDraw (origin : Origin) : Prog c Γ .point :=
  .step origin .gaussian (.ret .here)

def noisyTerms (aSlot cSlot : Fin n → Fin n → Fin c) (j : Fin n) :
    List (Fin c × Ref (noiseCtx n Γ) .point) :=
  (List.ofFn fun k => (aSlot j k, RefMap.shiftMany n (batchRef k))) ++
  (List.ofFn fun k => (cSlot j k, batchRef k))

/-- One row uses the same already stored reply and residual arrays. -/
def noisyRow (aSlot cSlot : Fin n → Fin n → Fin c)
    (direct : Fin n → Ref Γ .point) (j : Fin n) : Prog c (noiseCtx n Γ) .point :=
  affineRow [] (RefMap.shiftMany n (RefMap.shiftMany n (direct j)))
    (noisyTerms aSlot cSlot j)

noncomputable def noisyValues (aSlot cSlot : Fin n → Fin n → Fin c)
    (direct : Fin n → Ref Γ .point) (input : Inputs d c) (ρ : Env d Γ)
    (Q Z : Fin n → Point d) (j : Fin n) : Point d :=
  storedPoint ρ (direct j) + (∑ k, input.coefficient (aSlot j k) • Q k) +
    ∑ k, input.coefficient (cSlot j k) • Z k

theorem run_noisyRow (aSlot cSlot : Fin n → Fin n → Fin c)
    (direct : Fin n → Ref Γ .point) (j : Fin n)
    (G : Point d → Point d) (input : Inputs d c) (ρ : Env d Γ)
    (Q Z : Fin n → Point d) (ω : Tape d (noisyRow aSlot cSlot direct j)) :
    run (noisyRow aSlot cSlot direct j) G input (Env.prepend Z (Env.prepend Q ρ)) ω =
      pointResult (noisyValues aSlot cSlot direct input ρ Q Z j) [] := by
  unfold noisyRow
  erw [run_affineRow]
  simp only [noisyTerms,List.map_append,List.sum_append,List.map_ofFn,
    Function.comp_def,Fin.sum_ofFn,noisyValues]
  have h (r : Ref (replyCtx n Γ) .point) :
      storedPoint (Env.prepend Z (Env.prepend Q ρ)) (RefMap.shiftMany n r) =
        storedPoint (Env.prepend Q ρ) r := prepend_shiftMany Z (Env.prepend Q ρ) r
  rw [h]
  simp only [h,prepend_batchRef]
  rw [show storedPoint (Env.prepend Q ρ) (RefMap.shiftMany n (direct j)) =
    storedPoint ρ (direct j) from prepend_shiftMany Q ρ (direct j)]
  rw [add_assoc]

theorem syntaxCount_noisyRow (kind : EventKind)
    (aSlot cSlot : Fin n → Fin n → Fin c) (direct : Fin n → Ref Γ .point) (j : Fin n) :
    syntaxCount kind (noisyRow aSlot cSlot direct j) = 0 :=
  syntaxCount_affineRow kind [] _ _

/-- Actual closed child batch, residual batch, shared pure rows, and continuation. -/
def noisyLayer (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (old direct : Fin n → Ref Γ .point) (outer : Origin)
    (designated residual : Fin n → Origin)
    (auxiliary : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (next : Prog (publicSize c p) (nextCtx n Γ) τ) : Prog (publicSize c p) Γ τ :=
  .batch outer (fun i => freshChild (p i) (e i) (childSlot c p i) (old i)
    (designated i) (auxiliary i))
    (.batch [] (fun i => residualDraw (residual i))
      (.batch [] (noisyRow (aSlot c p) (residualSlot c p) direct) next))


private theorem flatten_ofFn_singleton (f : Fin n → α) :
    (List.ofFn (fun j => [f j])).flatten = List.ofFn f := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.ofFn_succ,List.flatten_cons,List.singleton_append,ih]

/-- The residual and row stage contains no child evaluator. -/
def finishLayer (aSlot cSlot : Fin n → Fin n → Fin c)
    (direct : Fin n → Ref Γ .point) (residual : Fin n → Origin)
    (next : Prog c (nextCtx n Γ) τ) : Prog c (replyCtx n Γ) τ :=
  .batch [] (fun i => residualDraw (residual i))
    (.batch [] (noisyRow aSlot cSlot direct) next)

theorem run_finishLayer (aSlot cSlot : Fin n → Fin n → Fin c)
    (direct : Fin n → Ref Γ .point) (residual : Fin n → Origin)
    (next : Prog c (nextCtx n Γ) τ) (G : Point d → Point d)
    (input : Inputs d c) (ρ : Env d Γ) (Q : Fin n → Point d)
    (ω : Tape d (finishLayer aSlot cSlot direct residual next)) :
    let Z : Fin n → Point d := fun j => (ω.1 j).1
    let tail := run next G input
      (Env.prepend (noisyValues aSlot cSlot direct input ρ Q Z)
        (Env.prepend Z (Env.prepend Q ρ))) ω.2.2
    run (finishLayer aSlot cSlot direct residual next) G input (Env.prepend Q ρ) ω =
      ⟨tail.value,List.ofFn (fun j => Event.gaussian (residual j)) ++ tail.trace⟩ := by
  simp only [finishLayer,run,residualDraw,evalInstr,List.append_nil,
    prefix_nil,flatten_ofFn_singleton]
  change (let rows := fun j => run (noisyRow aSlot cSlot direct j) G input
                            (Env.prepend (fun k => (ω.1 k).1) (Env.prepend Q ρ)) (ω.2.1 j)
          let tail := run next G input (Env.prepend (fun j => (rows j).value)
                        (Env.prepend (fun k => (ω.1 k).1) (Env.prepend Q ρ))) ω.2.2
          (⟨tail.value, List.ofFn (fun j => Event.gaussian (residual j)) ++
            ((List.ofFn (fun j => (rows j).trace)).flatten ++ tail.trace)⟩ : Result d τ)) = _
  have hrow (j : Fin n) := run_noisyRow aSlot cSlot direct j G input ρ Q
    (fun k => (ω.1 k).1) (ω.2.1 j)
  simp only [hrow,pointResult,List.ofFn_const,List.flatten_replicate_nil,List.nil_append]

/-- Full provenance includes the continuation under the outer batch prefix. -/
theorem run_noisyLayer (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (old direct : Fin n → Ref Γ .point) (outer : Origin)
    (designated residual : Fin n → Origin)
    (auxiliary : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (next : Prog (publicSize c p) (nextCtx n Γ) τ)
    (G : Point d → Point d) (input : Inputs d (publicSize c p)) (ρ : Env d Γ)
    (ω : Tape d (noisyLayer c p e old direct outer designated residual auxiliary next)) :
    let children := fun i => run
      (freshChild (p i) (e i) (childSlot c p i) (old i) (designated i) (auxiliary i))
      G input ρ (ω.1 i)
    let Q : Fin n → Point d := fun i => (children i).value
    let Z : Fin n → Point d := fun j => (ω.2.1 j).1
    let tail := run next G input
      (Env.prepend (noisyValues (aSlot c p) (residualSlot c p) direct input ρ Q Z)
        (Env.prepend Z (Env.prepend Q ρ))) ω.2.2.2
    run (noisyLayer c p e old direct outer designated residual auxiliary next) G input ρ ω =
      ⟨tail.value, ((List.ofFn (fun j => (children j).trace)).flatten ++
        List.ofFn (fun j => Event.gaussian (residual j)) ++ tail.trace).map
          (Event.withPrefix outer)⟩ := by
  change (let children := fun i => run
                             (freshChild (p i) (e i) (childSlot c p i) (old i)
                               (designated i) (auxiliary i)) G input ρ (ω.1 i)
          let tail := run (finishLayer (aSlot c p) (residualSlot c p) direct residual next)
                        G input (Env.prepend (fun i => (children i).value) ρ) ω.2
          (⟨tail.value, ((List.ofFn (fun i => (children i).trace)).flatten ++ tail.trace).map
            (Event.withPrefix outer)⟩ : Result d τ)) = _
  dsimp only
  have h := run_finishLayer (aSlot c p) (residualSlot c p) direct residual next G input ρ
    (fun i => (run (freshChild (p i) (e i) (childSlot c p i) (old i)
      (designated i) (auxiliary i)) G input ρ (ω.1 i)).value) ω.2
  erw [h]
  simp only [List.append_assoc]

/-- Literal numerical matrices, without a supplied lookup certificate. -/
theorem noisyValues_layerTable (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (A C : Fin n → Fin n → ℝ)
    (T : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (coeff : ∀ i, Fin (c i) → ℝ) (hostX hostP : Point d)
    (direct : Fin n → Ref Γ .point) (ρ : Env d Γ) (Q Z : Fin n → Point d) (j : Fin n) :
    noisyValues (aSlot c p) (residualSlot c p) direct
      ⟨layerTable c p A C T coeff,hostX,hostP⟩ ρ Q Z j =
      storedPoint ρ (direct j) + (∑ k, A j k • Q k) + ∑ k, C j k • Z k := by
  simp only [noisyValues,layerTable_a,layerTable_residual]

/-- Every block occurrence is charged irrespective of its numerical coefficient. -/
theorem syntaxCount_noisyLayer (kind : EventKind) (c : Fin n → ℕ)
    (p : ∀ i, Program (c i) .point)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (old direct : Fin n → Ref Γ .point) (outer : Origin)
    (designated residual : Fin n → Origin)
    (auxiliary : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (next : Prog (publicSize c p) (nextCtx n Γ) τ) :
    syntaxCount kind (noisyLayer c p e old direct outer designated residual auxiliary next) =
      (if kind = .gaussian then n + (∑ i, (tapeShape (p i)).gaussianBlocks) + n
        else ∑ i, syntaxCount kind (p i)) + syntaxCount kind next := by
  have hchild (i : Fin n) := syntaxCount_freshChild kind (p i) (e i)
    (childSlot c p i) (old i) (designated i) (auxiliary i)
  simp only [noisyLayer,syntaxCount,hchild,Fin.sum_ofFn]
  cases kind <;> simp [syntaxCount,syntaxCount_noisyRow,residualDraw,
    instructionCount,Instr.eventKind,Finset.sum_add_distrib,Nat.add_assoc]


section Routing
variable (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (old direct : Fin n → Ref Γ .point) (outer : Origin)
    (designated residual : Fin n → Origin)
    (auxiliary : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (next : Prog (publicSize c p) (nextCtx n Γ) τ)

/-- The explicit raw coordinate space includes all residual uniform coordinates. -/
abbrev LayerData (d : ℕ) :=
  (∀ i, Point d × ((Fin (tapeShape (p i)).gaussianBlocks → Point d) × ResidualTape (p i))) ×
    (Fin n → Point d) × Tape d next

def packLayerTape (data : LayerData c p next d) :
    Tape d (noisyLayer c p e old direct outer designated residual auxiliary next) :=
  ⟨(fun i => (freshChildTapeEquiv (p i) (e i) (childSlot c p i) (old i)
      (designated i) (auxiliary i)).symm (data.1 i)),
    (fun i => (data.2.1 i,PUnit.unit)),
    (fun j => rowTape d [] (noisyTerms (aSlot c p) (residualSlot c p) j)
      (fun a => a) (RefMap.shiftMany n (RefMap.shiftMany n (direct j)))),data.2.2⟩

def unpackLayerTape
    (ω : Tape d (noisyLayer c p e old direct outer designated residual auxiliary next)) :
    LayerData c p next d :=
  ⟨(fun i => freshChildTapeEquiv (p i) (e i) (childSlot c p i) (old i)
      (designated i) (auxiliary i) (ω.1 i)), (fun i => (ω.2.1 i).1),ω.2.2.2⟩

theorem unpack_packLayerTape (data : LayerData c p next d) :
    unpackLayerTape c p e old direct outer designated residual auxiliary next
      (packLayerTape c p e old direct outer designated residual auxiliary next data) = data := by
  simp only [unpackLayerTape,packLayerTape,Equiv.apply_symm_apply]

theorem pack_unpackLayerTape
    (ω : Tape d (noisyLayer c p e old direct outer designated residual auxiliary next)) :
    packLayerTape c p e old direct outer designated residual auxiliary next
      (unpackLayerTape c p e old direct outer designated residual auxiliary next ω) = ω := by
  rcases ω with ⟨children,draws,rows,tail⟩
  simp only [packLayerTape,unpackLayerTape,Equiv.symm_apply_apply]
  have hd : (fun i => ((draws i).1,PUnit.unit)) = draws := by
    funext i
    rcases draws i with ⟨z,⟨⟩⟩
    rfl
  have hr : (fun j => rowTape d [] (noisyTerms (aSlot c p) (residualSlot c p) j)
      (fun a => a) (RefMap.shiftMany n (RefMap.shiftMany n (direct j)))) = rows := by
    funext j
    exact (rowTape_unique [] _ (fun a => a) _ (rows j)).symm
  erw [hd,hr]

/-- This equivalence covers the complete target execution, not just child slices. -/
def layerTapeEquiv :
    Tape d (noisyLayer c p e old direct outer designated residual auxiliary next) ≃
      LayerData c p next d where
  toFun := unpackLayerTape c p e old direct outer designated residual auxiliary next
  invFun := packLayerTape c p e old direct outer designated residual auxiliary next
  left_inv := pack_unpackLayerTape c p e old direct outer designated residual auxiliary next
  right_inv := unpack_packLayerTape c p e old direct outer designated residual auxiliary next

/-- Actual executed counts follow for every tape through the interpreter theorem. -/
theorem executedCount_noisyLayer (kind : EventKind) (G : Point d → Point d)
    (input : Inputs d (publicSize c p)) (ρ : Env d Γ)
    (ω : Tape d (noisyLayer c p e old direct outer designated residual auxiliary next)) :
    shapeCount kind ((run (noisyLayer c p e old direct outer designated residual auxiliary next)
      G input ρ ω).trace.map Event.erase) =
      (if kind = .gaussian then n + (∑ i, (tapeShape (p i)).gaussianBlocks) + n
        else ∑ i, syntaxCount kind (p i)) + syntaxCount kind next := by
  rw [run_trace_shape,shapeCount_staticTrace,syntaxCount_noisyLayer]
end Routing


/-- Distinct matrix coordinates have distinct literal public slots. -/
theorem aSlot_injective (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point) :
    Function.Injective (fun jk : Fin n × Fin n => aSlot c p jk.1 jk.2) := by
  intro x y h
  apply finProdFinEquiv.injective
  apply Fin.ext
  have hv := congrArg (fun z : Fin (publicSize c p) => z.val) h
  exact hv

theorem residualSlot_injective (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point) :
    Function.Injective (fun jk : Fin n × Fin n => residualSlot c p jk.1 jk.2) := by
  intro x y h
  apply finProdFinEquiv.injective
  apply Fin.ext
  have hv := congrArg Fin.val h
  change n*n + (finProdFinEquiv x).val = n*n + (finProdFinEquiv y).val at hv
  omega

/-- Equal code at different child positions still receives disjoint coefficients. -/
theorem childSlot_injective (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point) :
    Function.Injective (fun s : Σ i, Fin (childSize (p i)) => childSlot c p s.1 s.2) := by
  intro x y h
  apply finSigmaFinEquiv.injective
  apply Fin.ext
  have hv := congrArg Fin.val h
  change n*n + (n*n + (finSigmaFinEquiv x).val) =
    n*n + (n*n + (finSigmaFinEquiv y).val) at hv
  omega

theorem aSlot_ne_residualSlot (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (j k l t : Fin n) : aSlot c p j k ≠ residualSlot c p l t := by
  intro h
  have hv := congrArg Fin.val h
  change (finProdFinEquiv (j,k)).val = n*n + (finProdFinEquiv (l,t)).val at hv
  have := (finProdFinEquiv (j,k)).isLt
  omega

theorem aSlot_ne_childSlot (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (j k i : Fin n) (t : Fin (childSize (p i))) : aSlot c p j k ≠ childSlot c p i t := by
  intro h
  have hv := congrArg Fin.val h
  change (finProdFinEquiv (j,k)).val = n*n + (n*n + (finSigmaFinEquiv (⟨i,t⟩ : Σ k, Fin (childSize (p k)))).val) at hv
  have := (finProdFinEquiv (j,k)).isLt
  omega

theorem residualSlot_ne_childSlot (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (j k i : Fin n) (t : Fin (childSize (p i))) : residualSlot c p j k ≠ childSlot c p i t := by
  intro h
  have hv := congrArg Fin.val h
  change n*n + (finProdFinEquiv (j,k)).val = n*n + (n*n + (finSigmaFinEquiv (⟨i,t⟩ : Σ k, Fin (childSize (p k)))).val) at hv
  have := (finProdFinEquiv (j,k)).isLt
  omega

/-- The literal child table supplies the compiler's matrix identity itself. -/
theorem run_layerChild (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (old : Fin n → Ref Γ .point) (designated : Fin n → Origin)
    (auxiliary : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (A C : Fin n → Fin n → ℝ)
    (T : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (coeff : ∀ i, Fin (c i) → ℝ) (hostX hostP : Point d) (G : Point d → Point d)
    (ρ : Env d Γ) (i : Fin n)
    (ω : Tape d (freshChild (p i) (e i) (childSlot c p i) (old i)
      (designated i) (auxiliary i))) :
    let data := freshChildTapeEquiv (p i) (e i) (childSlot c p i) (old i)
      (designated i) (auxiliary i) ω
    let source := run (p i) G ⟨coeff i,storedPoint ρ (old i),data.1⟩ Env.empty
      (transformedSourceTape (p i) (e i) (T i) data.2.1 data.2.2)
    run (freshChild (p i) (e i) (childSlot c p i) (old i) (designated i) (auxiliary i))
      G ⟨layerTable c p A C T coeff,hostX,hostP⟩ ρ ω =
      ⟨source.value,[Event.gaussian (designated i)] ++
        List.ofFn (fun j => Event.gaussian (auxiliary i j)) ++ source.trace.filter keepNonGaussian⟩ :=
  run_freshChild (p i) (e i) (childSlot c p i) (old i) (designated i) (auxiliary i)
    (T i) (coeff i) G ⟨layerTable c p A C T coeff,hostX,hostP⟩ ρ (funext (fun k => layerTable_child c p A C T coeff i k)) ω


/-- A literal one-term row for the separate initial center noise. -/
def initialRow (rho : Fin c) (direct : Fin n → Ref Γ .point) (j : Fin n) :
    Prog c (replyCtx n Γ) .point :=
  affineRow [] (RefMap.shiftMany n (direct j)) [(rho,batchRef j)]

/-- Initial centers pay for their own blocks before any noisy layer is executed. -/
def initializeCenters (rho : Fin c) (direct : Fin n → Ref Γ .point)
    (outer : Origin) (origin : Fin n → Origin)
    (next : Prog c (replyCtx n (replyCtx n Γ)) τ) : Prog c Γ τ :=
  .batch outer (fun j => residualDraw (origin j))
    (.batch [] (initialRow rho direct) next)

theorem run_initialRow (rho : Fin c) (direct : Fin n → Ref Γ .point) (j : Fin n)
    (G : Point d → Point d) (input : Inputs d c) (ρ : Env d Γ) (Z : Fin n → Point d)
    (ω : Tape d (initialRow rho direct j)) :
    run (initialRow rho direct j) G input (Env.prepend Z ρ) ω =
      pointResult (storedPoint ρ (direct j) + input.coefficient rho • Z j) [] := by
  unfold initialRow
  erw [run_affineRow]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,prepend_batchRef]
  rw [show storedPoint (Env.prepend Z ρ) (RefMap.shiftMany n (direct j)) =
    storedPoint ρ (direct j) from prepend_shiftMany Z ρ (direct j)]

theorem run_initialize (rho : Fin c) (direct : Fin n → Ref Γ .point)
    (outer : Origin) (origin : Fin n → Origin)
    (next : Prog c (replyCtx n (replyCtx n Γ)) τ)
    (G : Point d → Point d) (input : Inputs d c) (ρ : Env d Γ)
    (ω : Tape d (initializeCenters rho direct outer origin next)) :
    let Z : Fin n → Point d := fun j => (ω.1 j).1
    let tail := run next G input
      (Env.prepend (fun j => storedPoint ρ (direct j) + input.coefficient rho • Z j)
        (Env.prepend Z ρ)) ω.2.2
    run (initializeCenters rho direct outer origin next) G input ρ ω =
      ⟨tail.value,(List.ofFn (fun j => Event.gaussian (origin j)) ++ tail.trace).map
        (Event.withPrefix outer)⟩ := by
  simp only [initializeCenters,run,residualDraw,evalInstr,List.append_nil,prefix_nil,flatten_ofFn_singleton]
  change (let rows := fun j => run (initialRow rho direct j) G input
                            (Env.prepend (fun k => (ω.1 k).1) ρ) (ω.2.1 j)
          let tail := run next G input (Env.prepend (fun j => (rows j).value)
                        (Env.prepend (fun k => (ω.1 k).1) ρ)) ω.2.2
          (⟨tail.value,(List.ofFn (fun j => Event.gaussian (origin j)) ++
            ((List.ofFn (fun j => (rows j).trace)).flatten ++ tail.trace)).map
              (Event.withPrefix outer)⟩ : Result d τ)) = _
  have hrow (j : Fin n) := run_initialRow rho direct j G input ρ
    (fun k => (ω.1 k).1) (ω.2.1 j)
  simp only [hrow,pointResult,List.ofFn_const,List.flatten_replicate_nil,List.nil_append]

def packInitialTape (rho : Fin c) (direct : Fin n → Ref Γ .point)
    (outer : Origin) (origin : Fin n → Origin)
    (next : Prog c (replyCtx n (replyCtx n Γ)) τ)
    (data : (Fin n → Point d) × Tape d next) : Tape d (initializeCenters rho direct outer origin next) :=
  ⟨(fun j => (data.1 j,PUnit.unit)),
    (fun j => rowTape d [] [(rho,batchRef j)] (fun a => a) (RefMap.shiftMany n (direct j))),data.2⟩

def unpackInitialTape (rho : Fin c) (direct : Fin n → Ref Γ .point)
    (outer : Origin) (origin : Fin n → Origin)
    (next : Prog c (replyCtx n (replyCtx n Γ)) τ)
    (ω : Tape d (initializeCenters rho direct outer origin next)) : (Fin n → Point d) × Tape d next :=
  ⟨(fun j => (ω.1 j).1),ω.2.2⟩

theorem pack_unpackInitialTape (rho : Fin c) (direct : Fin n → Ref Γ .point)
    (outer : Origin) (origin : Fin n → Origin)
    (next : Prog c (replyCtx n (replyCtx n Γ)) τ)
    (ω : Tape d (initializeCenters rho direct outer origin next)) :
    packInitialTape rho direct outer origin next (unpackInitialTape rho direct outer origin next ω) = ω := by
  rcases ω with ⟨draws,rows,tail⟩
  simp only [packInitialTape,unpackInitialTape]
  have hd : (fun j => ((draws j).1,PUnit.unit)) = draws := by
    funext j
    rcases draws j with ⟨z,⟨⟩⟩
    rfl
  have hr : (fun j => rowTape d [] [(rho,batchRef j)] (fun a => a)
      (RefMap.shiftMany n (direct j))) = rows := by
    funext j
    exact (rowTape_unique [] _ (fun a => a) _ (rows j)).symm
  erw [hd,hr]

def initialTapeEquiv (rho : Fin c) (direct : Fin n → Ref Γ .point)
    (outer : Origin) (origin : Fin n → Origin)
    (next : Prog c (replyCtx n (replyCtx n Γ)) τ) :
    Tape d (initializeCenters rho direct outer origin next) ≃ ((Fin n → Point d) × Tape d next) where
  toFun := unpackInitialTape rho direct outer origin next
  invFun := packInitialTape rho direct outer origin next
  left_inv := pack_unpackInitialTape rho direct outer origin next
  right_inv := by intro data; rfl

theorem syntaxCount_initialize (kind : EventKind) (rho : Fin c)
    (direct : Fin n → Ref Γ .point) (outer : Origin) (origin : Fin n → Origin)
    (next : Prog c (replyCtx n (replyCtx n Γ)) τ) :
    syntaxCount kind (initializeCenters rho direct outer origin next) =
      (if kind = .gaussian then n else 0) + syntaxCount kind next := by
  cases kind <;> simp [initializeCenters,syntaxCount,residualDraw,initialRow,
    syntaxCount_affineRow,instructionCount,Instr.eventKind]

theorem executedCount_initialize (kind : EventKind) (rho : Fin c)
    (direct : Fin n → Ref Γ .point) (outer : Origin) (origin : Fin n → Origin)
    (next : Prog c (replyCtx n (replyCtx n Γ)) τ) (G : Point d → Point d)
    (input : Inputs d c) (ρ : Env d Γ) (ω : Tape d (initializeCenters rho direct outer origin next)) :
    shapeCount kind ((run (initializeCenters rho direct outer origin next) G input ρ ω).trace.map Event.erase) =
      (if kind = .gaussian then n else 0) + syntaxCount kind next := by
  rw [run_trace_shape,shapeCount_staticTrace,syntaxCount_initialize]


/-- Literal compiler-eval: actual source children at stored centers and fresh P,
actual disjoint public matrices, shared replies, and complete trace provenance. -/
theorem run_noisyLayer_packed (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (old direct : Fin n → Ref Γ .point) (outer : Origin)
    (designated residual : Fin n → Origin)
    (auxiliary : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (next : Prog (publicSize c p) (nextCtx n Γ) τ)
    (A C : Fin n → Fin n → ℝ)
    (T : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (coeff : ∀ i, Fin (c i) → ℝ) (hostX hostP : Point d)
    (G : Point d → Point d) (ρ : Env d Γ) (data : LayerData c p next d) :
    let input : Inputs d (publicSize c p) := ⟨layerTable c p A C T coeff,hostX,hostP⟩
    let sources := fun i => run (p i) G ⟨coeff i,storedPoint ρ (old i),(data.1 i).1⟩ Env.empty
      (transformedSourceTape (p i) (e i) (T i) (data.1 i).2.1 (data.1 i).2.2)
    let Q : Fin n → Point d := fun i => (sources i).value
    let new : Fin n → Point d := fun j => storedPoint ρ (direct j) +
      (∑ i, A j i • Q i) + ∑ k, C j k • data.2.1 k
    let tail := run next G input (Env.prepend new (Env.prepend data.2.1 (Env.prepend Q ρ))) data.2.2
    run (noisyLayer c p e old direct outer designated residual auxiliary next) G input ρ
      (packLayerTape c p e old direct outer designated residual auxiliary next data) =
      ⟨tail.value, ((List.ofFn (fun i => [Event.gaussian (designated i)] ++
          List.ofFn (fun j => Event.gaussian (auxiliary i j)) ++
          (sources i).trace.filter keepNonGaussian)).flatten ++
        List.ofFn (fun j => Event.gaussian (residual j)) ++ tail.trace).map (Event.withPrefix outer)⟩ := by
  have hc (i : Fin n) := run_layerChild c p e old designated auxiliary A C T coeff
    hostX hostP G ρ i ((freshChildTapeEquiv (p i) (e i) (childSlot c p i) (old i)
      (designated i) (auxiliary i)).symm (data.1 i))
  simp only [Equiv.apply_symm_apply] at hc
  have hv (Q Z : Fin n → Point d) :
      noisyValues (aSlot c p) (residualSlot c p) direct
        ⟨layerTable c p A C T coeff,hostX,hostP⟩ ρ Q Z =
        (fun j => storedPoint ρ (direct j) + (∑ i, A j i • Q i) + ∑ k, C j k • Z k) := by
    funext j
    exact noisyValues_layerTable c p A C T coeff hostX hostP direct ρ Q Z j
  dsimp only
  erw [run_noisyLayer]
  simp only [packLayerTape,hc]
  erw [hv]

end AcceleratedLogConcave.Oracle.NoisyLayer
