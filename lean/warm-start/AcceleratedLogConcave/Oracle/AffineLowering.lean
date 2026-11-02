import AcceleratedLogConcave.Oracle.Lowering
import AcceleratedLogConcave.Numerics.AffineGraph

/-!
# Closed affine rows and synchronous stored-reply layers

This compiler uses only the existing public-scalar, scalar-vector multiplication
and vector-addition primitives. Child programs are embedded at stored inputs;
every child is executed once and all affine rows reuse its stored reply.
Noise setup, recursive graph generation and tape probability laws are separate.
-/

namespace AcceleratedLogConcave.Oracle.AffineLowering

open scoped BigOperators

/-- Read a point with its concrete Euclidean carrier exposed to elaboration. -/
def storedPoint (ρ : Env d Γ) (r : Ref Γ .point) : Point d := ρ r

/-- A result whose value is explicitly in the concrete point carrier. -/
def pointResult (v : Point d) (events : List (Event d)) : Result d .point := ⟨v, events⟩

/-- Lift old references past the scalar, product and new accumulator. -/
def shiftTerm (f : RefMap Γ Δ) : RefMap Γ (.point :: .point :: .scalar :: Δ) :=
  fun r => .there (.there (.there (f r)))

/-- The recursive code keeps its source references fixed and routes them through
the changing store. Each term has three actual closed pure instructions. -/
def rowCode (origin : Origin) (terms : List (Fin c × Ref Γ .point))
    {Δ : Ctx} (f : RefMap Γ Δ) (base : Ref Δ .point) : Prog c Δ .point :=
  match terms with
  | [] => .ret base
  | (slot, vector) :: rest =>
    .step origin (.pure (.publicScalar slot))
      (.step origin (.pure (.smul .here (.there (f vector))))
        (.step origin (.pure (.vadd (.there (.there base)) .here))
          (rowCode origin rest (shiftTerm f) .here)))

/-- A finite ordered affine row, with no arbitrary evaluator constructor. -/
abbrev affineRow (origin : Origin) (base : Ref Γ .point)
    (terms : List (Fin c × Ref Γ .point)) : Prog c Γ .point :=
  rowCode origin terms (fun r => r) base

theorem run_rowCode (origin : Origin) (terms : List (Fin c × Ref Γ .point))
    {Δ : Ctx} (f : RefMap Γ Δ) (base : Ref Δ .point)
    (G : Point d → Point d) (i : Inputs d c) (ρ : Env d Δ)
    (ω : Tape d (rowCode origin terms f base)) :
    run (rowCode origin terms f base) G i ρ ω =
      pointResult (storedPoint ρ base + (terms.map (fun t : Fin c × Ref Γ .point => i.coefficient t.1 • storedPoint ρ (f t.2))).sum) [] := by
  induction terms generalizing Δ with
  | nil =>
    change pointResult (storedPoint ρ base) [] = pointResult (storedPoint ρ base + 0) []
    rw [add_zero]
  | cons t ts ih =>
    rcases t with ⟨slot, vector⟩
    simp only [rowCode, run, evalInstr, evalPure]
    rw [ih]
    change pointResult ((storedPoint ρ base + i.coefficient slot • storedPoint ρ (f vector)) +
      (ts.map (fun t => i.coefficient t.1 • storedPoint ρ (f t.2))).sum) [] =
      pointResult (storedPoint ρ base + (i.coefficient slot • storedPoint ρ (f vector) +
      (ts.map (fun t => i.coefficient t.1 • storedPoint ρ (f t.2))).sum)) []
    rw [add_assoc]

theorem run_affineRow (origin : Origin) (base : Ref Γ .point)
    (terms : List (Fin c × Ref Γ .point))
    (G : Point d → Point d) (i : Inputs d c) (ρ : Env d Γ)
    (ω : Tape d (affineRow origin base terms)) :
    run (affineRow origin base terms) G i ρ ω =
      pointResult (storedPoint ρ base + (terms.map (fun t : Fin c × Ref Γ .point => i.coefficient t.1 • storedPoint ρ t.2)).sum) [] :=
  run_rowCode origin terms (fun r => r) base G i ρ ω

theorem syntaxCount_rowCode (kind : EventKind) (origin : Origin)
    (terms : List (Fin c × Ref Γ .point)) {Δ : Ctx}
    (f : RefMap Γ Δ) (base : Ref Δ .point) :
    syntaxCount kind (rowCode origin terms f base) = 0 := by
  induction terms generalizing Δ with
  | nil => rfl
  | cons t ts ih =>
    simp [rowCode, syntaxCount, instructionCount, Instr.eventKind, ih]

theorem syntaxCount_affineRow (kind : EventKind) (origin : Origin)
    (base : Ref Γ .point) (terms : List (Fin c × Ref Γ .point)) :
    syntaxCount kind (affineRow origin base terms) = 0 :=
  syntaxCount_rowCode kind origin terms (fun r => r) base

/-- The unique structural tape of the pure arithmetic row. -/
def rowTape (d : ℕ) (origin : Origin) (terms : List (Fin c × Ref Γ .point))
    {Δ : Ctx} (f : RefMap Γ Δ) (base : Ref Δ .point) :
    Tape d (rowCode origin terms f base) :=
  match terms with
  | [] => PUnit.unit
  | (_, _) :: rest => ⟨PUnit.unit, PUnit.unit, PUnit.unit,
      rowTape d origin rest (shiftTerm f) .here⟩

theorem rowTape_unique (origin : Origin) (terms : List (Fin c × Ref Γ .point))
    {Δ : Ctx} (f : RefMap Γ Δ) (base : Ref Δ .point)
    (ω : Tape d (rowCode origin terms f base)) :
    ω = rowTape d origin terms f base := by
  induction terms generalizing Δ with
  | nil =>
    change PUnit at ω
    cases ω
    rfl
  | cons t ts ih =>
    rcases t with ⟨slot, vector⟩
    rcases ω with ⟨⟨⟩, ⟨⟩, ⟨⟩, tail⟩
    exact congrArg (fun z => (PUnit.unit, PUnit.unit, PUnit.unit, z))
      (ih (shiftTerm f) .here tail)

/-- Read a batch result in its ascending finite occurrence order. -/
def batchRef {Γ : Ctx} : {n : ℕ} → Fin n → Ref (List.replicate n Ty.point ++ Γ) .point
  | _n+1, j => Fin.cases .here (fun k => .there (batchRef k)) j

theorem prepend_batchRef (values : Fin n → Point d) (ρ : Env d Γ) (j : Fin n) :
    storedPoint (Env.prepend values ρ) (batchRef j) = values j := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    refine Fin.cases ?_ (fun k => ?_) j
    · rfl
    · exact ih (fun k => values k.succ) k

theorem prepend_shiftMany (values : Fin n → Point d) (ρ : Env d Γ)
    (r : Ref Γ τ) : Env.prepend values ρ (RefMap.shiftMany n r) = ρ r := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih (fun k => values k.succ)

theorem run_affineRow_ofFn (origin : Origin) (base : Ref Γ .point)
    (slots : Fin n → Fin c) (vectors : Fin n → Ref Γ .point)
    (G : Point d → Point d) (i : Inputs d c) (ρ : Env d Γ)
    (ω : Tape d (affineRow origin base (List.ofFn fun j => (slots j, vectors j)))) :
    run (affineRow origin base (List.ofFn fun j => (slots j, vectors j))) G i ρ ω =
      pointResult (storedPoint ρ base + ∑ j, i.coefficient (slots j) •
        storedPoint ρ (vectors j)) [] := by
  rw [run_affineRow]
  simp only [List.map_ofFn, Function.comp_def, Fin.sum_ofFn]

/-- All rows read the one cached reply block. They do not invoke its suppliers. -/
abbrev affineRows (matrixSlot : Fin n → Fin n → Fin c)
    (direct : Fin n → Ref Γ .point) (j : Fin n) :
    Prog c (List.replicate n Ty.point ++ Γ) .point :=
  affineRow [] (RefMap.shiftMany n (direct j))
    (List.ofFn fun k => (matrixSlot j k, batchRef k))

/-- Literal numerical row value in a store with a separately cached reply array. -/
noncomputable def updatedRows (matrixSlot : Fin n → Fin n → Fin c)
    (direct : Fin n → Ref Γ .point) (i : Inputs d c) (ρ : Env d Γ)
    (Q : Fin n → Point d) (j : Fin n) : Point d :=
  storedPoint ρ (direct j) + ∑ k, i.coefficient (matrixSlot j k) • Q k

theorem run_affineRows (matrixSlot : Fin n → Fin n → Fin c)
    (direct : Fin n → Ref Γ .point) (j : Fin n)
    (G : Point d → Point d) (i : Inputs d c) (ρ : Env d Γ) (Q : Fin n → Point d)
    (ω : Tape d (affineRows matrixSlot direct j)) :
    run (affineRows matrixSlot direct j) G i (Env.prepend Q ρ) ω =
      pointResult (updatedRows matrixSlot direct i ρ Q j) [] := by
  change run (affineRow [] (RefMap.shiftMany n (direct j))
    (List.ofFn fun k => (matrixSlot j k, batchRef k))) G i (Env.prepend Q ρ) ω = _
  rw [run_affineRow_ofFn]
  congr 1
  unfold updatedRows
  rw [show storedPoint (Env.prepend Q ρ) (RefMap.shiftMany n (direct j)) =
    storedPoint ρ (direct j) from prepend_shiftMany Q ρ (direct j)]
  simp only [prepend_batchRef]

theorem prefix_nil (events : List (Event d)) :
    events.map (Event.withPrefix []) = events := by
  have h : Event.withPrefix [] = (id : Event d → Event d) := by
    funext e
    cases e <;> rfl
  rw [h, List.map_id]

/-- The pure row batch changes only the stored environment, without events. -/
theorem run_rowBatch (matrixSlot : Fin n → Fin n → Fin c)
    (direct : Fin n → Ref Γ .point)
    (next : Prog c (List.replicate n Ty.point ++ (List.replicate n Ty.point ++ Γ)) τ)
    (G : Point d → Point d) (i : Inputs d c) (ρ : Env d Γ) (Q : Fin n → Point d)
    (ω : (∀ j, Tape d (affineRows matrixSlot direct j)) × Tape d next) :
    run (τ := τ) (.batch [] (affineRows matrixSlot direct) next) G i (Env.prepend Q ρ) ω =
      run next G i (Env.prepend (updatedRows matrixSlot direct i ρ Q)
        (Env.prepend Q ρ)) ω.2 := by
  simp only [run, run_affineRows, pointResult]
  simp only [List.ofFn_const, List.flatten_replicate_nil, List.nil_append, prefix_nil]

/-- Store all child replies before computing any updated affine row. -/
abbrev layer (origin : Origin) (childC : Fin n → ℕ)
    (children : ∀ j, Program (childC j) .point)
    (κ : ∀ j, Fin (childC j) → Fin c)
    (old momentum direct : Fin n → Ref Γ .point)
    (matrixSlot : Fin n → Fin n → Fin c)
    (next : Prog c (List.replicate n Ty.point ++ (List.replicate n Ty.point ++ Γ)) τ) :
    Prog c Γ τ :=
  .batch origin (fun j => (children j).embed (κ j) (old j) (momentum j))
    (.batch [] (affineRows matrixSlot direct) next)

/-- Exact source-child execution on the tape recovered from its embedded slice. -/
noncomputable def childResults (childC : Fin n → ℕ)
    (children : ∀ j, Program (childC j) .point)
    (κ : ∀ j, Fin (childC j) → Fin c) (old momentum : Fin n → Ref Γ .point)
    (G : Point d → Point d) (i : Inputs d c) (ρ : Env d Γ)
    (ω : ∀ j, Tape d ((children j).embed (κ j) (old j) (momentum j)))
    (j : Fin n) : Result d .point :=
  run (children j) G
    ⟨i.coefficient ∘ κ j, storedPoint ρ (old j), storedPoint ρ (momentum j)⟩ Env.empty
    (restoreTape (κ j) (children j) (fun r => nomatch r) (old j) (momentum j) (ω j))

/-- Entire Result preservation, including the outer prefix on the continuation. -/
theorem run_layer (origin : Origin) (childC : Fin n → ℕ)
    (children : ∀ j, Program (childC j) .point)
    (κ : ∀ j, Fin (childC j) → Fin c)
    (old momentum direct : Fin n → Ref Γ .point)
    (matrixSlot : Fin n → Fin n → Fin c)
    (next : Prog c (List.replicate n Ty.point ++ (List.replicate n Ty.point ++ Γ)) τ)
    (G : Point d → Point d) (i : Inputs d c) (ρ : Env d Γ)
    (ω : (∀ j, Tape d ((children j).embed (κ j) (old j) (momentum j))) ×
      ((∀ j, Tape d (affineRows matrixSlot direct j)) × Tape d next)) :
    let results := childResults childC children κ old momentum G i ρ ω.1
    let Q : Fin n → Point d := fun j => (results j).value
    let tail := run next G i
      (Env.prepend (updatedRows matrixSlot direct i ρ Q) (Env.prepend Q ρ)) ω.2.2
    run (τ := τ) (layer origin childC children κ old momentum direct matrixSlot next) G i ρ ω =
      ⟨tail.value, ((List.ofFn fun j => (results j).trace).flatten ++ tail.trace).map
        (Event.withPrefix origin)⟩ := by
  change (let results := fun j => run ((children j).embed (κ j) (old j) (momentum j))
            G i ρ (ω.1 j)
          let Q : Fin n → Point d := fun j => (results j).value
          let tail := run (τ := τ) (.batch [] (affineRows matrixSlot direct) next) G i
            (Env.prepend Q ρ) ω.2
          (⟨tail.value, ((List.ofFn fun j => (results j).trace).flatten ++ tail.trace).map
            (Event.withPrefix origin)⟩ : Result d τ)) = _
  dsimp only
  erw [run_rowBatch]
  simp only [run_embed_every_tape]
  rfl

/-- Every child occurrence is charged, including unused or zero-column replies. -/
theorem syntaxCount_layer (kind : EventKind) (origin : Origin) (childC : Fin n → ℕ)
    (children : ∀ j, Program (childC j) .point)
    (κ : ∀ j, Fin (childC j) → Fin c)
    (old momentum direct : Fin n → Ref Γ .point)
    (matrixSlot : Fin n → Fin n → Fin c)
    (next : Prog c (List.replicate n Ty.point ++ (List.replicate n Ty.point ++ Γ)) τ) :
    syntaxCount kind (layer origin childC children κ old momentum direct matrixSlot next) =
      (∑ j, syntaxCount kind (children j)) + syntaxCount kind next := by
  simp only [layer, syntaxCount_batch, affineRows, syntaxCount_affineRow,
    Finset.sum_const_zero, zero_add, Program.embed, syntaxCount_lower]

/-- The syntax count is the actual executed count on every structural tape. -/
theorem executedCount_layer (kind : EventKind) (origin : Origin) (childC : Fin n → ℕ)
    (children : ∀ j, Program (childC j) .point)
    (κ : ∀ j, Fin (childC j) → Fin c)
    (old momentum direct : Fin n → Ref Γ .point)
    (matrixSlot : Fin n → Fin n → Fin c)
    (next : Prog c (List.replicate n Ty.point ++ (List.replicate n Ty.point ++ Γ)) τ)
    (G : Point d → Point d) (i : Inputs d c) (ρ : Env d Γ)
    (ω : Tape d (layer origin childC children κ old momentum direct matrixSlot next)) :
    shapeCount kind ((run (layer origin childC children κ old momentum direct matrixSlot next)
      G i ρ ω).trace.map Event.erase) =
      (∑ j, syntaxCount kind (children j)) + syntaxCount kind next := by
  rw [run_trace_shape, shapeCount_staticTrace, syntaxCount_layer]

def affineRowsTape (d : ℕ) (matrixSlot : Fin n → Fin n → Fin c)
    (direct : Fin n → Ref Γ .point) (j : Fin n) :
    Tape d (affineRows matrixSlot direct j) :=
  rowTape d [] (List.ofFn fun k => (matrixSlot j k, batchRef k))
    (fun r => r) (RefMap.shiftMany n (direct j))

theorem affineRowsTape_unique (matrixSlot : Fin n → Fin n → Fin c)
    (direct : Fin n → Ref Γ .point) (j : Fin n)
    (ω : Tape d (affineRows matrixSlot direct j)) :
    ω = affineRowsTape d matrixSlot direct j :=
  rowTape_unique [] _ (fun r => r) _ ω

/-- Route every source child tape and the continuation tape to the actual layer. -/
def packLayerTape (origin : Origin) (childC : Fin n → ℕ)
    (children : ∀ j, Program (childC j) .point)
    (κ : ∀ j, Fin (childC j) → Fin c)
    (old momentum direct : Fin n → Ref Γ .point)
    (matrixSlot : Fin n → Fin n → Fin c)
    (next : Prog c (List.replicate n Ty.point ++ (List.replicate n Ty.point ++ Γ)) τ)
    (ω : (∀ j, Tape d (children j)) × Tape d next) :
    Tape d (layer origin childC children κ old momentum direct matrixSlot next) :=
  ⟨fun j => lowerTape (κ j) (children j) (fun r => nomatch r) (old j) (momentum j) (ω.1 j),
    affineRowsTape d matrixSlot direct, ω.2⟩

def unpackLayerTape (origin : Origin) (childC : Fin n → ℕ)
    (children : ∀ j, Program (childC j) .point)
    (κ : ∀ j, Fin (childC j) → Fin c)
    (old momentum direct : Fin n → Ref Γ .point)
    (matrixSlot : Fin n → Fin n → Fin c)
    (next : Prog c (List.replicate n Ty.point ++ (List.replicate n Ty.point ++ Γ)) τ)
    (ω : Tape d (layer origin childC children κ old momentum direct matrixSlot next)) :
    (∀ j, Tape d (children j)) × Tape d next :=
  ⟨fun j => restoreTape (κ j) (children j) (fun r => nomatch r) (old j) (momentum j) (ω.1 j),
    ω.2.2⟩

/-- A structural product equivalence only; no tape probability law is asserted. -/
def layerTapeEquiv (d : ℕ) (origin : Origin) (childC : Fin n → ℕ)
    (children : ∀ j, Program (childC j) .point)
    (κ : ∀ j, Fin (childC j) → Fin c)
    (old momentum direct : Fin n → Ref Γ .point)
    (matrixSlot : Fin n → Fin n → Fin c)
    (next : Prog c (List.replicate n Ty.point ++ (List.replicate n Ty.point ++ Γ)) τ) :
    ((∀ j, Tape d (children j)) × Tape d next) ≃
      Tape d (layer origin childC children κ old momentum direct matrixSlot next) where
  toFun := packLayerTape origin childC children κ old momentum direct matrixSlot next
  invFun := unpackLayerTape origin childC children κ old momentum direct matrixSlot next
  left_inv ω := by
    apply Prod.ext
    · funext j
      exact restoreTape_lowerTape (κ j) (children j) (fun r => nomatch r)
        (old j) (momentum j) (ω.1 j)
    · rfl
  right_inv ω := by
    apply Prod.ext
    · funext j
      exact lowerTape_restoreTape (κ j) (children j) (fun r => nomatch r)
        (old j) (momentum j) (ω.1 j)
    · apply Prod.ext
      · funext j
        exact (affineRowsTape_unique matrixSlot direct j (ω.2.1 j)).symm
      · rfl

open AcceleratedLogConcave.Numerics.AffineGraph

/-- A fixed, reply-independent public slot for each literal matrix entry. -/
def matrixIndex (extra : ℕ) (i j : Fin n) : Fin (n * n + extra) :=
  Fin.castAdd extra (finProdFinEquiv (i, j))

/-- The complete matrix is stored first, followed by an arbitrary public table. -/
def matrixTable (M : Fin n → Fin n → ℝ) (extra : Fin c → ℝ) : Fin (n*n+c) → ℝ :=
  Fin.append (fun k => M (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2) extra

@[simp] theorem matrixTable_entry (M : Fin n → Fin n → ℝ) (extra : Fin c → ℝ)
    (i j : Fin n) : matrixTable M extra (matrixIndex c i j) = M i j := by
  simp only [matrixTable, matrixIndex, Fin.append_left, Equiv.symm_apply_apply]

@[simp] theorem matrixTable_extra (M : Fin n → Fin n → ℝ) (extra : Fin c → ℝ)
    (j : Fin c) : matrixTable M extra (Fin.natAdd (n*n) j) = extra j := by
  simp [matrixTable]

/-- Supply the literal matrix coefficients while keeping both host inputs free. -/
def matrixInputs (M : Fin n → Fin n → ℝ) (extra : Fin c → ℝ)
    (center momentum : Point d) : Inputs d (n*n+c) :=
  ⟨matrixTable M extra, center, momentum⟩

/-- A literal compiled row realizes the actual finite graph under enumeration. -/
theorem updatedRows_eq_graph {ι : Type*} [Fintype ι]
    (A : FiniteGraph ι (Point d)) (e : Fin n ≃ ι)
    (direct : Fin n → Ref Γ .point) (ρ : Env d Γ)
    (hdirect : ∀ j, storedPoint ρ (direct j) = A.direct (e j))
    (extra : Fin c → ℝ) (center momentum : Point d) (Q : Fin n → Point d) (j : Fin n) :
    updatedRows (matrixIndex c) direct
      (matrixInputs (fun i j => A.matrix (e i) (e j)) extra center momentum) ρ Q j =
      A.updateFromReplies (fun a => Q (e.symm a)) (e j) := by
  simp only [updatedRows, matrixInputs, matrixTable_entry, hdirect,
    FiniteGraph.updateFromReplies]
  congr 1
  simpa using (e.sum_comp (fun a => A.matrix (e j) a • Q (e.symm a)))

/-- Specialization to the source mean graph, with its actual free-state centers. -/
theorem updatedRows_eq_mean_centers (M : MeanGeometry m)
    (e : Fin n ≃ M.MeanNode) (r σ : ℝ) (x y0 g0 : Point d)
    (ζ : Fin m → M.Kernel → Point d)
    (direct : Fin n → Ref Γ .point) (ρ : Env d Γ)
    (hdirect : ∀ j, storedPoint ρ (direct j) = M.direct r σ x y0 g0 ζ (e j))
    (extra : Fin c → ℝ) (center momentum : Point d) (Q : Fin n → Point d) (j : Fin n) :
    updatedRows (matrixIndex c) direct
      (matrixInputs (fun i j => M.matrix r σ (e i) (e j)) extra center momentum) ρ Q j =
      M.centers r σ x y0 g0 ζ (fun a => Q (e.symm a)) (e j) := by
  rw [← M.graph_update_eq_centers]
  exact updatedRows_eq_graph (M.graph r σ x y0 g0 ζ) e direct ρ hdirect
    extra center momentum Q j

/-- Specialization to the actual sampling graph and its probability-path centers. -/
theorem updatedRows_eq_sampling_centers (S : SamplingGeometry m)
    (e : Fin n ≃ S.Node) (r : ℝ) (x y0 : Point d)
    (direct : Fin n → Ref Γ .point) (ρ : Env d Γ)
    (hdirect : ∀ j, storedPoint ρ (direct j) = (S.graph r x y0).direct (e j))
    (extra : Fin c → ℝ) (center momentum : Point d) (Q : Fin n → Point d) (j : Fin n) :
    updatedRows (matrixIndex c) direct
      (matrixInputs (fun i j => (S.graph r x y0).matrix (e i) (e j)) extra center momentum) ρ Q j =
      S.centers r x y0 (fun a => Q (e.symm a)) (e j) := by
  rw [← S.graph_update_eq_centers]
  exact updatedRows_eq_graph (S.graph r x y0) e direct ρ hdirect extra center momentum Q j

/-- The actual child outputs feed the actual finite graph before the continuation.
The graph matrix table is constructed literally and is independent of replies. -/
theorem run_layer_graph {ι : Type*} [Fintype ι]
    (A : FiniteGraph ι (Point d)) (e : Fin n ≃ ι)
    (origin : Origin) (childC : Fin n → ℕ)
    (children : ∀ j, Program (childC j) .point)
    (κ : ∀ j, Fin (childC j) → Fin (n*n+c))
    (old momentum direct : Fin n → Ref Γ .point)
    (next : Prog (n*n+c) (List.replicate n Ty.point ++ (List.replicate n Ty.point ++ Γ)) τ)
    (G : Point d → Point d) (ρ : Env d Γ)
    (hdirect : ∀ j, storedPoint ρ (direct j) = A.direct (e j))
    (extra : Fin c → ℝ) (hostX hostP : Point d)
    (ω : Tape d (layer origin childC children κ old momentum direct (matrixIndex c) next)) :
    let i := matrixInputs (fun i j => A.matrix (e i) (e j)) extra hostX hostP
    let results := childResults childC children κ old momentum G i ρ ω.1
    let Q : Fin n → Point d := fun j => (results j).value
    let new : Fin n → Point d := fun j => A.updateFromReplies (fun a => Q (e.symm a)) (e j)
    let tail := run next G i (Env.prepend new (Env.prepend Q ρ)) ω.2.2
    run (layer origin childC children κ old momentum direct (matrixIndex c) next) G i ρ ω =
      ⟨tail.value, ((List.ofFn fun j => (results j).trace).flatten ++ tail.trace).map
        (Event.withPrefix origin)⟩ := by
  have hu (Q : Fin n → Point d) :
      updatedRows (matrixIndex c) direct
        (matrixInputs (fun i j => A.matrix (e i) (e j)) extra hostX hostP) ρ Q =
      fun j => A.updateFromReplies (fun a => Q (e.symm a)) (e j) := by
    funext j
    exact updatedRows_eq_graph A e direct ρ hdirect extra hostX hostP Q j
  dsimp only
  erw [run_layer]
  erw [hu]


/-- Pure affine arithmetic consumes no event resource on every structural tape. -/
theorem executedCount_affineRow (kind : EventKind) (origin : Origin)
    (base : Ref Γ .point) (terms : List (Fin c × Ref Γ .point))
    (G : Point d → Point d) (i : Inputs d c) (ρ : Env d Γ)
    (ω : Tape d (affineRow origin base terms)) :
    shapeCount kind ((run (affineRow origin base terms) G i ρ ω).trace.map Event.erase) = 0 := by
  rw [run_trace_shape, shapeCount_staticTrace, syntaxCount_affineRow]

end AcceleratedLogConcave.Oracle.AffineLowering
