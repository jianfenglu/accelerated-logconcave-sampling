import AcceleratedLogConcave.Oracle.RecursiveMeanFinalState
import AcceleratedLogConcave.Oracle.SourceMeanLayerTape

/-! Complete raw-tape decomposition and traces for the existing iterateThen.
Only the data carrier and trace extraction recurse; executable syntax is reused. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.RecursiveMeanContinuation
open AffineLowering TapeLowering NoisyLayer RecursiveMeanProgram SourceMeanLayer
open scoped BigOperators

abbrev LayerInputs (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point) (d : ℕ) :=
  (∀ i, Point d × ((Fin (tapeShape (p i)).gaussianBlocks → Point d) × ResidualTape (p i))) ×
    (Fin n → Point d)

variable (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
  (slots : Fin (publicSize c p) → Fin C)
  (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
  (outer : ℕ → Origin) (designated residual : ℕ → Fin n → Origin)
  (auxiliary : ℕ → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
  (finish : ∀ {Δ : Ctx}, (Fin n → Ref Δ .point) →
    (Fin n → Ref Δ .point) → RefMap Ξ Δ → Prog C Δ τ)

private theorem result_eq {a : Result d τ} {v : Ty.denote d τ} {es : List (Event d)}
    (hv : a.value = v) (ht : a.trace = es) : a = ⟨v,es⟩ := by
  cases a
  cases hv
  cases ht
  rfl

/-- Depth zero keeps the actual finish tape, including every uniform coordinate. -/
def RawData (d : ℕ) : (depth : ℕ) → {Γ : Ctx} →
    (Fin n → Ref Γ .point) → (Fin n → Ref Γ .point) → RefMap Ξ Γ → Type
  | 0, _, old, direct, saved => Tape d (finish old direct saved)
  | depth+1, _, _, direct, saved => LayerInputs c p d ×
      RawData d depth batchRef (fun j => preserveDirect (direct j)) (fun r => preserveDirect (saved r))

/-- The routed layer equivalence is used at its actual changing context. -/
def rawTapeEquiv (d : ℕ) : (depth : ℕ) → {Γ : Ctx} →
    (old direct : Fin n → Ref Γ .point) → (saved : RefMap Ξ Γ) →
    Tape d (iterateThen c p slots e outer designated residual auxiliary finish depth old direct saved) ≃
      RawData c p finish d depth old direct saved
  | 0, _, _, _, _ => Equiv.refl _
  | depth+1, _, old, direct, saved =>
      (layerAtTapeEquiv c p slots e old direct (outer depth) (designated depth) (residual depth) (auxiliary depth)
        (iterateThen c p slots e outer designated residual auxiliary finish depth batchRef
          (fun j => preserveDirect (direct j)) (fun r => preserveDirect (saved r)))).trans
        ((Equiv.prodAssoc _ _ _).symm.trans
          (Equiv.prodCongr (Equiv.refl _) (rawTapeEquiv d depth batchRef
            (fun j => preserveDirect (direct j)) (fun r => preserveDirect (saved r)))))

theorem rawTape_roundtrip (d depth : ℕ) {Γ : Ctx} (old direct : Fin n → Ref Γ .point) (saved : RefMap Ξ Γ)
    (tape : Tape d (iterateThen c p slots e outer designated residual auxiliary finish depth old direct saved)) :
    (rawTapeEquiv c p slots e outer designated residual auxiliary finish d depth old direct saved).symm
      (rawTapeEquiv c p slots e outer designated residual auxiliary finish d depth old direct saved tape) = tape := Equiv.symm_apply_apply _ _

theorem rawData_roundtrip (d depth : ℕ) {Γ : Ctx} (old direct : Fin n → Ref Γ .point) (saved : RefMap Ξ Γ)
    (data : RawData c p finish d depth old direct saved) :
    rawTapeEquiv c p slots e outer designated residual auxiliary finish d depth old direct saved
      ((rawTapeEquiv c p slots e outer designated residual auxiliary finish d depth old direct saved).symm data) = data := Equiv.apply_symm_apply _ _

/-- Trace extraction follows the existing actual interpreter and changing stores. -/
def executionTrace (G : Point d → Point d) (input : Inputs d C) :
    (depth : ℕ) → {Γ : Ctx} → (old direct : Fin n → Ref Γ .point) → (saved : RefMap Ξ Γ) →
    (env : Env d Γ) → Tape d (iterateThen c p slots e outer designated residual auxiliary finish depth old direct saved) → List (Event d)
  | 0, _, old, direct, saved, env, tape => (run (finish old direct saved) G input env tape).trace
  | depth+1, _, old, direct, saved, env, tape =>
      let children := fun i => run (freshChild (p i) (e i) (slots ∘ childSlot c p i) (old i)
        (designated depth i) (auxiliary depth i)) G input env (tape.1 i)
      let Q := fun i => (children i).value
      let Z := fun i => (tape.2.1 i).1
      let X := noisyValues (fun j k => slots (aSlot c p j k)) (fun j k => slots (residualSlot c p j k)) direct input env Q Z
      ((List.ofFn (fun i => (children i).trace)).flatten ++ List.ofFn (fun i => Event.gaussian (residual depth i)) ++
        executionTrace G input depth batchRef (fun j => preserveDirect (direct j)) (fun r => preserveDirect (saved r))
          (Env.prepend X (Env.prepend Z (Env.prepend Q env))) tape.2.2.2).map (Event.withPrefix (outer depth))

theorem run_iterateThen_trace (G : Point d → Point d) (input : Inputs d C)
    (depth : ℕ) {Γ : Ctx} (old direct : Fin n → Ref Γ .point) (saved : RefMap Ξ Γ) (env : Env d Γ)
    (tape : Tape d (iterateThen c p slots e outer designated residual auxiliary finish depth old direct saved)) :
    (run (iterateThen c p slots e outer designated residual auxiliary finish depth old direct saved) G input env tape).trace =
      executionTrace c p slots e outer designated residual auxiliary finish G input depth old direct saved env tape := by
  induction depth generalizing Γ with
  | zero => rfl
  | succ depth ih =>
    dsimp only [iterateThen] at tape ⊢
    rw [run_layerAt]
    dsimp only [executionTrace]
    rw [ih]

theorem run_iterateThen_result (G : Point d → Point d) (input : Inputs d C)
    (depth : ℕ) {Γ : Ctx} (old direct : Fin n → Ref Γ .point) (saved : RefMap Ξ Γ) (env : Env d Γ)
    (tape : Tape d (iterateThen c p slots e outer designated residual auxiliary finish depth old direct saved)) :
    let state := finalState c p slots e outer designated residual auxiliary finish G input depth old direct saved env tape
    run (iterateThen c p slots e outer designated residual auxiliary finish depth old direct saved) G input env tape =
      ⟨(run (finish state.old state.direct state.saved) G input state.env state.tape).value,
        executionTrace c p slots e outer designated residual auxiliary finish G input depth old direct saved env tape⟩ := by
  have hv := run_iterateThen_value c p slots e outer designated residual auxiliary finish G input depth old direct saved env tape
  have ht := run_iterateThen_trace c p slots e outer designated residual auxiliary finish G input depth old direct saved env tape
  exact result_eq hv ht


/-- Each raw successor executes the original child at the actual old center,
then keeps its residual term and passes the resulting concrete environment on. -/
theorem run_raw_succ (A R : Fin n → Fin n → ℝ)
    (T : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (coeff : ∀ i, Fin (c i) → ℝ) (G : Point d → Point d) (input : Inputs d C)
    (htable : input.coefficient ∘ slots = layerTable c p A R T coeff)
    (depth : ℕ) {Γ : Ctx} (old direct : Fin n → Ref Γ .point) (saved : RefMap Ξ Γ) (env : Env d Γ)
    (data : RawData c p finish d (depth+1) old direct saved) :
    let src := fun i => run (p i) G ⟨coeff i,storedPoint env (old i),(data.1.1 i).1⟩ Env.empty
      (transformedSourceTape (p i) (e i) (T i) (data.1.1 i).2.1 (data.1.1 i).2.2)
    let Q : Fin n → Point d := fun i => (src i).value
    let X := fun j => storedPoint env (direct j)+(∑ i, A j i • Q i)+∑ k, R j k • data.1.2 k
    let tail := run (iterateThen c p slots e outer designated residual auxiliary finish depth batchRef
      (fun j => preserveDirect (direct j)) (fun r => preserveDirect (saved r))) G input
      (Env.prepend X (Env.prepend data.1.2 (Env.prepend Q env)))
      ((rawTapeEquiv c p slots e outer designated residual auxiliary finish d depth batchRef
        (fun j => preserveDirect (direct j)) (fun r => preserveDirect (saved r))).symm data.2)
    run (iterateThen c p slots e outer designated residual auxiliary finish (depth+1) old direct saved) G input env
      ((rawTapeEquiv c p slots e outer designated residual auxiliary finish d (depth+1) old direct saved).symm data) =
      ⟨tail.value,((List.ofFn (fun i => [Event.gaussian (designated depth i)] ++
        List.ofFn (fun j => Event.gaussian (auxiliary depth i j)) ++ (src i).trace.filter keepNonGaussian)).flatten ++
        List.ofFn (fun i => Event.gaussian (residual depth i)) ++ tail.trace).map (Event.withPrefix (outer depth))⟩ := by
  exact run_layerAt_packed c p slots e old direct (outer depth) (designated depth) (residual depth) (auxiliary depth)
    (iterateThen c p slots e outer designated residual auxiliary finish depth batchRef
      (fun j => preserveDirect (direct j)) (fun r => preserveDirect (saved r))) A R T coeff G input env htable
    (data.1.1,data.1.2,(rawTapeEquiv c p slots e outer designated residual auxiliary finish d depth batchRef
      (fun j => preserveDirect (direct j)) (fun r => preserveDirect (saved r))).symm data.2)

theorem finalState_direct (G : Point d → Point d) (input : Inputs d C)
    (depth : ℕ) {Γ : Ctx} (old direct : Fin n → Ref Γ .point) (saved : RefMap Ξ Γ) (env : Env d Γ)
    (tape : Tape d (iterateThen c p slots e outer designated residual auxiliary finish depth old direct saved)) (j : Fin n) :
    let st := finalState c p slots e outer designated residual auxiliary finish G input depth old direct saved env tape
    storedPoint st.env (st.direct j) = storedPoint env (direct j) := by
  induction depth generalizing Γ with
  | zero => rfl
  | succ depth ih =>
    simp only [finalState]
    rw [ih]
    exact stored_preserveDirect env _ _ _ (direct j)

end AcceleratedLogConcave.Oracle.RecursiveMeanContinuation
