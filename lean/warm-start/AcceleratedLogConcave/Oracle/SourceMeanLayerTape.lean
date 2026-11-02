import AcceleratedLogConcave.Oracle.SourceMeanLayerValue

/-! Complete target-tape routing for a noisy layer inside a larger public table.
The continuation keeps the larger table; no transform inverse is required. -/
namespace AcceleratedLogConcave.Oracle.SourceMeanLayer
open NoisyLayer AffineLowering TapeLowering
open scoped BigOperators
section Routing
variable (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
  (slots : Fin (publicSize c p) → Fin C)
  (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
  (old direct : Fin n → Ref Γ .point) (outer : Origin)
  (designated residual : Fin n → Origin)
  (auxiliary : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
  (next : Prog C (nextCtx n Γ) τ)

abbrev LayerAtData (d : ℕ) :=
  (∀ i, Point d × ((Fin (tapeShape (p i)).gaussianBlocks → Point d) × ResidualTape (p i))) ×
    (Fin n → Point d) × Tape d next

def packLayerAtTape (data : LayerAtData c p next d) :
    Tape d (layerAt c p slots e old direct outer designated residual auxiliary next) :=
  ⟨(fun i => (freshChildTapeEquiv (p i) (e i) (slots ∘ childSlot c p i) (old i)
      (designated i) (auxiliary i)).symm (data.1 i)),
    (fun i => (data.2.1 i,PUnit.unit)),
    (fun j => rowTape d [] (noisyTerms (fun j k => slots (aSlot c p j k))
      (fun j k => slots (residualSlot c p j k)) j) (fun a => a)
      (RefMap.shiftMany n (RefMap.shiftMany n (direct j)))),data.2.2⟩

def unpackLayerAtTape (tape : Tape d (layerAt c p slots e old direct outer designated residual auxiliary next)) :
    LayerAtData c p next d :=
  ⟨(fun i => freshChildTapeEquiv (p i) (e i) (slots ∘ childSlot c p i) (old i)
      (designated i) (auxiliary i) (tape.1 i)), (fun i => (tape.2.1 i).1),tape.2.2.2⟩

theorem unpack_packLayerAtTape (data : LayerAtData c p next d) :
    unpackLayerAtTape c p slots e old direct outer designated residual auxiliary next
      (packLayerAtTape c p slots e old direct outer designated residual auxiliary next data) = data := by
  simp only [unpackLayerAtTape, packLayerAtTape, Equiv.apply_symm_apply]

theorem pack_unpackLayerAtTape (tape : Tape d (layerAt c p slots e old direct outer designated residual auxiliary next)) :
    packLayerAtTape c p slots e old direct outer designated residual auxiliary next
      (unpackLayerAtTape c p slots e old direct outer designated residual auxiliary next tape) = tape := by
  rcases tape with ⟨children,draws,rows,tail⟩
  simp only [packLayerAtTape, unpackLayerAtTape, Equiv.symm_apply_apply]
  have hd : (fun i => ((draws i).1,PUnit.unit)) = draws := by
    funext i
    rcases draws i with ⟨z,⟨⟩⟩
    rfl
  have hr : (fun j => rowTape d []
      (noisyTerms (fun j k => slots (aSlot c p j k)) (fun j k => slots (residualSlot c p j k)) j)
      (fun a => a) (RefMap.shiftMany n (RefMap.shiftMany n (direct j)))) = rows := by
    funext j
    exact (rowTape_unique [] _ (fun a => a) _ (rows j)).symm
  erw [hd,hr]

def layerAtTapeEquiv :
    Tape d (layerAt c p slots e old direct outer designated residual auxiliary next) ≃ LayerAtData c p next d where
  toFun := unpackLayerAtTape c p slots e old direct outer designated residual auxiliary next
  invFun := packLayerAtTape c p slots e old direct outer designated residual auxiliary next
  left_inv := pack_unpackLayerAtTape c p slots e old direct outer designated residual auxiliary next
  right_inv := unpack_packLayerAtTape c p slots e old direct outer designated residual auxiliary next

theorem run_layerAt_packed (A R : Fin n → Fin n → ℝ)
    (T : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (coeff : ∀ i, Fin (c i) → ℝ) (G : Point d → Point d) (input : Inputs d C) (env : Env d Γ)
    (htable : input.coefficient ∘ slots = layerTable c p A R T coeff) (data : LayerAtData c p next d) :
    let src := fun i => run (p i) G ⟨coeff i,storedPoint env (old i),(data.1 i).1⟩ Env.empty
      (transformedSourceTape (p i) (e i) (T i) (data.1 i).2.1 (data.1 i).2.2)
    let Q : Fin n → Point d := fun i => (src i).value
    let new := fun j => storedPoint env (direct j)+(∑ i, A j i • Q i)+∑ k, R j k • data.2.1 k
    let tail := run next G input (Env.prepend new (Env.prepend data.2.1 (Env.prepend Q env))) data.2.2
    run (layerAt c p slots e old direct outer designated residual auxiliary next) G input env
      (packLayerAtTape c p slots e old direct outer designated residual auxiliary next data) =
      ⟨tail.value, ((List.ofFn (fun i => [Event.gaussian (designated i)] ++
          List.ofFn (fun j => Event.gaussian (auxiliary i j)) ++ (src i).trace.filter keepNonGaussian)).flatten ++
        List.ofFn (fun j => Event.gaussian (residual j)) ++ tail.trace).map (Event.withPrefix outer)⟩ := by
  have hc (i : Fin n) := run_freshChild (p i) (e i) (slots ∘ childSlot c p i) (old i)
    (designated i) (auxiliary i) (T i) (coeff i) G input env
    (funext (fun k => (congrFun htable (childSlot c p i k)).trans (layerTable_child c p A R T coeff i k)))
    ((freshChildTapeEquiv (p i) (e i) (slots ∘ childSlot c p i) (old i) (designated i) (auxiliary i)).symm (data.1 i))
  simp only [Equiv.apply_symm_apply] at hc
  have hv (Q Z : Fin n → Point d) :
      noisyValues (fun j k => slots (aSlot c p j k)) (fun j k => slots (residualSlot c p j k)) direct input env Q Z =
      (fun j => storedPoint env (direct j)+(∑ i, A j i • Q i)+∑ k, R j k • Z k) := by
    funext j
    unfold noisyValues
    have ha (k : Fin n) := (congrFun htable (aSlot c p j k)).trans (layerTable_a c p A R T coeff j k)
    have hr (k : Fin n) := (congrFun htable (residualSlot c p j k)).trans (layerTable_residual c p A R T coeff j k)
    simp only [Function.comp_apply] at ha hr
    simp only [ha,hr]
  dsimp only
  erw [run_layerAt]
  simp only [packLayerAtTape,hc]
  erw [hv]
end Routing
end AcceleratedLogConcave.Oracle.SourceMeanLayer
