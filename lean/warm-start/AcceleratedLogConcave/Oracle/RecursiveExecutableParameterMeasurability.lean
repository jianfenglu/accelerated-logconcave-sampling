import AcceleratedLogConcave.Oracle.RecursiveExecutableParameterShape
import AcceleratedLogConcave.Oracle.CovarianceSetupMeasurability

/-! Measurability of the actual recursive source data after its syntax shape
has been fixed by `meanCore_shape`. -/
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
namespace AcceleratedLogConcave.Oracle.RecursiveExecutableParameterMeasurability
open RecursiveExecutable RecursiveExecutableParameterShape TapeLowering
  Numerics.AffineGraph AffineLowering NoisyLayer
open scoped MatrixOrder Matrix.Norms.L2Operator

abbrev Shape := Σ c : ℕ, Program c .point
abbrev Payload (s : Shape) := (Fin s.1 → ℝ) ×
  (GaussianSlot s.2 → ℝ)

def payload (E : ExecutableData) : Payload (shape E) :=
  ⟨E.coefficient, E.shift⟩

def reconstruct (s : Shape) (v : Payload s) : ExecutableData where
  size := s.1
  program := s.2
  coefficient := v.1
  shift := v.2

theorem reconstruct_payload (E : ExecutableData) :
    reconstruct (shape E) (payload E) = E := by
  cases E
  rfl

def alignedPayload (E : ExecutableData) (s : Shape)
    (h : shape E = s) : Payload s := h ▸ payload E

theorem reconstruct_alignedPayload (E : ExecutableData) (s : Shape)
    (h : shape E = s) : reconstruct s (alignedPayload E s h) = E := by
  cases h
  exact reconstruct_payload E

theorem terminal_coefficient_measurable :
    Measurable (fun z : ℝ × ℝ × ℝ =>
      (show Fin 3 → ℝ from (terminal z.1 z.2.1 z.2.2).coefficient)) := by
  apply measurable_pi_iff.mpr
  intro j
  dsimp [terminal, TerminalMeanShift.coefficients]
  split_ifs <;> fun_prop

theorem terminal_shiftVector_measurable :
    Measurable (fun z : ℝ × ℝ × ℝ =>
      (show Fin 1 → ℝ from (terminal z.1 z.2.1 z.2.2).shiftVector)) := by
  apply measurable_pi_iff.mpr
  intro i
  change Measurable (fun _ : ℝ × ℝ × ℝ => (-1 : ℝ))
  exact measurable_const

theorem terminal_payload_measurable :
    Measurable (fun z : ℝ × ℝ × ℝ =>
      alignedPayload (terminal z.1 z.2.1 z.2.2)
        (shape (terminal 0 0 0))
        (terminal_shape z.1 z.2.1 z.2.2 0 0 0)) := by
  change Measurable (fun z : ℝ × ℝ × ℝ =>
    ((show Fin 3 → ℝ from (terminal z.1 z.2.1 z.2.2).coefficient),
      (show GaussianSlot (terminal 0 0 0).program → ℝ from
        (terminal z.1 z.2.1 z.2.2).shift)))
  apply terminal_coefficient_measurable.prodMk
  apply measurable_pi_iff.mpr
  intro i
  change Measurable (fun _ : ℝ × ℝ × ℝ => (-1 : ℝ))
  exact measurable_const

variable {X : Type*} [MeasurableSpace X] {ms ns : ℕ}

theorem measurable_fin_append {a b : ℕ}
    (f : X → Fin a → ℝ) (g : X → Fin b → ℝ)
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => Fin.append (f x) (g x)) := by
  apply measurable_pi_iff.mpr
  intro j
  cases j using Fin.addCases <;> simp only [Fin.append_left, Fin.append_right]
  · exact (measurable_pi_apply _).comp hf
  · exact (measurable_pi_apply _).comp hg

theorem measurable_matrixTable {N c : ℕ}
    (A : X → Fin N → Fin N → ℝ) (extra : X → Fin c → ℝ)
    (hA : Measurable A) (he : Measurable extra) :
    Measurable (fun x => matrixTable (A x) (extra x)) := by
  unfold matrixTable
  apply measurable_fin_append
  · apply measurable_pi_iff.mpr
    intro j
    exact ((measurable_pi_apply _).comp
      ((measurable_pi_apply _).comp hA))
  · exact he

theorem measurable_layerTable {n : ℕ} (c : Fin n → ℕ)
    (p : ∀ i, Program (c i) .point)
    (A C : X → Fin n → Fin n → ℝ)
    (T : X → ∀ i, Fin (tapeShape (p i)).gaussianBlocks →
      Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (coeff : X → ∀ i, Fin (c i) → ℝ)
    (hA : Measurable A) (hC : Measurable C)
    (hT : Measurable T) (hcoeff : Measurable coeff) :
    Measurable (fun x => layerTable c p (A x) (C x) (T x) (coeff x)) := by
  unfold layerTable
  apply measurable_fin_append
  · apply measurable_pi_iff.mpr
    intro j
    exact ((measurable_pi_apply _).comp ((measurable_pi_apply _).comp hA))
  · apply measurable_fin_append
    · apply measurable_pi_iff.mpr
      intro j
      exact ((measurable_pi_apply _).comp ((measurable_pi_apply _).comp hC))
    · apply measurable_pi_iff.mpr
      intro j
      let pair := finSigmaFinEquiv.symm j
      have hmat : Measurable (fun x => T x pair.1) :=
        (measurable_pi_apply pair.1).comp hT
      have hco : Measurable (fun x => coeff x pair.1) :=
        (measurable_pi_apply pair.1).comp hcoeff
      exact (measurable_pi_apply pair.2).comp
        (measurable_matrixTable (fun x => T x pair.1)
          (fun x => coeff x pair.1) hmat hco)

theorem measurable_finalTable {n : ℕ} (c : Fin n → ℕ)
    (p : ∀ i, Program (c i) .point)
    (T : X → ∀ i, Fin (tapeShape (p i)).gaussianBlocks →
      Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (coeff : X → ∀ i, Fin (c i) → ℝ)
    (hT : Measurable T) (hc : Measurable coeff) :
    Measurable (fun x => RecursiveMeanPublicTable.finalTable c p (T x) (coeff x)) := by
  apply measurable_pi_iff.mpr
  intro j
  let pair := finSigmaFinEquiv.symm j
  have hmat : Measurable (fun x => T x pair.1) :=
    (measurable_pi_apply pair.1).comp hT
  have hco : Measurable (fun x => coeff x pair.1) :=
    (measurable_pi_apply pair.1).comp hc
  exact (measurable_pi_apply pair.2).comp
    (measurable_matrixTable (fun x => T x pair.1)
      (fun x => coeff x pair.1) hmat hco)

theorem measurable_sourceLayerTable {n : ℕ} (c : Fin n → ℕ)
    (p : ∀ i, Program (c i) .point)
    (A : X → CovarianceSetup.Mat n)
    (r R Ds rowBound : X → ℝ)
    (radius : X → Fin n → ℝ)
    (shift : X → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (coeff : X → ∀ i, Fin (c i) → ℝ)
    (hA : Measurable A) (hr : Measurable r) (hR : Measurable R)
    (hDs : Measurable Ds) (hb : Measurable rowBound)
    (hrad : Measurable radius) (hs : Measurable shift)
    (hc : Measurable coeff) :
    Measurable (fun x => RecursiveMeanPublicTable.sourceLayerTable c p
      (A x) (r x) (R x) (Ds x) (rowBound x)
      (radius x) (shift x) (coeff x)) := by
  let rho : X → ℝ := fun x => RecursiveMeanPublicTable.centerNoise (r x) (R x) (Ds x)
  have hrho : Measurable rho := by
    dsimp [rho, RecursiveMeanPublicTable.centerNoise]
    fun_prop
  have hroot : Measurable (fun x => CovarianceSetup.residualRoot
      (A x) (rho x) (rowBound x)) :=
    CovarianceSetup.measurable_residualRoot A rho rowBound hA hrho hb
  have hchild : Measurable (fun x => fun i => CovarianceSetup.childRoot
      (rho x) (radius x i) (shift x i)) := by
    apply measurable_pi_iff.mpr
    intro i
    exact CovarianceSetup.measurable_childRoot rho
      (fun x => radius x i) (fun x => shift x i) hrho
      ((measurable_pi_apply i).comp hrad)
      ((measurable_pi_apply i).comp hs)
  exact measurable_layerTable c p A
    (fun x => CovarianceSetup.residualRoot (A x) (rho x) (rowBound x))
    (fun x i => CovarianceSetup.childRoot (rho x) (radius x i) (shift x i))
    coeff hA hroot hchild hc

theorem measurable_sourceFinalTable {n : ℕ} (c : Fin n → ℕ)
    (p : ∀ i, Program (c i) .point)
    (r R Ds : X → ℝ)
    (shift : X → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (coeff : X → ∀ i, Fin (c i) → ℝ)
    (hr : Measurable r) (hR : Measurable R) (hDs : Measurable Ds)
    (hs : Measurable shift) (hc : Measurable coeff) :
    Measurable (fun x => RecursiveMeanPublicTable.sourceFinalTable c p
      (r x) (R x) (Ds x) (shift x) (coeff x)) := by
  let rho : X → ℝ := fun x => RecursiveMeanPublicTable.centerNoise (r x) (R x) (Ds x)
  have hrho : Measurable rho := by
    dsimp [rho, RecursiveMeanPublicTable.centerNoise]
    fun_prop
  have hchild : Measurable (fun x => fun i => CovarianceSetup.childRoot
      (rho x) (r x * R x) (shift x i)) := by
    apply measurable_pi_iff.mpr
    intro i
    exact CovarianceSetup.measurable_childRoot rho (fun x => r x * R x)
      (fun x => shift x i) hrho (hr.mul hR)
      ((measurable_pi_apply i).comp hs)
  exact measurable_finalTable c p
    (fun x i => CovarianceSetup.childRoot (rho x) (r x * R x) (shift x i))
    coeff hchild hc

theorem measurable_reconstruct_coefficient (s : Shape) (v : X → Payload s)
    (hv : Measurable v) :
    Measurable (fun x => (show Fin s.1 → ℝ from
      (reconstruct s (v x)).coefficient)) := hv.fst

theorem measurable_reconstruct_shiftVector (s : Shape) (v : X → Payload s)
    (hv : Measurable v) :
    Measurable (fun x => (show Fin (tapeShape s.2).gaussianBlocks → ℝ from
      (reconstruct s (v x)).shiftVector)) := by
  apply measurable_pi_iff.mpr
  intro j
  change Measurable (fun x => (v x).2 ((gaussianSlotEquiv s.2).symm j))
  exact (measurable_pi_apply _).comp hv.snd

theorem measurable_matrix_inverse {N : ℕ} :
    Measurable (fun A : CovarianceSetup.Mat N => A⁻¹) := by
  have hdet : Measurable (fun A : CovarianceSetup.Mat N => A.det) :=
    continuous_id.matrix_det.measurable
  have hadj : Measurable (fun A : CovarianceSetup.Mat N => A.adjugate) :=
    continuous_id.matrix_adjugate.measurable
  convert hdet.inv.smul hadj using 1
  funext A
  simpa [Pi.smul_apply] using Matrix.inv_def A

theorem measurable_rawShift {N : ℕ}
    (rho radius r k : X → ℝ) (v : X → Fin N → ℝ)
    (hrho : Measurable rho) (hrad : Measurable radius)
    (hr : Measurable r) (hk : Measurable k) (hv : Measurable v) :
    Measurable (fun x => LayerShift.rawShift (rho x) (radius x) (r x) (k x) (v x)) := by
  have hroot : Measurable (fun x => CovarianceSetup.childRoot
      (rho x) (radius x) (v x)) :=
    CovarianceSetup.measurable_childRoot rho radius v hrho hrad hv
  have hinv : Measurable (fun x =>
      (CovarianceSetup.childRoot (rho x) (radius x) (v x))⁻¹) :=
    measurable_matrix_inverse.comp hroot
  apply measurable_pi_iff.mpr
  intro j
  dsimp [LayerShift.rawShift]
  fun_prop

theorem measurable_compiledWeights {c N : ℕ} {τ : Ty}
    (p : Program c τ) (e : GaussianSlot p ≃ Fin N)
    (auxiliary : Fin N → Origin) (w : X → Fin N → ℝ)
    (hw : Measurable w) :
    Measurable (fun x => (show GaussianSlot (compileWith p e auxiliary) → ℝ from
      ExecutableShiftWeights.compiledWeights p e auxiliary (w x))) := by
  apply measurable_pi_iff.mpr
  intro s
  unfold ExecutableShiftWeights.compiledWeights
  split <;> fun_prop

theorem measurable_lowerWeights {c c' : ℕ} {Γ Δ : Ctx} {τ : Ty}
    (κ : Fin c → Fin c') (p : Prog c Γ τ) (f : RefMap Γ Δ)
    (center momentum : Ref Δ .point)
    (w : X → GaussianSlot p → ℝ) (hw : Measurable w) :
    Measurable (fun x => (show GaussianSlot (p.lower κ f center momentum) → ℝ from
      ExecutableShiftWeights.lowerWeights κ p f center momentum (w x))) := by
  apply measurable_pi_iff.mpr
  intro s
  change Measurable (fun x => w x
    (ExecutableShiftWeights.lowerSlot κ p f center momentum s))
  exact (measurable_pi_apply _).comp hw

theorem measurable_freshWeights {c C N : ℕ} {Γ : Ctx}
    (p : Program c .point) (e : GaussianSlot p ≃ Fin N)
    (slots : Fin (N * N + c) → Fin C) (old : Ref Γ .point)
    (designated : Origin) (auxiliary : Fin N → Origin)
    (w : X → Fin N → ℝ) (hw : Measurable w) :
    Measurable (fun x => (show GaussianSlot
      (freshChild p e slots old designated auxiliary) → ℝ from
      ExecutableShiftWeights.freshWeights p e slots old designated auxiliary (w x))) := by
  apply measurable_pi_iff.mpr
  intro s
  cases s with
  | inl _ => exact measurable_const
  | inr s =>
      have hc := measurable_compiledWeights p e auxiliary w hw
      have hl := measurable_lowerWeights slots (compileWith p e auxiliary)
        (fun r => nomatch r) (.there old) .here
        (fun x => ExecutableShiftWeights.compiledWeights p e auxiliary (w x)) hc
      exact (measurable_pi_apply s).comp hl

theorem measurable_layerWeights {n C : ℕ} {Γ : Ctx} {τ : Ty}
    (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (slots : Fin (publicSize c p) → Fin C)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (old direct : Fin n → Ref Γ .point) (outer : Origin)
    (designated residual : Fin n → Origin)
    (auxiliary : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (next : Prog C (nextCtx n Γ) τ)
    (w : X → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (tail : X → GaussianSlot next → ℝ)
    (hw : Measurable w) (htail : Measurable tail) :
    Measurable (fun x => (show GaussianSlot
      (SourceMeanLayer.layerAt c p slots e old direct outer designated residual
        auxiliary next) → ℝ from
      ExecutableShiftWeights.layerWeights c p slots e old direct outer designated
        residual auxiliary next (w x) (tail x))) := by
  apply measurable_pi_iff.mpr
  intro s
  cases s with
  | inl z =>
      have hwi : Measurable (fun x => w x z.1) :=
        (measurable_pi_apply z.1).comp hw
      have hf := measurable_freshWeights (p z.1) (e z.1)
        (slots ∘ childSlot c p z.1) (old z.1) (designated z.1)
        (auxiliary z.1) (fun x => w x z.1) hwi
      exact (measurable_pi_apply z.2).comp hf
  | inr z =>
      cases z with
      | inl _ => exact measurable_const
      | inr z =>
          cases z with
          | inl _ => exact measurable_const
          | inr z => exact (measurable_pi_apply z).comp htail

theorem measurable_initializeWeights {n C : ℕ} {Γ : Ctx} {τ : Ty}
    (rho : Fin C) (direct : Fin n → Ref Γ .point)
    (outer : Origin) (origin : Fin n → Origin)
    (next : Prog C (noiseCtx n Γ) τ)
    (tail : X → GaussianSlot next → ℝ) (ht : Measurable tail) :
    Measurable (fun x => (show GaussianSlot
      (initializeCenters rho direct outer origin next) → ℝ from
      ExecutableShiftWeights.initializeWeights rho direct outer origin next (tail x))) := by
  apply measurable_pi_iff.mpr
  intro s
  cases s with
  | inl _ => exact measurable_const
  | inr s =>
      cases s with
      | inl _ => exact measurable_const
      | inr s => exact (measurable_pi_apply s).comp ht

theorem measurable_iterateWeights {n C : ℕ} {Ξ : Ctx} {τ : Ty}
    (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (slots : Fin (publicSize c p) → Fin C)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (outer : ℕ → Origin) (designated residual : ℕ → Fin n → Origin)
    (auxiliary : ℕ → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (finish : ∀ {Δ : Ctx}, (Fin n → Ref Δ .point) →
      (Fin n → Ref Δ .point) → RefMap Ξ Δ → Prog C Δ τ)
    (w : X → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (finishWeights : (x : X) → ∀ {Δ : Ctx}
      (old direct : Fin n → Ref Δ .point) (saved : RefMap Ξ Δ),
      GaussianSlot (finish old direct saved) → ℝ)
    (hw : Measurable w)
    (hf : ∀ {Δ : Ctx} (old direct : Fin n → Ref Δ .point)
      (saved : RefMap Ξ Δ),
      Measurable (fun x => finishWeights x old direct saved))
    (N : ℕ) : ∀ {Γ : Ctx} (old direct : Fin n → Ref Γ .point)
      (saved : RefMap Ξ Γ),
      Measurable (fun x => (show GaussianSlot
        (RecursiveMeanContinuation.iterateThen c p slots e outer designated
          residual auxiliary finish N old direct saved) → ℝ from
        ExecutableShiftWeights.iterateWeights c p slots e outer designated
          residual auxiliary finish (w x)
          (fun old direct saved => finishWeights x old direct saved)
          N old direct saved)) := by
  induction N with
  | zero =>
      intro Γ old direct saved
      exact hf old direct saved
  | succ N ih =>
      intro Γ old direct saved
      exact measurable_layerWeights c p slots e old direct (outer N)
        (designated N) (residual N) (auxiliary N) _ w
        (fun x => ExecutableShiftWeights.iterateWeights c p slots e outer
          designated residual auxiliary finish (w x)
          (fun old direct saved => finishWeights x old direct saved) N
          batchRef (fun j => RecursiveMeanProgram.preserveDirect (direct j))
          (fun r => RecursiveMeanProgram.preserveDirect (saved r)))
        hw (ih _ _ _)

theorem measurable_samplingFinal {n C : ℕ} {c cf : Fin n → ℕ}
    {p : ∀ i, Program (c i) .point}
    {pf : ∀ i, Program (cf i) .point}
    (cfg : PrivateSamplingProgram.Config n C c cf p pf)
    {Γ : Ctx} (old : Fin n → Ref Γ .point) (direct : Ref Γ .point)
    (final : X → ∀ i, Fin (tapeShape (pf i)).gaussianBlocks → ℝ)
    (reserve : X → ℝ) (hf : Measurable final) (hr : Measurable reserve) :
    Measurable (fun x => SourceExecutableShift.samplingFinal cfg old direct
      (final x) (reserve x)) := by
  apply measurable_pi_iff.mpr
  intro s
  cases s with
  | inl s =>
      have hfi := (measurable_pi_apply s.1).comp hf
      have h := measurable_freshWeights (pf s.1) (cfg.finalEquiv s.1)
        (cfg.finalSlots s.1) (old s.1) (cfg.finalDesignated s.1)
        (cfg.finalAuxiliary s.1) (fun x => final x s.1) hfi
      exact (measurable_pi_apply s.2).comp h
  | inr s =>
      cases s with
      | inl _ => exact measurable_const
      | inr s =>
          cases s with
          | inl _ => exact hr
          | inr _ => exact measurable_const

theorem measurable_samplingBody {n C : ℕ} {c cf : Fin n → ℕ}
    {p : ∀ i, Program (c i) .point}
    {pf : ∀ i, Program (cf i) .point}
    (cfg : PrivateSamplingProgram.Config n C c cf p pf)
    {Γ : Ctx} (direct : Fin n → Ref Γ .point)
    (outputDirect : Ref Γ .point)
    (main : X → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (final : X → ∀ i, Fin (tapeShape (pf i)).gaussianBlocks → ℝ)
    (reserve : X → ℝ) (hm : Measurable main)
    (hf : Measurable final) (hr : Measurable reserve) :
    Measurable (fun x => SourceExecutableShift.samplingBody cfg direct
      outputDirect (main x) (final x) (reserve x)) := by
  unfold SourceExecutableShift.samplingBody
  apply measurable_initializeWeights
  apply measurable_iterateWeights c p cfg.mainSlots cfg.mainEquiv
    cfg.layerOrigin cfg.mainDesignated cfg.mainResidual cfg.mainAuxiliary
    (fun old _ saved => PrivateSamplingProgram.finish cfg old (saved outputDirect))
    main (fun x {Δ} old _ saved => SourceExecutableShift.samplingFinal cfg old
      (saved outputDirect) (final x) (reserve x))
  · exact hm
  · intro Δ old direct saved
    exact measurable_samplingFinal cfg old (saved outputDirect) final reserve hf hr

theorem measurable_samplingWeights {n C : ℕ} {c cf : Fin n → ℕ}
    {p : ∀ i, Program (c i) .point}
    {pf : ∀ i, Program (cf i) .point}
    (cfg : PrivateSamplingProgram.Config n C c cf p pf)
    (position : X → ℝ)
    (main : X → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (final : X → ∀ i, Fin (tapeShape (pf i)).gaussianBlocks → ℝ)
    (reserve : X → ℝ) (hp : Measurable position)
    (hm : Measurable main) (hf : Measurable final)
    (hr : Measurable reserve) :
    Measurable (fun x => SourceExecutableShift.sampling cfg
      (position x) (main x) (final x) (reserve x)) := by
  apply measurable_pi_iff.mpr
  intro s
  cases s with
  | inl s => exact nomatch s
  | inr s =>
      cases s with
      | inl _ => exact hp
      | inr s =>
          cases s with
          | inl s => exact nomatch s
          | inr s =>
              cases s with
              | inl s => exact nomatch s
              | inr s =>
                  cases s with
                  | inl _ => exact measurable_const
                  | inr s =>
                      exact (measurable_pi_apply s).comp
                        (measurable_samplingBody cfg batchRef
                          (RefMap.shiftMany n .here) main final reserve hm hf hr)

theorem measurable_meanBlock {n m C : ℕ} {Γ : Ctx}
    (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (mainSlots : Fin (publicSize c p) → Fin C)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (cf : Fin m → ℕ) (pf : ∀ i, Program (cf i) .point)
    (ef : ∀ i, GaussianSlot (pf i) ≃ Fin (tapeShape (pf i)).gaussianBlocks)
    (finalSlots : ∀ i, Fin (childSize (pf i)) → Fin C)
    (correctionSlots : Fin (1+(m+m)) → Fin C) (rhoSlot : Fin C)
    (P : Ref Γ .point) (designated : Fin m → Ref Γ .point)
    (direct : Fin n → Ref Γ .point) (active : Fin m → Fin n)
    (initialOrigin : Fin n → Origin) (outer : ℕ → Origin)
    (mainDesignated residual : ℕ → Fin n → Origin)
    (auxiliary : ℕ → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (finalOuter : Origin)
    (finalAuxiliary : ∀ i, Fin (tapeShape (pf i)).gaussianBlocks → Origin)
    (N : ℕ) (raw : X → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (hraw : Measurable raw) :
    Measurable (fun x => SourceExecutableShift.meanBlock c p mainSlots e cf pf ef
      finalSlots correctionSlots rhoSlot P designated direct active initialOrigin
      outer mainDesignated residual auxiliary finalOuter finalAuxiliary N (raw x)) := by
  unfold SourceExecutableShift.meanBlock
  apply measurable_initializeWeights
  apply measurable_iterateWeights c p mainSlots e outer mainDesignated residual auxiliary
    (fun old _ saved => RetainedMeanFinalBatch.paidCorrection cf pf ef finalSlots
      correctionSlots (saved P) (fun i => old (active i))
      (fun i => saved (designated i)) finalOuter finalAuxiliary)
    raw (fun _ {_} _ _ _ _ => 0)
  · exact hraw
  · intro Δ old direct saved
    exact measurable_const

theorem measurable_meanPrefix {order a h m n C privateC : ℕ}
    {Γ : Ctx} {τ : Ty}
    (M : Numerics.AffineGraph.MeanGeometry order)
    (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin order × M.Kernel)
    (privateCode : Program privateC .point)
    (privateSlots : Fin privateC → Fin C) (scaleSlot : Fin C)
    (x P : Ref Γ .point)
    (assemblySlots : Fin ((m+1)*(m+1)+(m+1)) → Fin C)
    (assemblyOrigins : Fin (m+1) → Origin) (flowOrigins : Fin h → Origin)
    (directSlots : Fin (n*a) → Fin C)
    (next : Prog C (MeanExecutablePrefix.readyCtx n (m+1) h Γ) τ)
    (privateShift : X → GaussianSlot privateCode → ℝ)
    (tail : X → GaussianSlot next → ℝ)
    (hp : Measurable privateShift) (ht : Measurable tail) :
    Measurable (fun z => SourceExecutableShift.meanPrefix M anchors seeds privateC
      privateCode privateSlots scaleSlot x P assemblySlots assemblyOrigins flowOrigins
      directSlots next (privateShift z) (tail z)) := by
  apply measurable_pi_iff.mpr
  intro s
  cases s with
  | inl s =>
      have h := measurable_lowerWeights privateSlots privateCode
        (fun r => nomatch r) x P privateShift hp
      exact (measurable_pi_apply s.2).comp h
  | inr s =>
      cases s with
      | inl _ => exact measurable_const
      | inr s =>
          cases s with
          | inl _ => exact measurable_const
          | inr s =>
              cases s with
              | inl _ => exact measurable_const
              | inr s =>
                  cases s with
                  | inl _ => exact measurable_const
                  | inr s =>
                      cases s with
                      | inl _ => exact measurable_const
                      | inr s => exact (measurable_pi_apply s).comp ht

theorem measurable_meanAssemblyTable {f : ℕ}
    (a : X → Fin f → ℝ) (ha : Measurable a) :
    Measurable (fun x => MeanGaussianSetup.table (a x)) := by
  have hroot : Measurable (fun x => MeanGaussianSetup.inputRoot (a x)) := by
    have hcov : Measurable (fun x =>
        (1 - Matrix.vecMulVec (a x) (a x) : Matrix (Fin f) (Fin f) ℝ)) := by
      apply measurable_pi_iff.mpr
      intro i
      apply measurable_pi_iff.mpr
      intro j
      dsimp [Matrix.vecMulVec]
      fun_prop
    exact CFC.measurable_sqrt.comp hcov
  exact measurable_matrixTable (fun x => MeanGaussianSetup.inputRoot (a x))
    a hroot ha

theorem measurable_centerForm {order : ℕ}
    (M : Numerics.AffineGraph.MeanGeometry order)
    (r sigma : X → ℝ) (i : M.MeanNode) (a : M.Atom)
    (hr : Measurable r) (hs : Measurable sigma) :
    Measurable (fun x => M.centerForm (r x) (sigma x) i a) := by
  rcases i with _ | b | ⟨b,k⟩ | ⟨b,ρ,k⟩ | ⟨b,ρ,z,k⟩
  all_goals simp only [Numerics.AffineGraph.MeanGeometry.centerForm,
    Numerics.AffineGraph.MeanGeometry.positionForm,
    Numerics.AffineGraph.MeanGeometry.velocityForm,
    Numerics.AffineGraph.MeanGeometry.scoreForm,
    Numerics.AffineGraph.MeanGeometry.backwardForm,
    Numerics.AffineGraph.MeanGeometry.conditionalForm,
    Numerics.AffineGraph.MeanGeometry.observationForm,
    Numerics.AffineGraph.MeanGeometry.midpointForm,
    Numerics.AffineGraph.MeanGeometry.rotationForm,
    Numerics.AffineGraph.MeanGeometry.forwardForm,
    Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Finset.sum_apply]
  all_goals fun_prop

theorem measurable_prefixTable {order n a f privateC : ℕ}
    (M : Numerics.AffineGraph.MeanGeometry order)
    (nodes : Fin n ≃ M.MeanNode) (anchors : Fin a ≃ M.Anchor)
    (r sigma : X → ℝ)
    (privateCoeff : X → Fin privateC → ℝ)
    (assembly : X → Fin f → ℝ)
    (hr : Measurable r) (hs : Measurable sigma)
    (hc : Measurable privateCoeff) (ha : Measurable assembly) :
    Measurable (fun x => PrefixPublicTable.table M nodes anchors
      (r x) (sigma x) (privateCoeff x) (assembly x)) := by
  unfold PrefixPublicTable.table
  apply measurable_fin_append _ _ hc
  apply measurable_fin_append
  · exact measurable_const
  apply measurable_fin_append
  · exact measurable_meanAssemblyTable assembly ha
  apply measurable_pi_iff.mpr
  intro j
  dsimp [PrefixDirect.table]
  exact measurable_centerForm M r sigma _ _ hr hs

theorem measurable_retainedCorrectionTable {m : ℕ}
    (sigma : X → ℝ) (omega width : X → Fin m → ℝ)
    (hs : Measurable sigma) (ho : Measurable omega)
    (hw : Measurable width) :
    Measurable (fun x => RetainedMeanCorrection.table (sigma x)
      (omega x) (width x)) := by
  unfold RetainedMeanCorrection.table
  apply measurable_fin_append
  · exact measurable_pi_iff.mpr (fun _ => hs)
  apply measurable_fin_append _ _ ho
  apply measurable_pi_iff.mpr
  intro i
  exact (((measurable_pi_apply i).comp ho).mul
    ((measurable_pi_apply i).comp hw)).neg

theorem measurable_bodyTable {L F m : ℕ}
    (rho sigma : X → ℝ) (layer : X → Fin L → ℝ)
    (final : X → Fin F → ℝ) (omega width : X → Fin m → ℝ)
    (hr : Measurable rho) (hs : Measurable sigma)
    (hl : Measurable layer) (hf : Measurable final)
    (ho : Measurable omega) (hw : Measurable width) :
    Measurable (fun x => RecursiveMeanPublicTable.table (rho x)
      (layer x) (final x) (sigma x) (omega x) (width x)) := by
  unfold RecursiveMeanPublicTable.table
  apply measurable_fin_append
  · exact measurable_pi_iff.mpr (fun _ => hr)
  apply measurable_fin_append _ _ hl
  apply measurable_fin_append _ _ hf
  exact measurable_retainedCorrectionTable sigma omega width hs ho hw

theorem measurable_samplingMainTable
    (S : SamplingGeometry ms) (nodes : Fin ns ≃ S.Node)
    (mainShape : Fin ns → Shape)
    (mainData : ∀ i, X → Payload (mainShape i))
    (r Ds : X → ℝ)
    (hm : ∀ i, Measurable (mainData i))
    (hr : Measurable r) (hDs : Measurable Ds) :
    Measurable (fun x => (show Fin (publicSize
      (fun i => (mainShape i).1) (fun i => (mainShape i).2)) → ℝ from
      SourceExecutableTables.samplingMainTable
        S nodes (r x) (Ds x)
        (fun i => reconstruct (mainShape i) (mainData i x)))) := by
  let c : Fin ns → ℕ := fun i => (mainShape i).1
  let p : ∀ i, Program (c i) .point := fun i => (mainShape i).2
  let A : X → CovarianceSetup.Mat ns := fun x =>
    SourceExecutableTables.samplingMatrix S nodes (r x)
  have hA : Measurable A := by
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro j
    dsimp [A, SourceExecutableTables.samplingMatrix]
    fun_prop
  let radius : X → Fin ns → ℝ := fun x i => S.radius (r x) (nodes i)
  have hrad : Measurable radius := by
    apply measurable_pi_iff.mpr
    intro i
    dsimp [radius, SamplingGeometry.radius]
    fun_prop
  let shift : X → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → ℝ :=
    fun x i => (reconstruct (mainShape i) (mainData i x)).shiftVector
  have hs : Measurable shift := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_reconstruct_shiftVector (mainShape i) (mainData i) (hm i)
  let coeff : X → ∀ i, Fin (c i) → ℝ :=
    fun x i => (reconstruct (mainShape i) (mainData i x)).coefficient
  have hc : Measurable coeff := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_reconstruct_coefficient (mainShape i) (mainData i) (hm i)
  exact measurable_sourceLayerTable c p A r (fun _ => S.R) Ds
    (fun x => (r x) ^ 2) radius shift coeff hA hr measurable_const
    hDs (hr.pow_const 2) hrad hs hc

theorem measurable_samplingFinalTable
    (S : SamplingGeometry ms) (nodes : Fin ns ≃ S.Node)
    (finalShape : Fin ns → Shape)
    (finalData : ∀ i, X → Payload (finalShape i))
    (r Ds : X → ℝ)
    (hf : ∀ i, Measurable (finalData i))
    (hr : Measurable r) (hDs : Measurable Ds) :
    Measurable (fun x => (show Fin (RecursiveMeanPublicTable.finalSize
      (fun i => (finalShape i).1) (fun i => (finalShape i).2)) → ℝ from
      SourceExecutableTables.samplingFinalTable S nodes (r x) (Ds x)
        (fun i => reconstruct (finalShape i) (finalData i x)))) := by
  let c : Fin ns → ℕ := fun i => (finalShape i).1
  let p : ∀ i, Program (c i) .point := fun i => (finalShape i).2
  let rho : X → ℝ := fun x => SourceExecutableTables.samplingNoise S (r x) (Ds x)
  have hrho : Measurable rho := by
    dsimp [rho, SourceExecutableTables.samplingNoise,
      RecursiveMeanPublicTable.centerNoise]
    fun_prop
  let radius : X → Fin ns → ℝ := fun x i => S.radius (r x) (nodes i)
  have hrad : Measurable radius := by
    apply measurable_pi_iff.mpr
    intro i
    dsimp [radius, SamplingGeometry.radius]
    fun_prop
  let shift : X → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → ℝ :=
    fun x i => (reconstruct (finalShape i) (finalData i x)).shiftVector
  have hs : Measurable shift := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_reconstruct_shiftVector (finalShape i) (finalData i) (hf i)
  let coeff : X → ∀ i, Fin (c i) → ℝ :=
    fun x i => (reconstruct (finalShape i) (finalData i x)).coefficient
  have hc : Measurable coeff := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_reconstruct_coefficient (finalShape i) (finalData i) (hf i)
  have hchild : Measurable (fun x => fun i => CovarianceSetup.childRoot
      (rho x) (radius x i) (shift x i)) := by
    apply measurable_pi_iff.mpr
    intro i
    exact CovarianceSetup.measurable_childRoot rho
      (fun x => radius x i) (fun x => shift x i) hrho
      ((measurable_pi_apply i).comp hrad)
      ((measurable_pi_apply i).comp hs)
  exact measurable_finalTable c p
    (fun x i => CovarianceSetup.childRoot (rho x) (radius x i) (shift x i))
    coeff hchild hc

theorem measurable_samplingScalarTable
    (S : SamplingGeometry ms) (nodes : Fin ns ≃ S.Node)
    (r Ds : X → ℝ) (hr : Measurable r) (hDs : Measurable Ds) :
    Measurable (fun x => SourceExecutableTables.samplingScalarTable S nodes (r x) (Ds x)) := by
  unfold SourceExecutableTables.samplingScalarTable
  apply measurable_fin_append
  · apply measurable_pi_iff.mpr
    intro i
    fun_prop
  · apply measurable_fin_append
    · apply measurable_pi_iff.mpr
      intro i
      dsimp [SourceExecutableTables.samplingFinalWeight]
      fun_prop
    · apply measurable_pi_iff.mpr
      intro i
      split_ifs
      all_goals
        try unfold SourceExecutableTables.samplingNoise
        try unfold SourceExecutableTables.samplingBeta
        try unfold SourceExecutableTables.samplingFinalWeight
        try unfold SourceExecutableTables.samplingFinalWidth
        try unfold RecursiveMeanPublicTable.centerNoise
        fun_prop

def samplingFamily (S : SamplingGeometry ms) (nodes : Fin ns ≃ S.Node)
    (mainShape finalShape : Fin ns → Shape)
    (mainData : ∀ i, X → Payload (mainShape i))
    (finalData : ∀ i, X → Payload (finalShape i))
    (r Ds : X → ℝ) (layers : ℕ) (x : X) : ExecutableData :=
  SamplingExecutable.build S nodes (r x) (Ds x)
    (fun i => reconstruct (mainShape i) (mainData i x))
    (fun i => reconstruct (finalShape i) (finalData i x)) layers

theorem samplingFamily_coefficient_measurable
    (S : SamplingGeometry ms) (nodes : Fin ns ≃ S.Node)
    (mainShape finalShape : Fin ns → Shape)
    (mainData : ∀ i, X → Payload (mainShape i))
    (finalData : ∀ i, X → Payload (finalShape i))
    (r Ds : X → ℝ) (layers : ℕ)
    (hm : ∀ i, Measurable (mainData i))
    (hf : ∀ i, Measurable (finalData i))
    (hr : Measurable r) (hDs : Measurable Ds) :
    Measurable (fun x => (show Fin (SourceExecutableTables.samplingSize
      (fun i => canonicalData (mainShape i))
      (fun i => canonicalData (finalShape i))) → ℝ from
      (samplingFamily S nodes mainShape finalShape mainData finalData r Ds layers x).coefficient)) := by
  change Measurable (fun x => Fin.append
    (SourceExecutableTables.samplingScalarTable S nodes (r x) (Ds x))
    (Fin.append
      (show Fin (publicSize (fun i => (mainShape i).1)
        (fun i => (mainShape i).2)) → ℝ from
        SourceExecutableTables.samplingMainTable S nodes (r x) (Ds x)
          (fun i => reconstruct (mainShape i) (mainData i x)))
      (show Fin (RecursiveMeanPublicTable.finalSize
        (fun i => (finalShape i).1) (fun i => (finalShape i).2)) → ℝ from
        SourceExecutableTables.samplingFinalTable S nodes (r x) (Ds x)
          (fun i => reconstruct (finalShape i) (finalData i x)))))
  exact measurable_fin_append _ _
    (measurable_samplingScalarTable S nodes r Ds hr hDs)
    (measurable_fin_append _ _
      (measurable_samplingMainTable S nodes mainShape mainData r Ds hm hr hDs)
      (measurable_samplingFinalTable S nodes finalShape finalData r Ds hf hr hDs))

theorem measurable_samplingRaw
    (S : SamplingGeometry ms) (nodes : Fin ns ≃ S.Node)
    (childShape : Fin ns → Shape)
    (childData : ∀ i, X → Payload (childShape i))
    (r Ds : X → ℝ)
    (hc : ∀ i, Measurable (childData i))
    (hr : Measurable r) (hDs : Measurable Ds) :
    Measurable (fun x => (show ∀ i, Fin (tapeShape (childShape i).2).gaussianBlocks → ℝ
      from fun i => SamplingExecutable.raw S nodes (r x) (Ds x)
        (fun j => reconstruct (childShape j) (childData j x)) i)) := by
  apply measurable_pi_iff.mpr
  intro i
  let rho : X → ℝ := fun x => SourceExecutableTables.samplingNoise S (r x) (Ds x)
  have hrho : Measurable rho := by
    dsimp [rho, SourceExecutableTables.samplingNoise,
      RecursiveMeanPublicTable.centerNoise]
    fun_prop
  let radius : X → ℝ := fun x => S.radius (r x) (nodes i)
  have hrad : Measurable radius := by
    dsimp [radius, SamplingGeometry.radius]
    fun_prop
  let k : X → ℝ := fun x =>
    1 - S.mesh.location ms (nodes i) * samplingEnd S.τ
  have hk : Measurable k := measurable_const
  exact measurable_rawShift (N := (tapeShape (childShape i).2).gaussianBlocks)
    rho radius r k
    (fun x => (reconstruct (childShape i) (childData i x)).shiftVector)
    hrho hrad hr hk
    (measurable_reconstruct_shiftVector (childShape i) (childData i) (hc i))

theorem samplingFamily_shift_measurable
    (S : SamplingGeometry ms) (nodes : Fin ns ≃ S.Node)
    (mainShape finalShape : Fin ns → Shape)
    (mainData : ∀ i, X → Payload (mainShape i))
    (finalData : ∀ i, X → Payload (finalShape i))
    (r Ds : X → ℝ) (layers : ℕ)
    (hm : ∀ i, Measurable (mainData i))
    (hf : ∀ i, Measurable (finalData i))
    (hr : Measurable r) (hDs : Measurable Ds) :
    Measurable (fun x => (show GaussianSlot
      (SamplingExecutable.build S nodes 0 0
        (fun i => canonicalData (mainShape i))
        (fun i => canonicalData (finalShape i)) layers).program → ℝ
      from (samplingFamily S nodes mainShape finalShape mainData finalData r Ds layers x).shift)) := by
  change Measurable (fun x => (show GaussianSlot
    (SamplingExecutable.build S nodes 0 0
      (fun i => canonicalData (mainShape i))
      (fun i => canonicalData (finalShape i)) layers).program → ℝ from
    SourceExecutableShift.sampling
    (SourceExecutableTables.samplingConfig
      (fun i => reconstruct (mainShape i) (mainData i x))
      (fun i => reconstruct (finalShape i) (finalData i x)) layers)
    (-(samplingEnd S.τ))
    (SamplingExecutable.raw S nodes (r x) (Ds x)
      (fun i => reconstruct (mainShape i) (mainData i x)))
    (SamplingExecutable.raw S nodes (r x) (Ds x)
      (fun i => reconstruct (finalShape i) (finalData i x))) 0))
  exact measurable_samplingWeights _ _ _ _ _ measurable_const
    (measurable_samplingRaw S nodes mainShape mainData r Ds hm hr hDs)
    (measurable_samplingRaw S nodes finalShape finalData r Ds hf hr hDs)
    measurable_const

def samplingAugmentedPayload
    (S : SamplingGeometry ms) (nodes : Fin ns ≃ S.Node)
    (mainShape finalShape : Fin ns → Shape)
    (mainData : ∀ i, X → Payload (mainShape i))
    (finalData : ∀ i, X → Payload (finalShape i))
    (r Ds reserve : X → ℝ) (layers : ℕ) (x : X) :
    Payload (shape (SamplingExecutable.build S nodes 0 0
      (fun i => canonicalData (mainShape i))
      (fun i => canonicalData (finalShape i)) layers)) :=
  ⟨(samplingFamily S nodes mainShape finalShape mainData finalData
      r Ds layers x).coefficient,
    SamplingExecutable.weights S nodes (r x) (Ds x)
      (fun i => reconstruct (mainShape i) (mainData i x))
      (fun i => reconstruct (finalShape i) (finalData i x))
      layers (reserve x)⟩

theorem samplingAugmentedPayload_measurable
    (S : SamplingGeometry ms) (nodes : Fin ns ≃ S.Node)
    (mainShape finalShape : Fin ns → Shape)
    (mainData : ∀ i, X → Payload (mainShape i))
    (finalData : ∀ i, X → Payload (finalShape i))
    (r Ds reserve : X → ℝ) (layers : ℕ)
    (hm : ∀ i, Measurable (mainData i))
    (hf : ∀ i, Measurable (finalData i))
    (hr : Measurable r) (hDs : Measurable Ds)
    (hres : Measurable reserve) :
    Measurable (samplingAugmentedPayload S nodes mainShape finalShape
      mainData finalData r Ds reserve layers) := by
  apply Measurable.prodMk
  · exact samplingFamily_coefficient_measurable S nodes mainShape finalShape
      mainData finalData r Ds layers hm hf hr hDs
  · change Measurable (fun x => (show GaussianSlot
      (SamplingExecutable.build S nodes 0 0
        (fun i => canonicalData (mainShape i))
        (fun i => canonicalData (finalShape i)) layers).program → ℝ from
      SourceExecutableShift.sampling
      (SourceExecutableTables.samplingConfig
        (fun i => reconstruct (mainShape i) (mainData i x))
        (fun i => reconstruct (finalShape i) (finalData i x)) layers)
      (-(samplingEnd S.τ))
      (SamplingExecutable.raw S nodes (r x) (Ds x)
        (fun i => reconstruct (mainShape i) (mainData i x)))
      (SamplingExecutable.raw S nodes (r x) (Ds x)
        (fun i => reconstruct (finalShape i) (finalData i x))) (reserve x)))
    exact measurable_samplingWeights _ _ _ _ _ measurable_const
      (measurable_samplingRaw S nodes mainShape mainData r Ds hm hr hDs)
      (measurable_samplingRaw S nodes finalShape finalData r Ds hf hr hDs)
      hres

omit [MeasurableSpace X] in
theorem reconstruct_samplingAugmented_zero
    (S : SamplingGeometry ms) (nodes : Fin ns ≃ S.Node)
    (mainShape finalShape : Fin ns → Shape)
    (mainData : ∀ i, X → Payload (mainShape i))
    (finalData : ∀ i, X → Payload (finalShape i))
    (r Ds : X → ℝ) (layers : ℕ) (x : X) :
    reconstruct _ (samplingAugmentedPayload S nodes mainShape finalShape
      mainData finalData r Ds (fun _ => 0) layers x) =
    SamplingExecutable.build S nodes (r x) (Ds x)
      (fun i => reconstruct (mainShape i) (mainData i x))
      (fun i => reconstruct (finalShape i) (finalData i x)) layers := rfl

theorem measurable_realRpow (a b : X → ℝ)
    (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun x => (a x).rpow (b x)) := by
  have h : Measurable (fun x =>
      if 0 ≤ a x then
        if a x = 0 then if b x = 0 then (1 : ℝ) else 0
        else Real.exp (Real.log (a x) * b x)
      else Real.exp (Real.log (a x) * b x) * Real.cos (b x * Real.pi)) := by
    apply Measurable.ite (by measurability)
    · apply Measurable.ite (by measurability)
      · apply Measurable.ite (by measurability) measurable_const measurable_const
      · fun_prop
    · fun_prop
  convert h using 1
  funext x
  by_cases hx : 0 ≤ a x
  · simp only [hx, ite_true]
    exact Real.rpow_def_of_nonneg hx (b x)
  · have hneg : a x < 0 := lt_of_not_ge hx
    simp only [hx, ite_false]
    exact Real.rpow_def_of_neg hneg (b x)

theorem measurable_meanRowBound {m : ℕ}
    (r sigma delta t w : X → ℝ)
    (hr : Measurable r) (hs : Measurable sigma)
    (hd : Measurable delta) (ht : Measurable t)
    (hw : Measurable w) :
    Measurable (fun x => SourceMeanExecutable.rowBound (m := m)
      (r x) (sigma x) (delta x) (t x) (w x)) := by
  unfold SourceMeanExecutable.rowBound
  have hp : Measurable (fun x => (delta x).rpow (-4 * t x - w x)) :=
    measurable_realRpow delta (fun x => -4 * t x - w x)
      hd (by fun_prop)
  fun_prop

theorem measurable_meanAssembly {m : ℕ}
    (M : Numerics.AffineGraph.MeanGeometry m) :
    Measurable (fun _ : X => SourceMeanExecutable.assembly M) := measurable_const

theorem measurable_meanMainTable {m n : ℕ}
    (M : Numerics.AffineGraph.MeanGeometry m)
    (nodes : Fin n ≃ M.MeanNode)
    (childShape : Fin n → Shape)
    (childData : ∀ i, X → Payload (childShape i))
    (r sigma Ds delta t w : X → ℝ)
    (hc : ∀ i, Measurable (childData i))
    (hr : Measurable r) (hs : Measurable sigma)
    (hDs : Measurable Ds) (hd : Measurable delta)
    (ht : Measurable t) (hw : Measurable w) :
    Measurable (fun x => (show Fin (publicSize
      (fun i => (childShape i).1) (fun i => (childShape i).2)) → ℝ from
      SourceMeanExecutable.mainTable M nodes (r x) (sigma x)
        (Ds x) (delta x) (t x) (w x)
        (fun i => reconstruct (childShape i) (childData i x)))) := by
  let A : X → CovarianceSetup.Mat n := fun x i j =>
    M.matrix (r x) (sigma x) (nodes i) (nodes j)
  have hA : Measurable A := by
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_centerForm M r sigma (nodes i) (.inr (nodes j)) hr hs
  let rad : X → Fin n → ℝ := fun x i => M.radius (r x) (nodes i)
  have hrad : Measurable rad := by
    apply measurable_pi_iff.mpr
    intro i
    dsimp [rad]
    rcases nodes i with _ | b | ⟨b,k⟩ | ⟨b,ρ,k⟩ | ⟨b,ρ,z,k⟩ <;>
      simp only [Numerics.AffineGraph.MeanGeometry.radius] <;> fun_prop
  let sh : X → ∀ i, Fin (tapeShape (childShape i).2).gaussianBlocks → ℝ :=
    fun x i => (reconstruct (childShape i) (childData i x)).shiftVector
  have hsh : Measurable sh := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_reconstruct_shiftVector (childShape i) (childData i) (hc i)
  let co : X → ∀ i, Fin (childShape i).1 → ℝ :=
    fun x i => (childData i x).1
  have hco : Measurable co := by
    apply measurable_pi_iff.mpr
    intro i
    exact (hc i).fst
  exact measurable_sourceLayerTable _ _ A r (fun _ => M.R) Ds
    (fun x => SourceMeanExecutable.rowBound (m := m)
      (r x) (sigma x) (delta x) (t x) (w x))
    rad sh co hA hr measurable_const hDs
    (measurable_meanRowBound r sigma delta t w hr hs hd ht hw)
    hrad hsh hco

theorem measurable_meanFinalTable {m : ℕ}
    (M : Numerics.AffineGraph.MeanGeometry m)
    (childShape : Fin m → Shape)
    (childData : ∀ i, X → Payload (childShape i))
    (r Ds : X → ℝ)
    (hc : ∀ i, Measurable (childData i))
    (hr : Measurable r) (hDs : Measurable Ds) :
    Measurable (fun x => (show Fin (RecursiveMeanPublicTable.finalSize
      (fun i => (childShape i).1) (fun i => (childShape i).2)) → ℝ from
      SourceMeanExecutable.finalTable M (r x) (Ds x)
        (fun i => reconstruct (childShape i) (childData i x)))) := by
  let sh : X → ∀ i, Fin (tapeShape (childShape i).2).gaussianBlocks → ℝ :=
    fun x i => (reconstruct (childShape i) (childData i x)).shiftVector
  have hsh : Measurable sh := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_reconstruct_shiftVector (childShape i) (childData i) (hc i)
  let co : X → ∀ i, Fin (childShape i).1 → ℝ :=
    fun x i => (childData i x).1
  have hco : Measurable co := by
    apply measurable_pi_iff.mpr
    intro i
    exact (hc i).fst
  exact measurable_sourceFinalTable _ _ r (fun _ => M.R) Ds sh co
    hr measurable_const hDs hsh hco

def meanFamily {m n a h : ℕ}
    (M : Numerics.AffineGraph.MeanGeometry m)
    (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor)
    (seeds : Fin h ≃ Fin m × M.Kernel)
    (mainShape : Fin n → Shape) (finalShape : Fin m → Shape)
    (privateShape : Shape)
    (mainData : ∀ i, X → Payload (mainShape i))
    (finalData : ∀ i, X → Payload (finalShape i))
    (privateData : X → Payload privateShape)
    (privateShift : X → GaussianSlot privateShape.2 → ℝ)
    (r sigma Ds delta t w : X → ℝ)
    (layers : ℕ) (x : X) : ExecutableData :=
  SourceMeanExecutable.build M nodes anchors seeds
    (r x) (sigma x) (Ds x) (delta x) (t x) (w x)
    (fun i => reconstruct (mainShape i) (mainData i x))
    (fun i => reconstruct (finalShape i) (finalData i x))
    (reconstruct privateShape (privateData x)) layers (privateShift x)

theorem meanFamily_coefficient_measurable {m n a h : ℕ}
    (M : Numerics.AffineGraph.MeanGeometry m)
    (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor)
    (seeds : Fin h ≃ Fin m × M.Kernel)
    (mainShape : Fin n → Shape) (finalShape : Fin m → Shape)
    (privateShape : Shape)
    (mainData : ∀ i, X → Payload (mainShape i))
    (finalData : ∀ i, X → Payload (finalShape i))
    (privateData : X → Payload privateShape)
    (privateShift : X → GaussianSlot privateShape.2 → ℝ)
    (r sigma Ds delta t w : X → ℝ) (layers : ℕ)
    (hm : ∀ i, Measurable (mainData i))
    (hf : ∀ i, Measurable (finalData i))
    (hp : Measurable privateData)
    (hr : Measurable r) (hs : Measurable sigma)
    (hDs : Measurable Ds) (hd : Measurable delta)
    (ht : Measurable t) (hw : Measurable w) :
    Measurable (fun x => (show Fin
      (SourceMeanExecutable.size
        (fun i => canonicalData (mainShape i))
        (fun i => canonicalData (finalShape i))
        (canonicalData privateShape)) → ℝ from
      (meanFamily M nodes anchors seeds mainShape finalShape privateShape
        mainData finalData privateData privateShift r sigma Ds delta t w layers x).coefficient)) := by
  change Measurable (fun x => Fin.append
    (PrefixPublicTable.table M nodes anchors (r x) (sigma x)
      (privateData x).1 (SourceMeanExecutable.assembly M))
    (RecursiveMeanPublicTable.table
      (RecursiveMeanPublicTable.centerNoise (r x) M.R (Ds x))
      (show Fin (publicSize
        (fun i => (mainShape i).1) (fun i => (mainShape i).2)) → ℝ from
       SourceMeanExecutable.mainTable M nodes (r x) (sigma x) (Ds x)
        (delta x) (t x) (w x)
        (fun i => reconstruct (mainShape i) (mainData i x)))
      (show Fin (RecursiveMeanPublicTable.finalSize
        (fun i => (finalShape i).1) (fun i => (finalShape i).2)) → ℝ from
       SourceMeanExecutable.finalTable M (r x) (Ds x)
        (fun i => reconstruct (finalShape i) (finalData i x)))
      (sigma x) (Numerics.GaussLegendre.weight m)
      (fun _ => RecursiveMeanPublicTable.finalWidth M.R (sigma x))))
  apply measurable_fin_append
  · exact measurable_prefixTable M nodes anchors r sigma
      (fun x => (privateData x).1) (fun _ => SourceMeanExecutable.assembly M)
      hr hs hp.fst measurable_const
  · apply measurable_bodyTable
    · dsimp [RecursiveMeanPublicTable.centerNoise]
      fun_prop
    · exact hs
    · exact measurable_meanMainTable M nodes mainShape mainData
        r sigma Ds delta t w hm hr hs hDs hd ht hw
    · exact measurable_meanFinalTable M finalShape finalData r Ds hf hr hDs
    · exact measurable_const
    · apply measurable_pi_iff.mpr
      intro i
      dsimp [RecursiveMeanPublicTable.finalWidth,
        RecursiveMeanPublicTable.finalNoise]
      fun_prop

theorem measurable_meanRaw {m n : ℕ}
    (M : Numerics.AffineGraph.MeanGeometry m)
    (nodes : Fin n ≃ M.MeanNode)
    (childShape : Fin n → Shape)
    (childData : ∀ i, X → Payload (childShape i))
    (r sigma Ds : X → ℝ)
    (hc : ∀ i, Measurable (childData i))
    (hr : Measurable r) (hs : Measurable sigma)
    (hDs : Measurable Ds) :
    Measurable (fun x => (show ∀ i,
      Fin (tapeShape (childShape i).2).gaussianBlocks → ℝ from
      fun i => SourceMeanExecutable.mainRaw M nodes (r x) (sigma x) (Ds x)
        (fun j => reconstruct (childShape j) (childData j x)) i)) := by
  apply measurable_pi_iff.mpr
  intro i
  let rho : X → ℝ := fun x => RecursiveMeanPublicTable.centerNoise (r x) M.R (Ds x)
  have hrho : Measurable rho := by
    dsimp [rho, RecursiveMeanPublicTable.centerNoise]
    fun_prop
  let radius : X → ℝ := fun x => M.radius (r x) (nodes i)
  have hrad : Measurable radius := by
    dsimp [radius]
    rcases nodes i with _ | b | ⟨b,k⟩ | ⟨b,ρ,k⟩ | ⟨b,ρ,z,k⟩ <;>
      simp only [Numerics.AffineGraph.MeanGeometry.radius] <;> fun_prop
  let k : X → ℝ := fun x => SourceMeanExecutable.centerShift M nodes (r x) (sigma x) i
  have hk : Measurable k := by
    dsimp [k, SourceMeanExecutable.centerShift]
    have hform := measurable_centerForm M r sigma (nodes i) M.positionAtom hr hs
    fun_prop
  exact measurable_rawShift (N := (tapeShape (childShape i).2).gaussianBlocks)
    rho radius r k
    (fun x => (reconstruct (childShape i) (childData i x)).shiftVector)
    hrho hrad hr hk
    (measurable_reconstruct_shiftVector (childShape i) (childData i) (hc i))

theorem meanFamily_shift_measurable {m n a h : ℕ}
    (M : Numerics.AffineGraph.MeanGeometry m)
    (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor)
    (seeds : Fin h ≃ Fin m × M.Kernel)
    (mainShape : Fin n → Shape) (finalShape : Fin m → Shape)
    (privateShape : Shape)
    (mainData : ∀ i, X → Payload (mainShape i))
    (finalData : ∀ i, X → Payload (finalShape i))
    (privateData : X → Payload privateShape)
    (privateShift : X → GaussianSlot privateShape.2 → ℝ)
    (r sigma Ds delta t w : X → ℝ) (layers : ℕ)
    (hm : ∀ i, Measurable (mainData i))
    (_hf : ∀ i, Measurable (finalData i))
    (_hp : Measurable privateData)
    (hps : Measurable privateShift)
    (hr : Measurable r) (hs : Measurable sigma)
    (hDs : Measurable Ds) :
    Measurable (fun x => (show GaussianSlot
      (SourceMeanExecutable.build M nodes anchors seeds 0 0 0 0 0 0
        (fun i => canonicalData (mainShape i))
        (fun i => canonicalData (finalShape i))
        (canonicalData privateShape) layers (fun _ => 0)).program → ℝ from
      (meanFamily M nodes anchors seeds mainShape finalShape privateShape
        mainData finalData privateData privateShift r sigma Ds delta t w layers x).shift)) := by
  apply measurable_pi_iff.mpr
  intro s
  cases s with
  | inl s => exact nomatch s
  | inr s =>
      cases s with
      | inl s => exact nomatch s
      | inr s =>
          have hbody : Measurable (fun x => (show GaussianSlot
              (SourceMeanExecutable.body (a := a) (h := h) M nodes
                (fun i => canonicalData (mainShape i))
                (fun i => canonicalData (finalShape i))
                (canonicalData privateShape) layers) → ℝ from
              SourceMeanExecutable.bodyShift (a := a) (h := h) M nodes (r x) (sigma x) (Ds x)
                (fun i => reconstruct (mainShape i) (mainData i x))
                (fun i => reconstruct (finalShape i) (finalData i x))
                (reconstruct privateShape (privateData x)) layers)) := by
            exact measurable_meanBlock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              (measurable_meanRaw M nodes mainShape mainData r sigma Ds hm hr hs hDs)
          have hincoming : Measurable (fun x => (show GaussianSlot
              (SourceMeanExecutable.incoming M nodes anchors seeds
                (fun i => canonicalData (mainShape i))
                (fun i => canonicalData (finalShape i))
                (canonicalData privateShape) layers) → ℝ from
              SourceMeanExecutable.incomingShift M nodes anchors seeds
                (r x) (sigma x) (Ds x)
                (fun i => reconstruct (mainShape i) (mainData i x))
                (fun i => reconstruct (finalShape i) (finalData i x))
                (reconstruct privateShape (privateData x)) layers
                (privateShift x))) := by
            exact measurable_meanPrefix M anchors seeds privateShape.2
              (SourceMeanExecutable.prefixSlot (a := a)
                (fun i => canonicalData (mainShape i))
                (fun i => canonicalData (finalShape i))
                (canonicalData privateShape) ∘ PrefixPublicTable.privateSlot)
              (SourceMeanExecutable.prefixSlot (a := a)
                (fun i => canonicalData (mainShape i))
                (fun i => canonicalData (finalShape i))
                (canonicalData privateShape) PrefixPublicTable.scaleSlot)
              (.there .here) .here
              (SourceMeanExecutable.prefixSlot (a := a)
                (fun i => canonicalData (mainShape i))
                (fun i => canonicalData (finalShape i))
                (canonicalData privateShape) ∘ PrefixPublicTable.assemblySlot)
              (SourceMeanExecutable.assemblyOrigin)
              (SourceMeanExecutable.flowOrigin)
              (SourceMeanExecutable.prefixSlot (a := a)
                (fun i => canonicalData (mainShape i))
                (fun i => canonicalData (finalShape i))
                (canonicalData privateShape) ∘ PrefixPublicTable.directSlot)
              (SourceMeanExecutable.body (a := a) (h := h) M nodes
                (fun i => canonicalData (mainShape i))
                (fun i => canonicalData (finalShape i))
                (canonicalData privateShape) layers)
              privateShift
              (fun x => SourceMeanExecutable.bodyShift (a := a) (h := h)
                M nodes (r x) (sigma x) (Ds x)
                (fun i => reconstruct (mainShape i) (mainData i x))
                (fun i => reconstruct (finalShape i) (finalData i x))
                (reconstruct privateShape (privateData x)) layers)
              hps hbody
          exact (measurable_pi_apply s).comp hincoming

theorem meanFamily_payload_measurable {m n a h : ℕ}
    (M : Numerics.AffineGraph.MeanGeometry m)
    (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor)
    (seeds : Fin h ≃ Fin m × M.Kernel)
    (mainShape : Fin n → Shape) (finalShape : Fin m → Shape)
    (privateShape : Shape)
    (mainData : ∀ i, X → Payload (mainShape i))
    (finalData : ∀ i, X → Payload (finalShape i))
    (privateData : X → Payload privateShape)
    (privateShift : X → GaussianSlot privateShape.2 → ℝ)
    (r sigma Ds delta t w : X → ℝ) (layers : ℕ)
    (hm : ∀ i, Measurable (mainData i))
    (hf : ∀ i, Measurable (finalData i))
    (hp : Measurable privateData)
    (hps : Measurable privateShift)
    (hr : Measurable r) (hs : Measurable sigma)
    (hDs : Measurable Ds) (hd : Measurable delta)
    (ht : Measurable t) (hw : Measurable w) :
    Measurable (fun x => (show Payload
      (shape (SourceMeanExecutable.build M nodes anchors seeds 0 0 0 0 0 0
        (fun i => canonicalData (mainShape i))
        (fun i => canonicalData (finalShape i))
        (canonicalData privateShape) layers (fun _ => 0))) from
      payload (meanFamily M nodes anchors seeds mainShape finalShape privateShape
        mainData finalData privateData privateShift r sigma Ds delta t w layers x))) := by
  exact (meanFamily_coefficient_measurable M nodes anchors seeds mainShape finalShape
    privateShape mainData finalData privateData privateShift r sigma Ds delta t w layers
    hm hf hp hr hs hDs hd ht hw).prodMk
    (meanFamily_shift_measurable M nodes anchors seeds mainShape finalShape
      privateShape mainData finalData privateData privateShift r sigma Ds delta t w layers
      hm hf hp hps hr hs hDs)

omit [MeasurableSpace X] in
theorem meanFamily_shape {m n a h : ℕ}
    (M : Numerics.AffineGraph.MeanGeometry m)
    (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor)
    (seeds : Fin h ≃ Fin m × M.Kernel)
    (mainShape : Fin n → Shape) (finalShape : Fin m → Shape)
    (privateShape : Shape)
    (mainData : ∀ i, X → Payload (mainShape i))
    (finalData : ∀ i, X → Payload (finalShape i))
    (privateData : X → Payload privateShape)
    (privateShift : X → GaussianSlot privateShape.2 → ℝ)
    (r sigma Ds delta t w : X → ℝ) (layers : ℕ) (x : X) :
    shape (meanFamily M nodes anchors seeds mainShape finalShape privateShape
      mainData finalData privateData privateShift r sigma Ds delta t w layers x) =
    shape (SourceMeanExecutable.build M nodes anchors seeds 0 0 0 0 0 0
      (fun i => canonicalData (mainShape i))
      (fun i => canonicalData (finalShape i))
      (canonicalData privateShape) layers (fun _ => 0)) := rfl

theorem measurable_meanRadius {m : ℕ}
    (M : Numerics.AffineGraph.MeanGeometry m)
    (r : X → ℝ) (i : M.MeanNode) (hr : Measurable r) :
    Measurable (fun x => M.radius (r x) i) := by
  rcases i with _ | b | ⟨b,k⟩ | ⟨b,ρ,k⟩ | ⟨b,ρ,z,k⟩ <;>
    simp only [Numerics.AffineGraph.MeanGeometry.radius] <;> fun_prop

theorem measurable_samplingRadius {m : ℕ}
    (S : Numerics.AffineGraph.SamplingGeometry m)
    (r : X → ℝ) (i : S.Node) (hr : Measurable r) :
    Measurable (fun x => S.radius (r x) i) := by
  dsimp [Numerics.AffineGraph.SamplingGeometry.radius]
  fun_prop

theorem measurable_mainWidth (n : ℕ)
    (r R Ds A : X → ℝ)
    (hr : Measurable r) (hR : Measurable R)
    (hDs : Measurable Ds) (hA : Measurable A) :
    Measurable (fun x => RecursiveMeanPublicTable.mainWidth n
      (r x) (R x) (Ds x) (A x)) := by
  dsimp [RecursiveMeanPublicTable.mainWidth]
  exact CovarianceSetup.measurable_sigma
    (fun x => RecursiveMeanPublicTable.centerNoise (r x) (R x) (Ds x)) A
    (by dsimp [RecursiveMeanPublicTable.centerNoise]; fun_prop) hA

theorem measurable_finalWidth (R sigma : X → ℝ)
    (hR : Measurable R) (hs : Measurable sigma) :
    Measurable (fun x => RecursiveMeanPublicTable.finalWidth (R x) (sigma x)) := by
  dsimp [RecursiveMeanPublicTable.finalWidth,
    RecursiveMeanPublicTable.finalNoise]
  fun_prop

theorem measurable_samplingFinalWidth {m : ℕ}
    (S : Numerics.AffineGraph.SamplingGeometry m)
    (r : X → ℝ) (hr : Measurable r) :
    Measurable (fun x => SourceExecutableTables.samplingFinalWidth S (r x)) := by
  dsimp [SourceExecutableTables.samplingFinalWidth]
  fun_prop

open Precision
variable {m n a h ms ns : ℕ}
    (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
    (S : SamplingGeometry ms) (snodes : Fin ns ≃ S.Node)
    (Ds δ t w : ℝ) (layers : ℕ) (ht : 0 < t) (htq : t ≤ 1 / 4)

omit [MeasurableSpace X] in
theorem meanCore_measurable_payload_exists (q : ℝ) :
    ∃ s : Shape, ∃ f : (ℝ × ℝ × ℝ) → Payload s,
      Measurable f ∧ ∀ z,
        reconstruct s (f z) =
          meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
            z.1 z.2.1 z.2.2 q := by
  suffices hall : ∀ rank : ℕ, ∀ q : ℝ, precisionRank t q = rank →
      ∃ s : Shape, ∃ f : (ℝ × ℝ × ℝ) → Payload s,
        Measurable f ∧ ∀ z,
          reconstruct s (f z) =
            meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
              z.1 z.2.1 z.2.2 q by
    exact hall _ q rfl
  intro rank
  induction rank using Nat.strong_induction_on with
  | h rank ih =>
      intro q heq
      by_cases hq : q ≤ 1 / 2
      · refine ⟨shape (RecursiveExecutable.terminal 0 0 0),
          (fun z => payload (RecursiveExecutable.terminal z.1 z.2.1 z.2.2)), ?_, ?_⟩
        · simpa [alignedPayload] using terminal_payload_measurable
        · intro z
          change RecursiveExecutable.terminal z.1 z.2.1 z.2.2 = _
          exact (mean_terminal M nodes anchors seeds S snodes Ds δ t w ht htq
            layers z.1 z.2.1 z.2.2 q hq).symm
      · have hq' : (1 / 2 : ℝ) < q := lt_of_not_ge hq
        have hquarter : precisionRank t (q - 1 / 4) < rank := by
          have hd := precisionRank_drop ht hq'
            (show q - 1 / 4 ≤ q - t by linarith)
          omega
        have hfinal : precisionRank t (q - t) < rank := by
          have hd := precisionRank_drop ht hq'
            (show q - t ≤ q - t from le_rfl)
          omega
        obtain ⟨sq, fq, hfq, hrecq⟩ := ih _ hquarter _ rfl
        obtain ⟨st, ft, hft, hrect⟩ := ih _ hfinal _ rfl
        let rz : (ℝ × ℝ × ℝ) → ℝ := fun z => z.2.1
        let sz : (ℝ × ℝ × ℝ) → ℝ := fun z => z.2.2
        have hrz : Measurable rz := measurable_snd.fst
        have hsz : Measurable sz := measurable_snd.snd
        let row : (ℝ × ℝ × ℝ) → ℝ := fun z =>
          SourceMeanExecutable.rowBound (m := m) (rz z) (sz z) δ t w
        have hrow : Measurable row :=
          measurable_meanRowBound rz sz (fun _ => δ) (fun _ => t) (fun _ => w)
            hrz hsz measurable_const measurable_const measurable_const
        let mainWidth : (ℝ × ℝ × ℝ) → ℝ := fun z =>
          RecursiveMeanPublicTable.mainWidth n (rz z) M.R Ds (row z)
        have hmainWidth : Measurable mainWidth :=
          measurable_mainWidth n rz (fun _ => M.R) (fun _ => Ds) row
            hrz measurable_const measurable_const hrow
        let sampleMainWidth : (ℝ × ℝ × ℝ) → ℝ := fun z =>
          RecursiveMeanPublicTable.mainWidth ns (rz z) S.R Ds ((rz z)^2)
        have hsampleMainWidth : Measurable sampleMainWidth :=
          measurable_mainWidth ns rz (fun _ => S.R) (fun _ => Ds)
            (fun z => (rz z)^2) hrz measurable_const measurable_const
            (hrz.pow_const 2)
        let mainData : ∀ i : Fin n, (ℝ × ℝ × ℝ) → Payload sq := fun i z =>
          fq (z.1, M.radius (rz z) (nodes i), mainWidth z)
        have hm : ∀ i, Measurable (mainData i) := by
          intro i
          exact hfq.comp (measurable_fst.prodMk
            ((measurable_meanRadius M rz (nodes i) hrz).prodMk hmainWidth))
        let finalData : ∀ i : Fin m, (ℝ × ℝ × ℝ) → Payload st := fun _ z =>
          ft (z.1, rz z * M.R,
            RecursiveMeanPublicTable.finalWidth M.R (sz z))
        have hfi : ∀ i, Measurable (finalData i) := by
          intro i
          exact hft.comp (measurable_fst.prodMk
            ((hrz.mul_const M.R).prodMk
              (measurable_finalWidth (fun _ => M.R) sz measurable_const hsz)))
        let sampleMainData : ∀ i : Fin ns, (ℝ × ℝ × ℝ) → Payload sq := fun i z =>
          fq (z.1, S.radius (rz z) (snodes i), sampleMainWidth z)
        have hsm : ∀ i, Measurable (sampleMainData i) := by
          intro i
          exact hfq.comp (measurable_fst.prodMk
            ((measurable_samplingRadius S rz (snodes i) hrz).prodMk
              hsampleMainWidth))
        let sampleFinalData : ∀ i : Fin ns, (ℝ × ℝ × ℝ) → Payload sq := fun i z =>
          fq (z.1, S.radius (rz z) (snodes i),
            SourceExecutableTables.samplingFinalWidth S (rz z))
        have hsf : ∀ i, Measurable (sampleFinalData i) := by
          intro i
          exact hfq.comp (measurable_fst.prodMk
            ((measurable_samplingRadius S rz (snodes i) hrz).prodMk
              (measurable_samplingFinalWidth S rz hrz)))
        let sp : Shape := shape (SamplingExecutable.build S snodes 0 0
          (fun _ => canonicalData sq) (fun _ => canonicalData sq) layers)
        let privateData : (ℝ × ℝ × ℝ) → Payload sp :=
          samplingAugmentedPayload S snodes (fun _ => sq) (fun _ => sq)
            sampleMainData sampleFinalData rz (fun _ => Ds) (fun _ => 0) layers
        have hp : Measurable privateData :=
          samplingAugmentedPayload_measurable S snodes (fun _ => sq) (fun _ => sq)
            sampleMainData sampleFinalData rz (fun _ => Ds) (fun _ => 0) layers
            hsm hsf hrz measurable_const measurable_const
        let privateShift : (ℝ × ℝ × ℝ) → GaussianSlot sp.2 → ℝ := fun z =>
          (samplingAugmentedPayload S snodes (fun _ => sq) (fun _ => sq)
            sampleMainData sampleFinalData rz (fun _ => Ds)
            (fun _ => -2 * M.R / backwardEnd M.R) layers z).2
        have hps : Measurable privateShift :=
          (samplingAugmentedPayload_measurable S snodes (fun _ => sq) (fun _ => sq)
            sampleMainData sampleFinalData rz (fun _ => Ds)
            (fun _ => -2 * M.R / backwardEnd M.R) layers
            hsm hsf hrz measurable_const measurable_const).snd
        let s : Shape := shape (SourceMeanExecutable.build M nodes anchors seeds
          0 0 0 0 0 0 (fun _ => canonicalData sq) (fun _ => canonicalData st)
          (canonicalData sp) layers (fun _ => 0))
        let f : (ℝ × ℝ × ℝ) → Payload s := fun z =>
          payload (meanFamily M nodes anchors seeds (fun _ => sq) (fun _ => st) sp
            mainData finalData privateData privateShift rz sz (fun _ => Ds)
            (fun _ => δ) (fun _ => t) (fun _ => w) layers z)
        have hf : Measurable f :=
          meanFamily_payload_measurable M nodes anchors seeds (fun _ => sq)
            (fun _ => st) sp mainData finalData privateData privateShift rz sz
            (fun _ => Ds) (fun _ => δ) (fun _ => t) (fun _ => w) layers
            hm hfi hp hps hrz hsz measurable_const measurable_const
            measurable_const measurable_const
        refine ⟨s, f, hf, ?_⟩
        intro z
        have hmain (i : Fin n) : reconstruct sq (mainData i z) =
            meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
              z.1 (M.radius (rz z) (nodes i)) (mainWidth z) (q - 1 / 4) :=
          hrecq _
        have hfinal (i : Fin m) : reconstruct st (finalData i z) =
            meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
              z.1 (rz z * M.R)
                (RecursiveMeanPublicTable.finalWidth M.R (sz z)) (q - t) :=
          hrect _
        have hsmain (i : Fin ns) : reconstruct sq (sampleMainData i z) =
            meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
              z.1 (S.radius (rz z) (snodes i)) (sampleMainWidth z) (q - 1 / 4) :=
          hrecq _
        have hsfinal (i : Fin ns) : reconstruct sq (sampleFinalData i z) =
            meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
              z.1 (S.radius (rz z) (snodes i))
                (SourceExecutableTables.samplingFinalWidth S (rz z)) (q - 1 / 4) :=
          hrecq _
        change meanFamily M nodes anchors seeds (fun _ => sq) (fun _ => st) sp
          mainData finalData privateData privateShift rz sz (fun _ => Ds)
          (fun _ => δ) (fun _ => t) (fun _ => w) layers z = _
        rw [meanCore, dite_eq_right hq]
        unfold meanFamily
        simp only [hmain, hfinal]
        change SourceMeanExecutable.build M nodes anchors seeds (rz z) (sz z)
            Ds δ t w _ _
            (SamplingExecutable.build S snodes (rz z) Ds
              (fun i => reconstruct sq (sampleMainData i z))
              (fun i => reconstruct sq (sampleFinalData i z)) layers)
            layers
            (SamplingExecutable.weights S snodes (rz z) Ds
              (fun i => reconstruct sq (sampleMainData i z))
              (fun i => reconstruct sq (sampleFinalData i z)) layers
              (-2 * M.R / backwardEnd M.R)) = _
        have hsma : (fun i => reconstruct sq (sampleMainData i z)) =
            (fun i => meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
              z.1 (S.radius (rz z) (snodes i)) (sampleMainWidth z) (q - 1 / 4)) :=
          funext hsmain
        have hsfa : (fun i => reconstruct sq (sampleFinalData i z)) =
            (fun i => meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
              z.1 (S.radius (rz z) (snodes i))
              (SourceExecutableTables.samplingFinalWidth S (rz z)) (q - 1 / 4)) :=
          funext hsfinal
        rw [hsma, hsfa]


/-- Recover the fixed payload from a reconstructed executable datum. -/
theorem alignedPayload_of_reconstruct (s : Shape) (v : Payload s)
    (E : ExecutableData) (he : reconstruct s v = E) :
    alignedPayload E s (congrArg shape he.symm) = v := by
  cases he
  rfl

variable {X : Type*} [MeasurableSpace X]
/-- A measurable family of payloads remains measurable when aligned to any
equal fixed syntax shape. -/
theorem measurable_alignedPayload_of_reconstruct
    (s t : Shape) (f : X → Payload s) (E : X → ExecutableData)
    (hs : s = t) (he : ∀ x, reconstruct s (f x) = E x)
    (hshape : ∀ x, shape (E x) = t)
    (hf : Measurable f) :
    Measurable (fun x => alignedPayload (E x) t (hshape x)) := by
  cases hs
  have hval (x : X) : alignedPayload (E x) s (hshape x) = f x := by
    have h0 := alignedPayload_of_reconstruct s (f x) (E x) (he x)
    exact h0
  simpa only [hval] using hf

/-- Measurability of the actual recursive program payload when its three
physical parameters vary measurably, aligned to an arbitrary anchor. -/
theorem meanCore_alignedPayload_measurable (q scale₀ r₀ σ₀ : ℝ)
    (scale r σ : X → ℝ)
    (hscale : Measurable scale) (hr : Measurable r) (hσ : Measurable σ) :
    Measurable (fun x =>
      alignedPayload
        (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
          (scale x) (r x) (σ x) q)
        (shape (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
          scale₀ r₀ σ₀ q))
        (meanCore_shape M nodes anchors seeds S snodes Ds δ t w layers ht htq
          q (scale x) (r x) (σ x) scale₀ r₀ σ₀)) := by
  obtain ⟨s, f, hf, hrec⟩ :=
    meanCore_measurable_payload_exists M nodes anchors seeds S snodes
      Ds δ t w layers ht htq q
  let triple : X → ℝ × ℝ × ℝ := fun x => (scale x, r x, σ x)
  have htriple : Measurable triple := hscale.prodMk (hr.prodMk hσ)
  have hs : s = shape (meanCore M nodes anchors seeds S snodes
      Ds δ t w layers ht htq scale₀ r₀ σ₀ q) := by
    have hh := congrArg shape (hrec (scale₀, r₀, σ₀))
    exact hh
  exact measurable_alignedPayload_of_reconstruct s _
    (fun x => f (triple x))
    (fun x => meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
      (scale x) (r x) (σ x) q)
    hs (fun x => hrec (triple x))
    (fun x => meanCore_shape M nodes anchors seeds S snodes
      Ds δ t w layers ht htq q (scale x) (r x) (σ x) scale₀ r₀ σ₀)
    (hf.comp htriple)
end AcceleratedLogConcave.Oracle.RecursiveExecutableParameterMeasurability
