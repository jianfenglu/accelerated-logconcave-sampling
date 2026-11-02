import AcceleratedLogConcave.Oracle.NonterminalMeanBlock
import AcceleratedLogConcave.Oracle.RetainedMeanFinalValue
import AcceleratedLogConcave.Oracle.SourceExecutableShift
import AcceleratedLogConcave.Oracle.ExecutableShiftTape
import AcceleratedLogConcave.Oracle.ExecutableInputFree
import AcceleratedLogConcave.Oracle.ExecutableLayerTranslation

noncomputable section
namespace AcceleratedLogConcave.Oracle.MeanBlockShift
open AffineLowering TapeLowering NoisyLayer RecursiveMeanProgram RecursiveMeanContinuation
open ChildAbsorption CovarianceSetup LayerShift ExecutableShiftWeights SourceExecutableShift
open RetainedMeanFinalBatch
open scoped BigOperators

structure Config (n m C : ℕ) (c : Fin n → ℕ) (cf : Fin m → ℕ)
    (p : ∀ i, Program (c i) .point) (pf : ∀ i, Program (cf i) .point) where
  mainSlots : Fin (publicSize c p) → Fin C
  mainEquiv : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks
  finalSlots : ∀ i, Fin (childSize (pf i)) → Fin C
  finalEquiv : ∀ i, GaussianSlot (pf i) ≃ Fin (tapeShape (pf i)).gaussianBlocks
  correctionSlots : Fin (1+(m+m)) → Fin C
  noise : Fin C
  active : Fin m → Fin n
  initialOrigin : Fin n → Origin
  layerOrigin : ℕ → Origin
  mainDesignated : ℕ → Fin n → Origin
  mainResidual : ℕ → Fin n → Origin
  mainAuxiliary : ℕ → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin
  finalOrigin : Origin
  finalAuxiliary : ∀ i, Fin (tapeShape (pf i)).gaussianBlocks → Origin
  layers : ℕ

variable {c : Fin n → ℕ} {cf : Fin m → ℕ} {p : ∀ i, Program (c i) .point}
  {pf : ∀ i, Program (cf i) .point}

def finish (cfg : Config n m C c cf p pf) (P : Ref Γ .point)
    (designated : Fin m → Ref Γ .point) (old : Fin n → Ref Γ .point) : Prog C Γ .point :=
  paidCorrection cf pf cfg.finalEquiv cfg.finalSlots cfg.correctionSlots P
    (fun i => old (cfg.active i)) designated cfg.finalOrigin cfg.finalAuxiliary

def code (cfg : Config n m C c cf p pf) (P : Ref Γ .point)
    (designated : Fin m → Ref Γ .point) (direct : Fin n → Ref Γ .point) : Prog C Γ .point :=
  NonterminalMeanBlock.code c p cfg.mainSlots cfg.mainEquiv cf pf cfg.finalEquiv
    cfg.finalSlots cfg.correctionSlots cfg.noise P designated direct cfg.active
    cfg.initialOrigin cfg.layerOrigin cfg.mainDesignated cfg.mainResidual
    cfg.mainAuxiliary cfg.finalOrigin cfg.finalAuxiliary cfg.layers

def weights (cfg : Config n m C c cf p pf) (P : Ref Γ .point)
    (designated : Fin m → Ref Γ .point) (direct : Fin n → Ref Γ .point)
    (raw : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → ℝ) : GaussianSlot (code cfg P designated direct) → ℝ :=
  meanBlock c p cfg.mainSlots cfg.mainEquiv cf pf cfg.finalEquiv cfg.finalSlots
    cfg.correctionSlots cfg.noise P designated direct cfg.active cfg.initialOrigin cfg.layerOrigin
    cfg.mainDesignated cfg.mainResidual cfg.mainAuxiliary cfg.finalOrigin cfg.finalAuxiliary cfg.layers raw

set_option backward.isDefEq.respectTransparency false in
/-- Final mean calls need no child shift theorem when their stored centers,
designated inputs, and the retained parent are unchanged. -/
theorem paidCorrection_same (cfg : Config n m C c cf p pf)
    (P : Ref Γ .point) (designated : Fin m → Ref Γ .point) (old : Fin n → Ref Γ .point)
    (sigma : ℝ) (omega width : Fin m → ℝ)
    (G : Point d → Point d) (input input' : Inputs d C) (env env' : Env d Γ)
    (hcoeff : input'.coefficient = input.coefficient)
    (htable : input.coefficient ∘ cfg.correctionSlots = RetainedMeanCorrection.table sigma omega width)
    (hP : storedPoint env' P = storedPoint env P)
    (hdes : ∀ i, storedPoint env' (designated i) = storedPoint env (designated i))
    (hold : ∀ i, storedPoint env' (old (cfg.active i)) = storedPoint env (old (cfg.active i)))
    (tape : Tape d (finish cfg P designated old)) :
    run (finish cfg P designated old) G input' env' tape =
      run (finish cfg P designated old) G input env tape := by
  have hc (i : Fin m) : run (designatedChild (pf i) (cfg.finalEquiv i)
      (cfg.finalSlots i) (old (cfg.active i)) (designated i) (cfg.finalAuxiliary i))
      G input' env' (tape.1 i) =
      run (designatedChild (pf i) (cfg.finalEquiv i) (cfg.finalSlots i)
        (old (cfg.active i)) (designated i) (cfg.finalAuxiliary i))
        G input env (tape.1 i) := by
    unfold designatedChild
    rw [run_embed_every_tape,run_embed_every_tape]
    change run _ G ⟨input'.coefficient ∘ cfg.finalSlots i,
      storedPoint env' (old (cfg.active i)),storedPoint env' (designated i)⟩ Env.empty _ = _
    rw [hcoeff,hold i,hdes i]
    rfl
  have ht := run_paidCorrection cf pf cfg.finalEquiv cfg.finalSlots cfg.correctionSlots
    P (fun i => old (cfg.active i)) designated cfg.finalOrigin cfg.finalAuxiliary
    sigma omega width G input' env' (by rw [hcoeff,htable]) tape
  have hb := run_paidCorrection cf pf cfg.finalEquiv cfg.finalSlots cfg.correctionSlots
    P (fun i => old (cfg.active i)) designated cfg.finalOrigin cfg.finalAuxiliary
    sigma omega width G input env htable tape
  dsimp only at ht hb
  simp only [hc,hP,hdes] at ht
  exact ht.trans hb.symm

set_option backward.isDefEq.respectTransparency false in
theorem loop_translation (cfg : Config n m C c cf p pf)
    (P : Ref Ξ .point) (designated : Fin m → Ref Ξ .point)
    (rho r Ds : ℝ) (radius k : Fin n → ℝ)
    (vm : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (cm : ∀ i, Fin (c i) → ℝ)
    (hm : ∀ i, Admissible rho (radius i) Ds (vm i)) (hr : 0 < r)
    (hsm : ∀ i, QueryShift (p i) (cfg.mainEquiv i) (cm i) (radius i) (vm i))
    (sigma : ℝ) (omega width : Fin m → ℝ)
    (G : Point d → Point d) (input input' : Inputs d C)
    (hcoeff : input'.coefficient = input.coefficient) (Δ : Point d)
    (htm : ∀ i, input.coefficient ∘ (cfg.mainSlots ∘ childSlot c p i) =
      matrixTable (childRoot rho (radius i) (vm i)) (cm i))
    (htcorr : input.coefficient ∘ cfg.correctionSlots =
      RetainedMeanCorrection.table sigma omega width)
    (hactive : ∀ i, k (cfg.active i) = 0)
    (N : ℕ) {Γ : Ctx} (old direct : Fin n → Ref Γ .point) (saved : RefMap Ξ Γ)
    (env env' : Env d Γ)
    (hold : ∀ i, storedPoint env' (old i) = storedPoint env (old i) + k i • Δ)
    (hdir : ∀ i, storedPoint env' (direct i) = storedPoint env (direct i) + k i • Δ)
    (hP : storedPoint env' (saved P) = storedPoint env (saved P))
    (hdes : ∀ i, storedPoint env' (saved (designated i)) = storedPoint env (saved (designated i)))
    (tape : Tape d (iterateThen c p cfg.mainSlots cfg.mainEquiv cfg.layerOrigin
      cfg.mainDesignated cfg.mainResidual cfg.mainAuxiliary
      (fun old _ saved => finish cfg (saved P) (fun i => saved (designated i)) old)
      N old direct saved)) :
    let finisher := fun {Λ : Ctx} (old _ : Fin n → Ref Λ .point) (saved : RefMap Ξ Λ) =>
      finish cfg (saved P) (fun i => saved (designated i)) old
    let program := iterateThen c p cfg.mainSlots cfg.mainEquiv cfg.layerOrigin
      cfg.mainDesignated cfg.mainResidual cfg.mainAuxiliary finisher N old direct saved
    let weights := iterateWeights c p cfg.mainSlots cfg.mainEquiv cfg.layerOrigin
      cfg.mainDesignated cfg.mainResidual cfg.mainAuxiliary finisher
      (fun i => rawShift rho (radius i) r (k i) (vm i))
      (fun _ _ _ _ => 0) N old direct saved
    run program G input' env' (translate program weights r Δ tape) =
      run program G input env tape := by
  dsimp only
  induction N generalizing Γ with
  | zero =>
      change run (finish cfg (saved P) (fun i => saved (designated i)) old) G input' env'
        (translate _ (fun _ => 0) r Δ tape) = _
      rw [translate_zero]
      exact paidCorrection_same cfg (saved P) (fun i => saved (designated i)) old
        sigma omega width G input input' env env' hcoeff htcorr hP hdes
        (fun i => by simpa only [hactive,zero_smul,add_zero] using hold (cfg.active i)) tape
  | succ N ih =>
      let finisher := fun {Λ : Ctx} (old _ : Fin n → Ref Λ .point) (saved : RefMap Ξ Λ) =>
        finish cfg (saved P) (fun i => saved (designated i)) old
      let next := iterateThen c p cfg.mainSlots cfg.mainEquiv cfg.layerOrigin
        cfg.mainDesignated cfg.mainResidual cfg.mainAuxiliary finisher N batchRef
        (fun j => preserveDirect (direct j)) (fun r => preserveDirect (saved r))
      let shifted := translate
        (iterateThen c p cfg.mainSlots cfg.mainEquiv cfg.layerOrigin cfg.mainDesignated
          cfg.mainResidual cfg.mainAuxiliary finisher (N+1) old direct saved)
        (iterateWeights c p cfg.mainSlots cfg.mainEquiv cfg.layerOrigin cfg.mainDesignated
          cfg.mainResidual cfg.mainAuxiliary finisher
          (fun i => rawShift rho (radius i) r (k i) (vm i))
          (fun _ _ _ _ => 0) (N+1) old direct saved) r Δ tape
      have hc (i : Fin n) :
          run (freshChild (p i) (cfg.mainEquiv i) (cfg.mainSlots ∘ childSlot c p i) (old i)
            (cfg.mainDesignated N i) (cfg.mainAuxiliary N i)) G input' env' (shifted.1 i) =
          run (freshChild (p i) (cfg.mainEquiv i) (cfg.mainSlots ∘ childSlot c p i) (old i)
            (cfg.mainDesignated N i) (cfg.mainAuxiliary N i)) G input env (tape.1 i) := by
        change run _ G input' env'
          (translate _ (freshWeights (p i) (cfg.mainEquiv i)
            (cfg.mainSlots ∘ childSlot c p i) (old i) (cfg.mainDesignated N i)
            (cfg.mainAuxiliary N i) (rawShift rho (radius i) r (k i) (vm i))) r Δ (tape.1 i)) = _
        rw [translate_freshWeights]
        have table' : input'.coefficient ∘ (cfg.mainSlots ∘ childSlot c p i) =
            matrixTable (childRoot rho (radius i) (vm i)) (cm i) := by rw [hcoeff,htm i]
        exact (childExecutionTranslation (p i) (cfg.mainEquiv i)
          (cfg.mainSlots ∘ childSlot c p i) (old i) (cfg.mainDesignated N i)
          (cfg.mainAuxiliary N i) rho (radius i) Ds r (k i) (vm i) (cm i)
          (hm i) hr (hsm i) G input' env env' Δ table' (hold i) _).trans
          (freshChild_same_coefficients (p i) (cfg.mainEquiv i)
            (cfg.mainSlots ∘ childSlot c p i) (old i) (cfg.mainDesignated N i)
            (cfg.mainAuxiliary N i) _ (cm i) G input input' env hcoeff (htm i) _)
      have hl := SourceMeanLayer.run_layerAt_translation c p cfg.mainSlots cfg.mainEquiv old direct
        (cfg.layerOrigin N) (cfg.mainDesignated N) (cfg.mainResidual N)
        (cfg.mainAuxiliary N) next G input input' env env' tape shifted (0 : Point d) hc
      have ht : run next G input'
          (Env.prepend (noisyValues (fun j k => cfg.mainSlots (aSlot c p j k))
            (fun j k => cfg.mainSlots (residualSlot c p j k)) direct input' env'
            (fun i => (run (freshChild (p i) (cfg.mainEquiv i)
              (cfg.mainSlots ∘ childSlot c p i) (old i) (cfg.mainDesignated N i)
              (cfg.mainAuxiliary N i)) G input env (tape.1 i)).value)
            (fun i => (shifted.2.1 i).1))
            (Env.prepend (fun i => (shifted.2.1 i).1)
              (Env.prepend (fun i => (run (freshChild (p i) (cfg.mainEquiv i)
                (cfg.mainSlots ∘ childSlot c p i) (old i) (cfg.mainDesignated N i)
                (cfg.mainAuxiliary N i)) G input env (tape.1 i)).value) env'))) shifted.2.2.2 =
          run next G input
          (Env.prepend (noisyValues (fun j k => cfg.mainSlots (aSlot c p j k))
            (fun j k => cfg.mainSlots (residualSlot c p j k)) direct input env
            (fun i => (run (freshChild (p i) (cfg.mainEquiv i)
              (cfg.mainSlots ∘ childSlot c p i) (old i) (cfg.mainDesignated N i)
              (cfg.mainAuxiliary N i)) G input env (tape.1 i)).value)
            (fun i => (tape.2.1 i).1))
            (Env.prepend (fun i => (tape.2.1 i).1)
              (Env.prepend (fun i => (run (freshChild (p i) (cfg.mainEquiv i)
                (cfg.mainSlots ∘ childSlot c p i) (old i) (cfg.mainDesignated N i)
                (cfg.mainAuxiliary N i)) G input env (tape.1 i)).value) env))) tape.2.2.2 := by
        let Q : Fin n → Point d := fun i => (run
          (freshChild (p i) (cfg.mainEquiv i) (cfg.mainSlots ∘ childSlot c p i) (old i)
            (cfg.mainDesignated N i) (cfg.mainAuxiliary N i)) G input env (tape.1 i)).value
        let Z : Fin n → Point d := fun i => (tape.2.1 i).1
        have hz : (fun i : Fin n => (shifted.2.1 i).1) = Z := by
          funext i
          change (show Point d from (tape.2.1 i).1) + (0/r) • Δ = _
          simp only [zero_div,zero_smul,add_zero]
          rfl
        rw [hz]
        let X := noisyValues (fun j k => cfg.mainSlots (aSlot c p j k))
          (fun j k => cfg.mainSlots (residualSlot c p j k)) direct input env Q Z
        let X' := noisyValues (fun j k => cfg.mainSlots (aSlot c p j k))
          (fun j k => cfg.mainSlots (residualSlot c p j k)) direct input' env' Q Z
        have hx (i : Fin n) : X' i = X i + k i • Δ := by
          simp only [X',X,noisyValues,hcoeff,hdir]
          abel
        apply ih batchRef (fun j => preserveDirect (direct j))
          (fun r => preserveDirect (saved r))
          (Env.prepend X (Env.prepend Z (Env.prepend Q env)))
          (Env.prepend X' (Env.prepend Z (Env.prepend Q env')))
        · intro i
          exact (prepend_batchRef X' _ i).trans
            ((hx i).trans (congrArg (fun z => z + k i • Δ) (prepend_batchRef X _ i).symm))
        · intro i
          rw [stored_preserveDirect,stored_preserveDirect]
          exact hdir i
        · rw [stored_preserveDirect,stored_preserveDirect]
          exact hP
        · intro i
          rw [stored_preserveDirect,stored_preserveDirect]
          exact hdes i
      have hh := hl (by dsimp only; rw [ht]; simp only [add_zero])
      change run (SourceMeanLayer.layerAt c p cfg.mainSlots cfg.mainEquiv old direct
        (cfg.layerOrigin N) (cfg.mainDesignated N) (cfg.mainResidual N)
        (cfg.mainAuxiliary N) next) G input' env' shifted =
        run (SourceMeanLayer.layerAt c p cfg.mainSlots cfg.mainEquiv old direct
          (cfg.layerOrigin N) (cfg.mainDesignated N) (cfg.mainResidual N)
          (cfg.mainAuxiliary N) next) G input env tape
      simpa only [add_zero] using hh

set_option backward.isDefEq.respectTransparency false in
/-- Actual nonterminal mean block translation, including initialization, every
main layer, the paid active-final calls and the retained original-P correction. -/
theorem translation (cfg : Config n m C c cf p pf)
    (P : Ref Γ .point) (designated : Fin m → Ref Γ .point)
    (direct : Fin n → Ref Γ .point)
    (rho r Ds : ℝ) (radius k : Fin n → ℝ)
    (vm : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (cm : ∀ i, Fin (c i) → ℝ)
    (hm : ∀ i, Admissible rho (radius i) Ds (vm i)) (hr : 0 < r)
    (hsm : ∀ i, QueryShift (p i) (cfg.mainEquiv i) (cm i) (radius i) (vm i))
    (sigma : ℝ) (omega width : Fin m → ℝ)
    (G : Point d → Point d) (input input' : Inputs d C)
    (hcoeff : input'.coefficient = input.coefficient) (Δ : Point d)
    (htm : ∀ i, input.coefficient ∘ (cfg.mainSlots ∘ childSlot c p i) =
      matrixTable (childRoot rho (radius i) (vm i)) (cm i))
    (htcorr : input.coefficient ∘ cfg.correctionSlots =
      RetainedMeanCorrection.table sigma omega width)
    (hactive : ∀ i, k (cfg.active i) = 0)
    (env env' : Env d Γ)
    (hdir : ∀ i, storedPoint env' (direct i) = storedPoint env (direct i) + k i • Δ)
    (hP : storedPoint env' P = storedPoint env P)
    (hdes : ∀ i, storedPoint env' (designated i) = storedPoint env (designated i))
    (tape : Tape d (code cfg P designated direct)) :
    run (code cfg P designated direct) G input' env'
      (translate (code cfg P designated direct)
        (weights cfg P designated direct (fun i => rawShift rho (radius i) r (k i) (vm i)))
        r Δ tape) = run (code cfg P designated direct) G input env tape := by
  let shifted := translate (code cfg P designated direct)
    (weights cfg P designated direct (fun i => rawShift rho (radius i) r (k i) (vm i))) r Δ tape
  let Z : Fin n → Point d := fun i => (tape.1 i).1
  have hz : (fun i : Fin n => (shifted.1 i).1) = Z := by
    funext i
    change (show Point d from (tape.1 i).1) + (0/r) • Δ = _
    simp only [zero_div,zero_smul,add_zero]
    rfl
  let X : Fin n → Point d := fun i =>
    storedPoint env (direct i) + input.coefficient cfg.noise • Z i
  let X' : Fin n → Point d := fun i =>
    storedPoint env' (direct i) + input'.coefficient cfg.noise • Z i
  have hx (i : Fin n) : X' i = X i + k i • Δ := by
    simp only [X',X,hcoeff,hdir]
    abel
  have hs (v : Ref Γ .point) :
      Env.prepend X' (Env.prepend Z env') (RefMap.shiftMany n (RefMap.shiftMany n v)) = env' v :=
    (prepend_shiftMany X' _ _).trans (prepend_shiftMany Z _ _)
  have hb (v : Ref Γ .point) :
      Env.prepend X (Env.prepend Z env) (RefMap.shiftMany n (RefMap.shiftMany n v)) = env v :=
    (prepend_shiftMany X _ _).trans (prepend_shiftMany Z _ _)
  have hl := loop_translation cfg P designated rho r Ds radius k vm cm hm hr hsm
    sigma omega width G input input' hcoeff Δ htm htcorr hactive cfg.layers
    batchRef (fun i => RefMap.shiftMany n (RefMap.shiftMany n (direct i)))
    (fun r => RefMap.shiftMany n (RefMap.shiftMany n r))
    (Env.prepend X (Env.prepend Z env)) (Env.prepend X' (Env.prepend Z env'))
    (fun i => (prepend_batchRef X' _ i).trans
      ((hx i).trans (congrArg (fun z => z + k i • Δ) (prepend_batchRef X _ i).symm)))
    (fun i => (hs (direct i)).trans
      ((hdir i).trans (congrArg (fun z => z + k i • Δ) (hb (direct i)).symm)))
    ((hs P).trans (hP.trans (hb P).symm))
    (fun i => (hs (designated i)).trans ((hdes i).trans (hb (designated i)).symm)) tape.2.2
  let next := iterateThen c p cfg.mainSlots cfg.mainEquiv cfg.layerOrigin
    cfg.mainDesignated cfg.mainResidual cfg.mainAuxiliary
    (fun old _ saved => finish cfg (saved P) (fun i => saved (designated i)) old)
    cfg.layers batchRef (fun i => RefMap.shiftMany n (RefMap.shiftMany n (direct i)))
    (fun r => RefMap.shiftMany n (RefMap.shiftMany n r))
  have ht := run_initialize cfg.noise direct [] cfg.initialOrigin next G input' env' shifted
  have hu := run_initialize cfg.noise direct [] cfg.initialOrigin next G input env tape
  dsimp only at ht hu hl
  simp only [prefix_nil] at ht hu
  have hrow : (fun j => storedPoint env' (direct j) + input'.coefficient cfg.noise •
      (show Point d from (shifted.1 j).1)) = X' :=
    funext (fun j => congrArg (fun z => storedPoint env' (direct j) +
      input'.coefficient cfg.noise • z) (congrFun hz j))
  erw [hrow,hz] at ht
  change run (code cfg P designated direct) G input' env' shifted = _
  change run (code cfg P designated direct) G input' env' shifted = _ at ht
  change run (code cfg P designated direct) G input env tape = _ at hu
  rw [ht,hu]
  erw [hl]


end AcceleratedLogConcave.Oracle.MeanBlockShift
