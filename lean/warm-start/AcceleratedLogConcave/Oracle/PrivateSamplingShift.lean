import AcceleratedLogConcave.Oracle.PrivateSamplingValue
import AcceleratedLogConcave.Oracle.SourceExecutableShift
import AcceleratedLogConcave.Oracle.ExecutableShiftTape
import AcceleratedLogConcave.Oracle.ExecutableInputFree
import AcceleratedLogConcave.Oracle.ExecutableLayerTranslation

noncomputable section
namespace AcceleratedLogConcave.Oracle.PrivateSamplingProgram
open AffineLowering TapeLowering NoisyLayer RecursiveMeanProgram RecursiveMeanContinuation
open ChildAbsorption CovarianceSetup LayerShift ExecutableShiftWeights SourceExecutableShift
open scoped BigOperators

/-- Translation retains the full event transcript, including gradient arguments. -/
def displaced (result : Result d .point) (a : ℝ) (Δ : Point d) : Result d .point :=
  ⟨PrivateSamplingFinal.pointValue result + a • Δ, result.trace⟩

set_option backward.isDefEq.respectTransparency false in
theorem final_translation {c cf : Fin n → ℕ} {p : ∀ i, Program (c i) .point}
    {pf : ∀ i, Program (cf i) .point} (cfg : Config n C c cf p pf)
    (old : Fin n → Ref Γ .point) (outputDirect : Ref Γ .point)
    (rho r : ℝ) (radius Ds k : Fin n → ℝ)
    (v : ∀ i, Fin (tapeShape (pf i)).gaussianBlocks → ℝ)
    (coeff : ∀ i, Fin (cf i) → ℝ)
    (h : ∀ i, Admissible rho (radius i) (Ds i) (v i)) (hr : 0 < r)
    (hshift : ∀ i, QueryShift (pf i) (cfg.finalEquiv i) (coeff i) (radius i) (v i))
    (G : Point d → Point d) (input input' : Inputs d C) (env env' : Env d Γ)
    (hcoeff : input'.coefficient = input.coefficient)
    (Δ : Point d) (a reserveShift : ℝ)
    (htable : ∀ i, input.coefficient ∘ cfg.finalSlots i =
      matrixTable (childRoot rho (radius i) (v i)) (coeff i))
    (hold : ∀ i, storedPoint env' (old i) = storedPoint env (old i) + k i • Δ)
    (hdir : storedPoint env' outputDirect = storedPoint env outputDirect + a • Δ)
    (tape : Tape d (finish cfg old outputDirect)) :
    run (finish cfg old outputDirect) G input' env'
      (translate (finish cfg old outputDirect)
        (samplingFinal cfg old outputDirect
          (fun i => rawShift rho (radius i) r (k i) (v i)) reserveShift) r Δ tape) =
    displaced (run (finish cfg old outputDirect) G input env tape)
      (a + input.coefficient cfg.reserve * (reserveShift/r)) Δ := by
  let shifted := translate (finish cfg old outputDirect)
    (samplingFinal cfg old outputDirect
      (fun i => rawShift rho (radius i) r (k i) (v i)) reserveShift) r Δ tape
  have hc (i : Fin n) :
      run (freshChild (pf i) (cfg.finalEquiv i) (cfg.finalSlots i) (old i)
        (cfg.finalDesignated i) (cfg.finalAuxiliary i)) G input' env' (shifted.1 i) =
      run (freshChild (pf i) (cfg.finalEquiv i) (cfg.finalSlots i) (old i)
        (cfg.finalDesignated i) (cfg.finalAuxiliary i)) G input env (tape.1 i) := by
    change run _ G input' env'
      (translate (freshChild (pf i) (cfg.finalEquiv i) (cfg.finalSlots i) (old i)
        (cfg.finalDesignated i) (cfg.finalAuxiliary i))
        (freshWeights (pf i) (cfg.finalEquiv i) (cfg.finalSlots i) (old i)
          (cfg.finalDesignated i) (cfg.finalAuxiliary i)
          (rawShift rho (radius i) r (k i) (v i))) r Δ (tape.1 i)) = _
    rw [translate_freshWeights]
    have table' : input'.coefficient ∘ cfg.finalSlots i =
        matrixTable (childRoot rho (radius i) (v i)) (coeff i) := by rw [hcoeff,htable i]
    exact (childExecutionTranslation (pf i) (cfg.finalEquiv i) (cfg.finalSlots i) (old i)
      (cfg.finalDesignated i) (cfg.finalAuxiliary i) rho (radius i) (Ds i) r (k i)
      (v i) (coeff i) (h i) hr (hshift i) G input' env env' Δ table' (hold i) _).trans
      (freshChild_same_coefficients (pf i) (cfg.finalEquiv i) (cfg.finalSlots i) (old i)
        (cfg.finalDesignated i) (cfg.finalAuxiliary i) (childRoot rho (radius i) (v i))
        (coeff i) G input input' env hcoeff (htable i) _)
  have hz : PrivateSamplingFinal.gaussianValue shifted.2.1 =
      PrivateSamplingFinal.gaussianValue tape.2.1 := by
    change (show Point d from tape.2.1) + (0/r) • Δ = _
    simp only [zero_div,zero_smul,add_zero,PrivateSamplingFinal.gaussianValue]
  have hw : PrivateSamplingFinal.gaussianValue shifted.2.2.1 =
      PrivateSamplingFinal.gaussianValue tape.2.2.1 + (reserveShift/r) • Δ := rfl
  have ht := PrivateSamplingFinal.run_code cf pf cfg.finalEquiv cfg.finalSlots
    cfg.rowWeight cfg.beta cfg.reserve old outputDirect cfg.finalOrigin cfg.finalDesignated
    cfg.finalAuxiliary cfg.finalResidual cfg.finalReserve G input' env' shifted
  have hb := PrivateSamplingFinal.run_code cf pf cfg.finalEquiv cfg.finalSlots
    cfg.rowWeight cfg.beta cfg.reserve old outputDirect cfg.finalOrigin cfg.finalDesignated
    cfg.finalAuxiliary cfg.finalResidual cfg.finalReserve G input env tape
  dsimp only at ht hb
  simp only [hc,hz,hw,hdir,hcoeff] at ht
  change run (finish cfg old outputDirect) G input' env' shifted = _ at ht
  change run (finish cfg old outputDirect) G input env tape = _ at hb
  change run (finish cfg old outputDirect) G input' env' shifted = _
  rw [ht,hb]
  unfold displaced PrivateSamplingFinal.pointValue
  congr 1
  simp only [smul_add,smul_smul,add_smul]
  abel

set_option backward.isDefEq.respectTransparency false in
/-- Translation through every actually executed synchronous layer, with the
actual fresh final children. The induction preserves full Results. -/
theorem loop_translation {c cf : Fin n → ℕ} {p : ∀ i, Program (c i) .point}
    {pf : ∀ i, Program (cf i) .point} (cfg : Config n C c cf p pf)
    (outputDirect : Ref Ξ .point) (rho r Ds : ℝ) (radius k : Fin n → ℝ)
    (vm : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (vf : ∀ i, Fin (tapeShape (pf i)).gaussianBlocks → ℝ)
    (cm : ∀ i, Fin (c i) → ℝ) (cfinal : ∀ i, Fin (cf i) → ℝ)
    (hm : ∀ i, Admissible rho (radius i) Ds (vm i))
    (hf : ∀ i, Admissible rho (radius i) Ds (vf i)) (hr : 0 < r)
    (hsm : ∀ i, QueryShift (p i) (cfg.mainEquiv i) (cm i) (radius i) (vm i))
    (hsf : ∀ i, QueryShift (pf i) (cfg.finalEquiv i) (cfinal i) (radius i) (vf i))
    (G : Point d → Point d) (input input' : Inputs d C)
    (hcoeff : input'.coefficient = input.coefficient) (Δ : Point d) (a reserveShift : ℝ)
    (htm : ∀ i, input.coefficient ∘ (cfg.mainSlots ∘ childSlot c p i) =
      matrixTable (childRoot rho (radius i) (vm i)) (cm i))
    (htf : ∀ i, input.coefficient ∘ cfg.finalSlots i =
      matrixTable (childRoot rho (radius i) (vf i)) (cfinal i))
    (N : ℕ) {Γ : Ctx} (old direct : Fin n → Ref Γ .point) (saved : RefMap Ξ Γ)
    (env env' : Env d Γ)
    (hold : ∀ i, storedPoint env' (old i) = storedPoint env (old i) + k i • Δ)
    (hdir : ∀ i, storedPoint env' (direct i) = storedPoint env (direct i) + k i • Δ)
    (hout : storedPoint env' (saved outputDirect) =
      storedPoint env (saved outputDirect) + a • Δ)
    (tape : Tape d (iterateThen c p cfg.mainSlots cfg.mainEquiv cfg.layerOrigin
      cfg.mainDesignated cfg.mainResidual cfg.mainAuxiliary
      (fun old _ saved => finish cfg old (saved outputDirect)) N old direct saved)) :
    let finisher := fun {Λ : Ctx} (old _ : Fin n → Ref Λ .point) (saved : RefMap Ξ Λ) =>
      finish cfg old (saved outputDirect)
    let program := iterateThen c p cfg.mainSlots cfg.mainEquiv cfg.layerOrigin
      cfg.mainDesignated cfg.mainResidual cfg.mainAuxiliary finisher N old direct saved
    let weights := iterateWeights c p cfg.mainSlots cfg.mainEquiv cfg.layerOrigin
      cfg.mainDesignated cfg.mainResidual cfg.mainAuxiliary finisher
      (fun i => rawShift rho (radius i) r (k i) (vm i))
      (fun old _ saved => samplingFinal cfg old (saved outputDirect)
        (fun i => rawShift rho (radius i) r (k i) (vf i)) reserveShift) N old direct saved
    run program G input' env' (translate program weights r Δ tape) =
      displaced (run program G input env tape)
        (a + input.coefficient cfg.reserve * (reserveShift/r)) Δ := by
  dsimp only
  induction N generalizing Γ with
  | zero =>
      exact final_translation cfg old (saved outputDirect) rho r radius (fun _ => Ds) k
        vf cfinal hf hr hsf G input input' env env' hcoeff Δ a reserveShift htf hold hout tape
  | succ N ih =>
      let finisher := fun {Λ : Ctx} (old _ : Fin n → Ref Λ .point) (saved : RefMap Ξ Λ) =>
        finish cfg old (saved outputDirect)
      let next := iterateThen c p cfg.mainSlots cfg.mainEquiv cfg.layerOrigin
        cfg.mainDesignated cfg.mainResidual cfg.mainAuxiliary finisher N batchRef
        (fun j => preserveDirect (direct j)) (fun r => preserveDirect (saved r))
      let shifted := translate
        (iterateThen c p cfg.mainSlots cfg.mainEquiv cfg.layerOrigin cfg.mainDesignated
          cfg.mainResidual cfg.mainAuxiliary finisher (N+1) old direct saved)
        (iterateWeights c p cfg.mainSlots cfg.mainEquiv cfg.layerOrigin cfg.mainDesignated
          cfg.mainResidual cfg.mainAuxiliary finisher
          (fun i => rawShift rho (radius i) r (k i) (vm i))
          (fun old _ saved => samplingFinal cfg old (saved outputDirect)
            (fun i => rawShift rho (radius i) r (k i) (vf i)) reserveShift)
          (N+1) old direct saved) r Δ tape
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
      change run (SourceMeanLayer.layerAt c p cfg.mainSlots cfg.mainEquiv old direct
        (cfg.layerOrigin N) (cfg.mainDesignated N) (cfg.mainResidual N)
        (cfg.mainAuxiliary N) next) G input' env' shifted = _
      apply SourceMeanLayer.run_layerAt_translation c p cfg.mainSlots cfg.mainEquiv old direct
        (cfg.layerOrigin N) (cfg.mainDesignated N) (cfg.mainResidual N)
        (cfg.mainAuxiliary N) next G input input' env env' tape shifted
        ((a + input.coefficient cfg.reserve * (reserveShift/r)) • Δ) hc
      dsimp only
      let Q : Fin n → Point d := fun i => (run
        (freshChild (p i) (cfg.mainEquiv i) (cfg.mainSlots ∘ childSlot c p i) (old i)
          (cfg.mainDesignated N i) (cfg.mainAuxiliary N i)) G input env (tape.1 i)).value
      let Z : Fin n → Point d := fun i => (tape.2.1 i).1
      have hz : (fun i : Fin n => (shifted.2.1 i).1) = Z := by
        funext i
        change (show Point d from (tape.2.1 i).1) + (0/r) • Δ = _
        simp only [zero_div,zero_smul,add_zero]
        rfl
      simp only [hz]
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
        exact hout

end AcceleratedLogConcave.Oracle.PrivateSamplingProgram
