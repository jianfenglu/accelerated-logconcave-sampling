import AcceleratedLogConcave.Oracle.SamplingExecutableStability

/-! Zero-layer sampling retains arbitrary main carriers but pays only final IHs.
The actual setup and final readout use the same complete raw tape. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Oracle.FixedTapeSampling
open TapeLowering AffineLowering NoisyLayer RecursiveMeanProgram RecursiveMeanContinuation
open PrivateSamplingProgram FixedTapeStability RetainedMeanFinalBatch SourceExecutableTables
open Numerics.AffineGraph
open scoped BigOperators
variable {d n m C : ℕ}

theorem body_zero_sub_le {c cf : Fin n → ℕ} {p : ∀ i, Program (c i) .point}
    {pf : ∀ i, Program (cf i) .point} (cfg : Config n C c cf p pf)
    (Tf : ∀ i, Fin (tapeShape (pf i)).gaussianBlocks → Fin (tapeShape (pf i)).gaussianBlocks → ℝ)
    (coeffF : ∀ i, Fin (cf i) → ℝ) (G : Point d → Point d) (input : Inputs d C)
    (κ W : ℝ) (hκ : 0 ≤ κ)
    (htableF : ∀ i, input.coefficient ∘ cfg.finalSlots i = matrixTable (Tf i) (coeffF i))
    (hchildF : ∀ i, ChildStable (pf i) (coeffF i) G κ)
    (hweight : ∑ i, |input.coefficient (cfg.rowWeight i)| ≤ W)
    {Γ : Ctx} (direct : Fin n → Ref Γ .point)
    (outputDirect : Ref Γ .point) (env env' : Env d Γ) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ i, ‖storedPoint env (direct i)-storedPoint env' (direct i)‖ ≤ B)
    (hout : storedPoint env outputDirect = storedPoint env' outputDirect)
    (tape : Tape d (body {cfg with layers := 0} direct outputDirect)) :
    ‖childPoint (run (body {cfg with layers := 0} direct outputDirect) G input env tape) -
      childPoint (run (body {cfg with layers := 0} direct outputDirect) G input env' tape)‖ ≤
      (κ*W)*B := by
  let Z : Fin n → Point d := fun i => (tape.1 i).1
  let X := fun i => storedPoint env (direct i)+input.coefficient cfg.noise • Z i
  let X' := fun i => storedPoint env' (direct i)+input.coefficient cfg.noise • Z i
  let ρ : Env d (replyCtx n (replyCtx n Γ)) := Env.prepend X (Env.prepend Z env)
  let ρ' : Env d (replyCtx n (replyCtx n Γ)) := Env.prepend X' (Env.prepend Z env')
  have hs (r : Ref Γ .point) :
      storedPoint ρ (RefMap.shiftMany n (RefMap.shiftMany n r)) = storedPoint env r :=
    (prepend_shiftMany X (Env.prepend Z env) (RefMap.shiftMany n r)).trans
      (prepend_shiftMany Z env r)
  have hs' (r : Ref Γ .point) :
      storedPoint ρ' (RefMap.shiftMany n (RefMap.shiftMany n r)) = storedPoint env' r :=
    (prepend_shiftMany X' (Env.prepend Z env') (RefMap.shiftMany n r)).trans
      (prepend_shiftMany Z env' r)
  have hf := final_sub_le cf pf cfg.finalEquiv cfg.finalSlots cfg.rowWeight cfg.beta cfg.reserve
    batchRef (RefMap.shiftMany n (RefMap.shiftMany n outputDirect)) cfg.finalOrigin
    cfg.finalDesignated cfg.finalAuxiliary cfg.finalResidual cfg.finalReserve
    Tf coeffF G input ρ ρ' κ W B 0 hκ hB0 htableF hchildF hweight
    (fun i => by simpa only [ρ,ρ',prepend_batchRef,X,X',add_sub_add_right_eq_sub] using hB i)
    (by rw [hs,hs',hout,sub_self,norm_zero]) tape.2.2
  rw [run_body,run_body]
  simpa only [zero_add,childPoint,iterateThen,finish,ρ,ρ',X,X',Z] using hf

theorem code_zero_sub_le {c cf : Fin n → ℕ} {p : ∀ i, Program (c i) .point}
    {pf : ∀ i, Program (cf i) .point} (cfg : Config n C c cf p pf)
    (T : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (coeff : ∀ i, Fin (c i) → ℝ)
    (Tf : ∀ i, Fin (tapeShape (pf i)).gaussianBlocks → Fin (tapeShape (pf i)).gaussianBlocks → ℝ)
    (coeffF : ∀ i, Fin (cf i) → ℝ) (G : Point d → Point d) (input : Inputs d C)
    (κ W : ℝ) (hκ : 0 ≤ κ)
    (htable : ∀ i, input.coefficient ∘ (cfg.mainSlots ∘ childSlot c p i) = matrixTable (T i) (coeff i))
    (htableF : ∀ i, input.coefficient ∘ cfg.finalSlots i = matrixTable (Tf i) (coeffF i))
    (hchildF : ∀ i, ChildStable (pf i) (coeffF i) G κ)
    (hweight : ∑ i, |input.coefficient (cfg.rowWeight i)| ≤ W)
    (input' : Inputs d C)
    (hcoeff : input'.coefficient = input.coefficient) (tape : Tape d (code {cfg with layers := 0})) :
    ‖childPoint (run (code {cfg with layers := 0}) G input Env.empty tape) -
      childPoint (run (code {cfg with layers := 0}) G input' Env.empty tape)‖ ≤
      (κ*W)*‖input.center-input'.center‖ := by
  let Y : Point d := tape.2.1
  let ρ : Env d (replyCtx n [.point,.scalar,.point,.point]) := setupEnv cfg input Y
  let ρ' : Env d (replyCtx n [.point,.scalar,.point,.point]) := setupEnv cfg input' Y
  have hout : storedPoint ρ (RefMap.shiftMany n Ref.here) =
      storedPoint ρ' (RefMap.shiftMany n Ref.here) := by
    simp only [ρ,ρ',setupEnv_output,hcoeff]
  have hd (i : Fin n) : ‖storedPoint ρ (batchRef i)-storedPoint ρ' (batchRef i)‖ ≤
      ‖input.center-input'.center‖ := by
    simp only [ρ,ρ',setupEnv_direct,hcoeff,add_sub_add_right_eq_sub,le_refl]
  have hb := body_zero_sub_le cfg Tf coeffF G input κ W hκ htableF
    hchildF hweight batchRef (RefMap.shiftMany n Ref.here) ρ ρ'
    ‖input.center-input'.center‖ (norm_nonneg _) hd hout tape.2.2.2.2.2
  have ht := body_same_coefficients {cfg with layers := 0} batchRef (RefMap.shiftMany n Ref.here)
    T coeff Tf coeffF G input input' ρ' hcoeff htable htableF tape.2.2.2.2.2
  rw [← ht] at hb
  rw [run_code_setup,run_code_setup]
  exact hb


variable (S : SamplingGeometry m) (e : Fin n ≃ S.Node) (r Ds : ℝ)
    (main final : Fin n → ExecutableData) (G : Point d → Point d) (κ : ℝ)
    (hm : 0 < m) (hr : 0 ≤ r) (hκ : 0 ≤ κ)
    (hfinal : ∀ i, ChildStable (final i).program (final i).coefficient G κ)
include hm hr hκ hfinal

theorem build_zero_sub_le (P x y : Point d)
    (tape : Tape d (SamplingExecutable.build S e r Ds main final 0).program) :
    ‖childPoint (run (SamplingExecutable.build S e r Ds main final 0).program G
        ⟨(SamplingExecutable.build S e r Ds main final 0).coefficient,x,P⟩ Env.empty tape) -
      childPoint (run (SamplingExecutable.build S e r Ds main final 0).program G
        ⟨(SamplingExecutable.build S e r Ds main final 0).coefficient,y,P⟩ Env.empty tape)‖ ≤
      κ*r*‖x-y‖ := by
  let cfg := samplingConfig main final 0
  let input : Inputs d (samplingSize main final) := ⟨samplingTable S e r Ds main final,x,P⟩
  let T := fun i => CovarianceSetup.childRoot (samplingNoise S r Ds)
    (S.radius r (e i)) (main i).shiftVector
  let Tf := fun i => CovarianceSetup.childRoot (samplingNoise S r Ds)
    (S.radius r (e i)) (final i).shiftVector
  have ht (i : Fin n) : input.coefficient ∘
      (cfg.mainSlots ∘ childSlot (fun i => (main i).size) (fun i => (main i).program) i) =
      matrixTable (T i) (main i).coefficient := by
    funext j
    simp only [input,cfg,samplingConfig,Function.comp_apply,samplingTable_main,
      samplingMainTable,RecursiveMeanPublicTable.sourceLayerTable,layerTable_child,T,samplingNoise]
  have htf (i : Fin n) : input.coefficient ∘ cfg.finalSlots i =
      matrixTable (Tf i) (final i).coefficient := by
    funext j
    simp only [input,cfg,samplingConfig,Function.comp_apply,samplingTable_final,Tf]
  have hw : (∑ i, |input.coefficient (cfg.rowWeight i)|) ≤ r := by
    simpa only [input,cfg,samplingConfig,samplingTable_scalar,samplingScalarTable,
      Fin.append_right,Fin.append_left] using (sampling_final_mass S e r hm hr).le
  exact code_zero_sub_le cfg T (fun i => (main i).coefficient) Tf (fun i => (final i).coefficient)
    G input κ r hκ ht htf hfinal hw ⟨samplingTable S e r Ds main final,y,P⟩ rfl tape

/-- Arbitrary main programs remain in the literal carrier, without main IHs. -/
theorem build_zero_childStable :
    ChildStable (SamplingExecutable.build S e r Ds main final 0).program
      (SamplingExecutable.build S e r Ds main final 0).coefficient G (κ*r) := by
  intro P x y z rest
  exact build_zero_sub_le S e r Ds main final G κ hm hr hκ hfinal P x y (joinTape _ z rest)

end AcceleratedLogConcave.Oracle.FixedTapeSampling
