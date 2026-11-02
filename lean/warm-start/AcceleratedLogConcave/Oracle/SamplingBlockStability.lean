import AcceleratedLogConcave.Oracle.SamplingReadoutStability

/-! Actual sampling setup and finite loop stability under explicit child IHs. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.FixedTapeSampling
open TapeLowering AffineLowering NoisyLayer RecursiveMeanProgram RecursiveMeanContinuation
open PrivateSamplingProgram FixedTapeStability RetainedMeanFinalBatch
open scoped BigOperators

section Block
variable {c cf : Fin n → ℕ} {p : ∀ i, Program (c i) .point}
    {pf : ∀ i, Program (cf i) .point} (cfg : Config n C c cf p pf)
    (T : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (coeff : ∀ i, Fin (c i) → ℝ)
    (Tf : ∀ i, Fin (tapeShape (pf i)).gaussianBlocks → Fin (tapeShape (pf i)).gaussianBlocks → ℝ)
    (coeffF : ∀ i, Fin (cf i) → ℝ) (G : Point d → Point d) (input : Inputs d C)
    (κ a W : ℝ) (hκ : 0 ≤ κ) (ha : 0 ≤ a) (hW : 0 ≤ W)
    (htable : ∀ i, input.coefficient ∘ (cfg.mainSlots ∘ childSlot c p i) = matrixTable (T i) (coeff i))
    (htableF : ∀ i, input.coefficient ∘ cfg.finalSlots i = matrixTable (Tf i) (coeffF i))
    (hchild : ∀ i, ChildStable (p i) (coeff i) G κ)
    (hchildF : ∀ i, ChildStable (pf i) (coeffF i) G κ)
    (hrow : ∀ i, ∑ j, |input.coefficient (cfg.mainSlots (aSlot c p i j))| ≤ a)
    (hweight : ∑ i, |input.coefficient (cfg.rowWeight i)| ≤ W)
include hκ ha htable htableF hchild hchildF hrow hweight

/-- Equal output-direct anchor; initialization contributes the direct displacement B. -/
theorem body_sub_le_growth {Γ : Ctx} (direct : Fin n → Ref Γ .point)
    (outputDirect : Ref Γ .point) (env env' : Env d Γ) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ i, ‖storedPoint env (direct i)-storedPoint env' (direct i)‖ ≤ B)
    (hout : storedPoint env outputDirect = storedPoint env' outputDirect)
    (tape : Tape d (body cfg direct outputDirect)) :
    ‖childPoint (run (body cfg direct outputDirect) G input env tape) -
      childPoint (run (body cfg direct outputDirect) G input env' tape)‖ ≤
      (κ*W)*growth (κ*a) B B cfg.layers := by
  let finisher := fun {Δ : Ctx} (old _ : Fin n → Ref Δ .point) (saved : RefMap Γ Δ) =>
    finish cfg old (saved outputDirect)
  have hf : ∀ {Δ : Ctx} (old dir : Fin n → Ref Δ .point) (saved : RefMap Γ Δ)
      (ρ ρ' : Env d Δ) (tail : Tape d (finisher old dir saved)) (D : ℝ),
      0 ≤ D → (∀ i, ‖storedPoint ρ (old i)-storedPoint ρ' (old i)‖ ≤ D) →
      storedPoint ρ (saved outputDirect) = storedPoint ρ' (saved outputDirect) →
      (∀ i : Fin 0, storedPoint ρ (saved (Fin.elim0 i)) =
        storedPoint ρ' (saved (Fin.elim0 i))) →
      ‖childPoint (run (finisher old dir saved) G input ρ tail) -
        childPoint (run (finisher old dir saved) G input ρ' tail)‖ ≤ (κ*W)*D := by
    intro Δ old dir saved ρ ρ' tail D hD hd hp _
    have h := final_sub_le cf pf cfg.finalEquiv cfg.finalSlots cfg.rowWeight cfg.beta cfg.reserve
      old (saved outputDirect) cfg.finalOrigin cfg.finalDesignated cfg.finalAuxiliary
      cfg.finalResidual cfg.finalReserve Tf coeffF G input ρ ρ' κ W D 0 hκ hD htableF
      hchildF hweight hd (by rw [hp,sub_self,norm_zero]) tail
    simpa only [finisher,finish,zero_add] using h
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
  have hi := iterateThen_sub_le_growth c p cfg.mainSlots cfg.mainEquiv cfg.layerOrigin
    cfg.mainDesignated cfg.mainResidual cfg.mainAuxiliary finisher T coeff G input κ a B
    hκ ha hB0 htable hchild hrow outputDirect (fun i : Fin 0 => Fin.elim0 i) (κ*W) hf
    cfg.layers batchRef (fun i => RefMap.shiftMany n (RefMap.shiftMany n (direct i)))
    (fun r => RefMap.shiftMany n (RefMap.shiftMany n r)) ρ ρ' tape.2.2 B hB0
    (fun i => by rw [hs,hs']; exact hB i)
    (fun i => by simpa only [ρ,ρ',prepend_batchRef,X,X',add_sub_add_right_eq_sub] using hB i)
    (by rw [hs,hs']; exact hout) (fun i => Fin.elim0 i)
  rw [run_body,run_body]
  exact hi

/-- Setup centers may differ. Coefficient-only transport normalizes the second host input. -/
theorem code_sub_le_growth (input' : Inputs d C)
    (hcoeff : input'.coefficient = input.coefficient) (tape : Tape d (code cfg)) :
    ‖childPoint (run (code cfg) G input Env.empty tape) -
      childPoint (run (code cfg) G input' Env.empty tape)‖ ≤
      (κ*W)*growth (κ*a) ‖input.center-input'.center‖ ‖input.center-input'.center‖ cfg.layers := by
  let Y : Point d := tape.2.1
  let ρ : Env d (replyCtx n [.point,.scalar,.point,.point]) := setupEnv cfg input Y
  let ρ' : Env d (replyCtx n [.point,.scalar,.point,.point]) := setupEnv cfg input' Y
  have hout : storedPoint ρ (RefMap.shiftMany n Ref.here) =
      storedPoint ρ' (RefMap.shiftMany n Ref.here) := by
    simp only [ρ,ρ',setupEnv_output,hcoeff]
  have hd (i : Fin n) : ‖storedPoint ρ (batchRef i)-storedPoint ρ' (batchRef i)‖ ≤
      ‖input.center-input'.center‖ := by
    simp only [ρ,ρ',setupEnv_direct,hcoeff,add_sub_add_right_eq_sub,le_refl]
  have hb := body_sub_le_growth cfg T coeff Tf coeffF G input κ a W hκ ha htable htableF
    hchild hchildF hrow hweight batchRef (RefMap.shiftMany n Ref.here) ρ ρ'
    ‖input.center-input'.center‖ (norm_nonneg _) hd hout tape.2.2.2.2.2
  have ht := body_same_coefficients cfg batchRef (RefMap.shiftMany n Ref.here)
    T coeff Tf coeffF G input input' ρ' hcoeff htable htableF tape.2.2.2.2.2
  rw [← ht] at hb
  rw [run_code_setup,run_code_setup]
  exact hb

include hW in
/-- Actual finite sampling code, including its initialization and fresh final row. -/
theorem code_sub_le (input' : Inputs d C) (hcoeff : input'.coefficient = input.coefficient)
    (tape : Tape d (code cfg)) :
    ‖childPoint (run (code cfg) G input Env.empty tape) -
      childPoint (run (code cfg) G input' Env.empty tape)‖ ≤
      κ*W*‖input.center-input'.center‖*∑ j ∈ Finset.range (cfg.layers+1), (κ*a)^j := by
  have hb := code_sub_le_growth cfg T coeff Tf coeffF G input κ a W hκ ha htable htableF
    hchild hchildF hrow hweight input' hcoeff tape
  calc
    _ ≤ (κ*W)*growth (κ*a) ‖input.center-input'.center‖ ‖input.center-input'.center‖ cfg.layers := hb
    _ ≤ (κ*W)*((κ*a)^cfg.layers*‖input.center-input'.center‖+
        ‖input.center-input'.center‖*∑ j ∈ Finset.range cfg.layers, (κ*a)^j) :=
      mul_le_mul_of_nonneg_left (growth_le (κ*a) _ _ (mul_nonneg hκ ha) cfg.layers)
        (mul_nonneg hκ hW)
    _ = _ := by rw [Finset.sum_range_succ]; ring
end Block

end AcceleratedLogConcave.Oracle.FixedTapeSampling
