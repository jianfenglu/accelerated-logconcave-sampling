import AcceleratedLogConcave.Oracle.FixedTapeMainReadout
import AcceleratedLogConcave.Oracle.PrivateSamplingValue
import AcceleratedLogConcave.Oracle.ExecutableInputFree

/-! Fixed-tape sampling readout and coefficient-only host-input transport.
The fresh final row retains its direct displacement and both shared noise terms. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.FixedTapeSampling
open TapeLowering AffineLowering NoisyLayer RecursiveMeanProgram RecursiveMeanContinuation
open SourceMeanLayer PrivateSamplingProgram FixedTapeStability
open RetainedMeanFinalBatch
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false in
/-- General fresh final readout; its direct output need not agree. -/
theorem final_sub_le (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (slots : ∀ i, Fin (childSize (p i)) → Fin C)
    (weight : Fin n → Fin C) (beta reserve : Fin C)
    (old : Fin n → Ref Γ .point) (direct : Ref Γ .point)
    (outer : Origin) (designated : Fin n → Origin)
    (auxiliary : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (residualOrigin reserveOrigin : Origin)
    (T : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (coeff : ∀ i, Fin (c i) → ℝ) (G : Point d → Point d) (input : Inputs d C)
    (env env' : Env d Γ) (κ W D Dout : ℝ) (hκ : 0 ≤ κ) (hD : 0 ≤ D)
    (htable : ∀ i, input.coefficient ∘ slots i = matrixTable (T i) (coeff i))
    (hchild : ∀ i, ChildStable (p i) (coeff i) G κ)
    (hweight : ∑ i, |input.coefficient (weight i)| ≤ W)
    (hold : ∀ i, ‖storedPoint env (old i)-storedPoint env' (old i)‖ ≤ D)
    (hout : ‖storedPoint env direct-storedPoint env' direct‖ ≤ Dout)
    (tape : Tape d (PrivateSamplingFinal.code c p e slots weight beta reserve old direct
      outer designated auxiliary residualOrigin reserveOrigin)) :
    ‖childPoint (run (PrivateSamplingFinal.code c p e slots weight beta reserve old direct
        outer designated auxiliary residualOrigin reserveOrigin) G input env tape) -
      childPoint (run (PrivateSamplingFinal.code c p e slots weight beta reserve old direct
        outer designated auxiliary residualOrigin reserveOrigin) G input env' tape)‖ ≤
      Dout+κ*W*D := by
  rw [PrivateSamplingFinal.run_code,PrivateSamplingFinal.run_code]
  dsimp only [childPoint]
  rw [add_sub_add_right_eq_sub,add_sub_add_comm,← Finset.sum_sub_distrib]
  simp only [← smul_sub]
  have hc (i : Fin n) := (freshChild_sub_le (p i) (e i) (slots i) (old i)
    (designated i) (auxiliary i) (T i) (coeff i) G input env env' (htable i) κ
    (hchild i) (tape.1 i)).trans (mul_le_mul_of_nonneg_left (hold i) hκ)
  have hs := Numerics.AffineGraph.norm_sum_smul_le_of_norm_le
    (fun i => input.coefficient (weight i))
    (fun i => childPoint (run (freshChild (p i) (e i) (slots i) (old i)
      (designated i) (auxiliary i)) G input env (tape.1 i)) -
      childPoint (run (freshChild (p i) (e i) (slots i) (old i)
      (designated i) (auxiliary i)) G input env' (tape.1 i)))
    hweight (mul_nonneg hκ hD) hc
  calc
    _ ≤ ‖storedPoint env direct-storedPoint env' direct‖ + _ := norm_add_le _ _
    _ ≤ Dout+W*(κ*D) := add_le_add hout (by simpa only [childPoint,PrivateSamplingFinal.pointValue] using hs)
    _ = _ := by ring

set_option backward.isDefEq.respectTransparency false in
/-- At a fixed store, the sampling finish reads only host coefficients. -/
theorem finish_same_coefficients {c cf : Fin n → ℕ} {p : ∀ i, Program (c i) .point}
    {pf : ∀ i, Program (cf i) .point} (cfg : Config n C c cf p pf)
    (old : Fin n → Ref Γ .point) (direct : Ref Γ .point)
    (T : ∀ i, Fin (tapeShape (pf i)).gaussianBlocks → Fin (tapeShape (pf i)).gaussianBlocks → ℝ)
    (coeff : ∀ i, Fin (cf i) → ℝ) (G : Point d → Point d)
    (input input' : Inputs d C) (env : Env d Γ)
    (hcoeff : input'.coefficient = input.coefficient)
    (htable : ∀ i, input.coefficient ∘ cfg.finalSlots i = matrixTable (T i) (coeff i))
    (tape : Tape d (finish cfg old direct)) :
    childPoint (run (finish cfg old direct) G input' env tape) =
      childPoint (run (finish cfg old direct) G input env tape) := by
  unfold finish at tape ⊢
  rw [PrivateSamplingFinal.run_code,PrivateSamplingFinal.run_code]
  dsimp only [childPoint]
  have hc (i : Fin n) := freshChild_same_coefficients (pf i) (cfg.finalEquiv i)
    (cfg.finalSlots i) (old i) (cfg.finalDesignated i) (cfg.finalAuxiliary i)
    (T i) (coeff i) G input input' env hcoeff (htable i) (tape.1 i)
  simp only [hc,hcoeff]

section InputTransport
variable (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (slots : Fin (publicSize c p) → Fin C)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (outer : ℕ → Origin) (designated residual : ℕ → Fin n → Origin)
    (auxiliary : ℕ → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (finisher : ∀ {Δ : Ctx}, (Fin n → Ref Δ .point) →
      (Fin n → Ref Δ .point) → RefMap Ξ Δ → Prog C Δ .point)
    (T : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (coeff : ∀ i, Fin (c i) → ℝ) (G : Point d → Point d) (input input' : Inputs d C)
    (hcoeff : input'.coefficient = input.coefficient)
    (htable : ∀ i, input.coefficient ∘ (slots ∘ childSlot c p i) = matrixTable (T i) (coeff i))
    (hfinish : ∀ {Δ : Ctx} (old direct : Fin n → Ref Δ .point) (saved : RefMap Ξ Δ)
      (env : Env d Δ) (tape : Tape d (finisher old direct saved)),
      childPoint (run (finisher old direct saved) G input' env tape) =
        childPoint (run (finisher old direct saved) G input env tape))
include hcoeff htable hfinish

set_option backward.isDefEq.respectTransparency false in
/-- Literal synchronized loop; host centers may differ, but the stored environment is fixed. -/
theorem iterateThen_same_coefficients (N : ℕ) {Γ : Ctx}
    (old direct : Fin n → Ref Γ .point) (saved : RefMap Ξ Γ) (env : Env d Γ)
    (tape : Tape d (iterateThen c p slots e outer designated residual auxiliary finisher
      N old direct saved)) :
    childPoint (run (iterateThen c p slots e outer designated residual auxiliary finisher
      N old direct saved) G input' env tape) =
      childPoint (run (iterateThen c p slots e outer designated residual auxiliary finisher
        N old direct saved) G input env tape) := by
  induction N generalizing Γ with
  | zero => exact hfinish old direct saved env tape
  | succ N ih =>
    have hc (i : Fin n) := freshChild_same_coefficients (p i) (e i)
      (slots ∘ childSlot c p i) (old i) (designated N i) (auxiliary N i)
      (T i) (coeff i) G input input' env hcoeff (htable i) (tape.1 i)
    have hv (Q Z : Fin n → Point d) :
        noisyValues (fun i j => slots (aSlot c p i j))
          (fun i j => slots (residualSlot c p i j)) direct input' env Q Z =
        noisyValues (fun i j => slots (aSlot c p i j))
          (fun i j => slots (residualSlot c p i j)) direct input env Q Z := by
      funext j
      simp only [noisyValues,hcoeff]
    dsimp only [iterateThen] at tape ⊢
    rw [run_layerAt,run_layerAt]
    simp only [childPoint,hc,hv]
    exact ih _ _ _ _ tape.2.2.2
end InputTransport

/-- Transport the initialized sampling body while keeping its actual setup store. -/
theorem body_same_coefficients {c cf : Fin n → ℕ} {p : ∀ i, Program (c i) .point}
    {pf : ∀ i, Program (cf i) .point} (cfg : Config n C c cf p pf)
    (direct : Fin n → Ref Γ .point) (outputDirect : Ref Γ .point)
    (T : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (coeff : ∀ i, Fin (c i) → ℝ)
    (Tf : ∀ i, Fin (tapeShape (pf i)).gaussianBlocks → Fin (tapeShape (pf i)).gaussianBlocks → ℝ)
    (coeffF : ∀ i, Fin (cf i) → ℝ) (G : Point d → Point d)
    (input input' : Inputs d C) (env : Env d Γ)
    (hcoeff : input'.coefficient = input.coefficient)
    (htable : ∀ i, input.coefficient ∘ (cfg.mainSlots ∘ childSlot c p i) = matrixTable (T i) (coeff i))
    (htableF : ∀ i, input.coefficient ∘ cfg.finalSlots i = matrixTable (Tf i) (coeffF i))
    (tape : Tape d (body cfg direct outputDirect)) :
    childPoint (run (body cfg direct outputDirect) G input' env tape) =
      childPoint (run (body cfg direct outputDirect) G input env tape) := by
  rw [run_body,run_body]
  dsimp only [childPoint]
  simp only [hcoeff]
  apply iterateThen_same_coefficients c p cfg.mainSlots cfg.mainEquiv cfg.layerOrigin
    cfg.mainDesignated cfg.mainResidual cfg.mainAuxiliary _ T coeff G input input' hcoeff htable
  intro Δ old dir saved ρ tail
  exact finish_same_coefficients cfg old (saved outputDirect) Tf coeffF G input input'
    ρ hcoeff htableF tail

end AcceleratedLogConcave.Oracle.FixedTapeSampling
