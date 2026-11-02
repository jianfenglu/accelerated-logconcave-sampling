import AcceleratedLogConcave.Oracle.MeanFinalAssemblyReadout
import AcceleratedLogConcave.Oracle.SourceMeanExecutionRms

/-! Exact interpreter state/tape at the canonical paid-final cut. These
identities compare the actual finite execution schedules, not benchmark and
true iterate centers. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
set_option maxHeartbeats 1200000
namespace AcceleratedLogConcave.Oracle.MeanFinalEvaluatorReadout
open AffineLowering TapeLowering NoisyLayer SourceMeanLayer RecursiveMeanProgram
open RecursiveMeanContinuation TailOccurrenceCut TailCut
variable {n C d : ℕ} {Ξ : Ctx} {τ : Ty}
  (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
  (slots : Fin (publicSize c p) → Fin C)
  (en : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
  (outer : ℕ → Origin) (designated residual : ℕ → Fin n → Origin)
  (auxiliary : ℕ → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
  (finish : ∀ {Δ : Ctx}, (Fin n → Ref Δ .point) →
    (Fin n → Ref Δ .point) → RefMap Ξ Δ → Prog C Δ τ)
  (G : Point d → Point d) (input : Inputs d C)

/-- FinalState reconstructed by splitting the same original tape at its
canonical finish cut and interpreting its entire consumed prefix. -/
def focusedState (N : ℕ) {Γ : Ctx} (old direct : Fin n → Ref Γ .point)
    (saved : RefMap Ξ Γ) (env : Env d Γ)
    (ω : Tape d (iterateThen c p slots en outer designated residual auxiliary finish N old direct saved)) :
    FinalState C n d Ξ τ finish :=
  let f := atFinish c p slots en outer designated residual auxiliary finish N old direct saved
  ⟨f.ctx,f.old,f.direct,f.saved,envAt G input f.cut env (split f.cut ω).1,(split f.cut ω).2⟩

private theorem residual_value {c d : ℕ} {Γ : Ctx} (o : Origin)
    (G : Point d → Point d) (input : Inputs d c) (env : Env d Γ)
    (ω : Tape d (residualDraw (c := c) (Γ := Γ) o)) :
    (run (residualDraw o) G input env ω).value = ω.1 := rfl

/-- Literal noisy rows and residual instructions identify the two complete
state/tape constructions, including every original reference and paid suffix. -/
theorem focusedState_eq_finalState (N : ℕ) {Γ : Ctx} (old direct : Fin n → Ref Γ .point)
    (saved : RefMap Ξ Γ) (env : Env d Γ)
    (ω : Tape d (iterateThen c p slots en outer designated residual auxiliary finish N old direct saved)) :
    focusedState c p slots en outer designated residual auxiliary finish G input N old direct saved env ω =
      finalState c p slots en outer designated residual auxiliary finish G input N old direct saved env ω := by
  induction N generalizing Γ with
  | zero => rfl
  | succ N ih =>
      rcases ω with ⟨wq,wz,wr,wt⟩
      dsimp only [focusedState,atFinish,split,envAt,finalState]
      simp only [residual_value,run_noisyRow,pointResult]
      exact ih batchRef (fun j => preserveDirect (direct j))
        (fun q => preserveDirect (saved q)) _ wt

end AcceleratedLogConcave.Oracle.MeanFinalEvaluatorReadout
