import AcceleratedLogConcave.Oracle.TailOccurrenceCut
import AcceleratedLogConcave.Oracle.RecursiveMeanFinalState

/-! Literal interpreter values at a syntax-tail cut. The entering environment
is evaluated from exactly the consumed prefix, and the untouched suffix is
the original suffix. No law or execution-correctness premise is supplied. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Oracle.TailOccurrenceCut.TailCut
open TapeLowering
variable {d c : ℕ} {Γ Δ : Ctx} {τ : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ τ}

/-- Compose two cuts through the same original continuation. -/
def trans {c : ℕ} {Γ Δ Ξ : Ctx} {τ σ υ : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ σ} {r : Prog c Ξ υ}
    (inner : TailCut r q) (outer : TailCut q p) : TailCut r p := by
  induction outer with
  | here => exact inner
  | step o a next cut ih => exact .step o a next ih
  | batch o children next cut ih => exact .batch o children next ih

theorem run_join_value_heq {d c : ℕ} {Γ Δ : Ctx} {τ σ : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ σ}
    (G : Point d → Point d) (input : Inputs d c) (cut : TailCut q p) :
    ∀ (env : Env d Γ) (h : Prefix d cut) (suffix : Tape d q),
      HEq (run p G input env (join cut (h,suffix))).value
        (run q G input (envAt G input cut env h) suffix).value := by
  induction cut with
  | here => intro env h suffix; rfl
  | step o a next cut ih =>
    intro env h suffix
    exact ih (Env.cons (evalInstr o a G input env h.1).value env) h.2 suffix
  | batch o children next cut ih =>
    intro env h suffix
    exact ih (Env.prepend (fun i => (run (children i) G input env (h.1 i)).value) env)
      h.2 suffix

/-- Rejoining the original prefix and suffix runs the selected suffix from the
actual prefix store. Preceding child batches use their complete original tapes. -/
theorem run_join_value (G : Point d → Point d) (input : Inputs d c) (cut : TailCut q p) :
    ∀ (env : Env d Γ) (h : Prefix d cut) (suffix : Tape d q),
      (run p G input env (join cut (h,suffix))).value =
        (run q G input (envAt G input cut env h) suffix).value := by
  intro env h suffix
  exact eq_of_heq (run_join_value_heq G input cut env h suffix)

/-- The same identity on every original full tape, retaining its actual split. -/
theorem run_split_value (G : Point d → Point d) (input : Inputs d c)
    (cut : TailCut q p) (env : Env d Γ) (ω : Tape d p) :
    (run p G input env ω).value =
      (run q G input (envAt G input cut env (split cut ω).1) (split cut ω).2).value := by
  have h := run_join_value G input cut env (split cut ω).1 (split cut ω).2
  simpa only [Prod.mk.eta, join_split] using h

end AcceleratedLogConcave.Oracle.TailOccurrenceCut.TailCut

namespace AcceleratedLogConcave.Oracle.RecursiveMeanContinuation
open AffineLowering TapeLowering NoisyLayer RecursiveMeanProgram SourceMeanLayer
open TailOccurrenceCut
variable {n C : ℕ} {Ξ Γ : Ctx} {τ : Ty}
    (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (slots : Fin (publicSize c p) → Fin C)
    (en : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (outer : ℕ → Origin) (designated residual : ℕ → Fin n → Origin)
    (auxiliary : ℕ → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (finish : ∀ {Δ : Ctx}, (Fin n → Ref Δ .point) →
      (Fin n → Ref Δ .point) → RefMap Ξ Δ → Prog C Δ τ)

/-- Exact typed finish continuation after all original loop layers. -/
structure FinishFocus {Γ : Ctx} (host : Prog C Γ τ) where
  ctx : Ctx
  old : Fin n → Ref ctx .point
  direct : Fin n → Ref ctx .point
  saved : RefMap Ξ ctx
  cut : TailCut (finish old direct saved) host

def atFinish : (N : ℕ) → {Γ : Ctx} →
    (old direct : Fin n → Ref Γ .point) → (saved : RefMap Ξ Γ) →
    FinishFocus finish (iterateThen c p slots en outer designated residual auxiliary finish
      N old direct saved)
  | 0, Γ, old, direct, saved => ⟨Γ,old,direct,saved,.here⟩
  | N+1, _, old, direct, saved =>
      let f := atFinish N batchRef (fun j => preserveDirect (direct j))
        (fun r => preserveDirect (saved r))
      ⟨f.ctx,f.old,f.direct,f.saved,
        .batch (outer N) (fun i => freshChild (p i) (en i) (slots ∘ childSlot c p i)
          (old i) (designated N i) (auxiliary N i)) _
          (.batch [] (fun i => residualDraw (residual N i)) _
            (.batch [] (noisyRow (fun j l => slots (aSlot c p j l))
              (fun j l => slots (residualSlot c p j l)) direct) _ f.cut))⟩

end AcceleratedLogConcave.Oracle.RecursiveMeanContinuation
