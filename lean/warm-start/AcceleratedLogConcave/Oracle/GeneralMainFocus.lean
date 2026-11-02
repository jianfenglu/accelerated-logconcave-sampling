import AcceleratedLogConcave.Oracle.PrivateOccurrencePath

/-! Deterministic bounded main occurrence, preserving original
remaining-loop origins and the entire suffix. No random stopping-time claim. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.GeneralMainFocus
open AffineLowering TapeLowering NoisyLayer SourceMeanLayer
open RecursiveMeanProgram RecursiveMeanContinuation TailOccurrenceCut TailOccurrenceCut.TailCut

variable {n C : ℕ} {Ξ : Ctx} {τ : Ty}
  (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
  (slots : Fin (publicSize c p) → Fin C)
  (en : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
  (outer : ℕ → Origin) (designated residual : ℕ → Fin n → Origin)
  (auxiliary : ℕ → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
  (finish : ∀ {Δ : Ctx}, (Fin n → Ref Δ .point) →
    (Fin n → Ref Δ .point) → RefMap Ξ Δ → Prog C Δ τ)

local notation "loop" => iterateThen c p slots en outer designated residual auxiliary finish

structure Focus {Γ : Ctx} (host : Prog C Γ τ) where
  remainingAfter : ℕ
  ctx : Ctx
  old : Fin n → Ref ctx .point
  direct : Fin n → Ref ctx .point
  saved : RefMap Ξ ctx
  cut : TailCut (loop (remainingAfter+1) old direct saved) host

/-- This constructor is not defined outside k<N; no saturated cursor ambiguity. -/
def focus : (N k : ℕ) → (hk : k < N) → {Γ : Ctx} →
    (old direct : Fin n → Ref Γ .point) → (saved : RefMap Ξ Γ) →
    Focus c p slots en outer designated residual auxiliary finish (loop N old direct saved)
  | 0, k, hk, _, _, _, _ => False.elim (Nat.not_lt_zero k hk)
  | N+1, 0, _, Γ, old, direct, saved => ⟨N,Γ,old,direct,saved,.here⟩
  | N+1, k+1, hk, _, old, direct, saved =>
      let f := focus N k (Nat.lt_of_succ_lt_succ hk) batchRef
        (fun j => preserveDirect (direct j)) (fun q => preserveDirect (saved q))
      ⟨f.remainingAfter,f.ctx,f.old,f.direct,f.saved,
        .batch (outer N) (fun i => freshChild (p i) (en i) (slots ∘ childSlot c p i)
          (old i) (designated N i) (auxiliary N i)) _
          (.batch [] (fun i => residualDraw (residual N i)) _
            (.batch [] (noisyRow (fun j l => slots (aSlot c p j l))
              (fun j l => slots (residualSlot c p j l)) direct) _ f.cut))⟩

theorem remaining_eq (N k : ℕ) (hk : k<N) {Γ : Ctx}
    (old direct : Fin n → Ref Γ .point) (saved : RefMap Ξ Γ) :
    (focus c p slots en outer designated residual auxiliary finish N k hk old direct saved).remainingAfter
      = N-1-k := by
  induction N generalizing Γ k with
  | zero => omega
  | succ N ih =>
      cases k with
      | zero => simp [focus]
      | succ k =>
          dsimp only [focus]
          rw [ih]
          omega

set_option backward.isDefEq.respectTransparency false in
/-- Literal prefix interpreter agrees with the RECEIVED cursor's stored old
reference. The induction compares intermediate stores, never final outputs. -/
theorem readout_eq_cursor {d : ℕ} (G : Point d → Point d) (input : Inputs d C)
    (N k : ℕ) (hk : k<N) {Γ : Ctx} (old direct : Fin n → Ref Γ .point)
    (saved : RefMap Ξ Γ) (env : Env d Γ) (ω : Tape d (loop N old direct saved))
    (i : Fin n) :
    let f := focus c p slots en outer designated residual auxiliary finish N k hk old direct saved
    let st := prefixCursor c p slots en outer designated residual auxiliary finish
      G input N k old direct saved env ω
    storedPoint (envAt G input f.cut env (split f.cut ω).1) (f.old i) =
      storedPoint st.env (st.old i) := by
  induction N generalizing Γ k with
  | zero => omega
  | succ N ih =>
      cases k with
      | zero => rfl
      | succ k =>
          rcases ω with ⟨wq, wz, wr, wt⟩
          dsimp only [focus, split, envAt, prefixCursor]
          simp only [residualDraw, run, evalInstr, Env.cons]
          simp only [run_noisyRow, pointResult]
          exact ih k (Nat.lt_of_succ_lt_succ hk) batchRef
            (fun j => preserveDirect (direct j)) (fun q => preserveDirect (saved q)) _ _

end AcceleratedLogConcave.Oracle.GeneralMainFocus
