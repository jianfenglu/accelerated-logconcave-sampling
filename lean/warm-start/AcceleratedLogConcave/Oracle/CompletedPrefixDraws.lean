import AcceleratedLogConcave.Oracle.GeneralMainFocus
import AcceleratedLogConcave.Oracle.MeanExecutionSchedule

/-! Read only already-completed layer coordinates.
No flow-reference analysis, new law assumption or independent noise copy. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.CompletedPrefixDraws
open MeasureTheory AffineLowering TapeLowering NoisyLayer SourceMeanLayer
open RecursiveMeanProgram RecursiveMeanContinuation GeneralMainFocus
open CanonicalTapeLaw
open TailOccurrenceCut TailOccurrenceCut.TailCut CanonicalTapeMeasurability

variable {n C : ℕ} {Ξ : Ctx} {τ : Ty}
  (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
  (slots : Fin (publicSize c p) → Fin C)
  (en : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
  (outer : ℕ → Origin) (designated residual : ℕ → Fin n → Origin)
  (auxiliary : ℕ → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
  (finish : ∀ {Δ : Ctx}, (Fin n → Ref Δ .point) →
    (Fin n → Ref Δ .point) → RefMap Ξ Δ → Prog C Δ τ)

local notation "loop" => iterateThen c p slots en outer designated residual auxiliary finish

variable {d : ℕ}

/-- Query elapsed j strictly BEFORE the current k. The literal first coordinate
of freshChild is its designated momentum; every residualDraw has first draw. -/
def completed : (N k : ℕ) → (hk : k<N) → {Γ : Ctx} →
    (old direct : Fin n → Ref Γ .point) → (saved : RefMap Ξ Γ) →
    (j : ℕ) → (hj : j<k) →
    Prefix d (focus c p slots en outer designated residual auxiliary finish
      N k hk old direct saved).cut → ((Fin n → Point d) × (Fin n → Point d))
  | 0, _, hk, _, _, _, _, _, _, _ => False.elim (Nat.not_lt_zero _ hk)
  | _+1, 0, _, _, _, _, _, j, hj, _ => False.elim (Nat.not_lt_zero j hj)
  | _N+1, _k+1, _hk, _, _old, _direct, _saved, 0, _, h =>
      (fun i => (h.1 i).1, fun i => (h.2.1 i).1)
  | N+1, k+1, hk, _, _old, direct, saved, j+1, hj, h =>
      completed N k (Nat.lt_of_succ_lt_succ hk) batchRef
        (fun i => preserveDirect (direct i)) (fun q => preserveDirect (saved q))
        j (Nat.lt_of_succ_lt_succ hj) h.2.2.2

theorem measurable_completed (N k : ℕ) (hk : k<N) {Γ : Ctx}
    (old direct : Fin n → Ref Γ .point) (saved : RefMap Ξ Γ)
    (j : ℕ) (hj : j<k) :
    @Measurable _ _ (prefixSpace d (focus c p slots en outer designated residual auxiliary finish
      N k hk old direct saved).cut) _
      (completed c p slots en outer designated residual auxiliary finish N k hk old direct saved j hj) := by
  let tapeMeasurable (c₀ : ℕ) (Γ₀ : Ctx) (τ₀ : Ty) (q : Prog c₀ Γ₀ τ₀) :
      MeasurableSpace (Tape d q) := tapeSpace d q
  let instructionMeasurable (c₀ : ℕ) (Γ₀ : Ctx) (τ₀ : Ty) (a : Instr c₀ Γ₀ τ₀) :
      MeasurableSpace (Instr.Tape d a) := instrSpace d a
  let cutMeasurable (c₀ : ℕ) (Γ₀ Δ₀ : Ctx) (τ₀ σ₀ : Ty)
      (q : Prog c₀ Δ₀ σ₀) (p : Prog c₀ Γ₀ τ₀) (t : TailCut q p) :
      MeasurableSpace (Prefix d t) := prefixSpace d t
  induction N generalizing Γ k j with
  | zero => omega
  | succ N ih =>
      cases k with
      | zero => omega
      | succ k =>
          cases j with
          | zero =>
              exact (measurable_pi_iff.mpr (fun i =>
                ((measurable_pi_apply i).comp measurable_fst).fst)).prodMk
                (measurable_pi_iff.mpr (fun i =>
                  ((measurable_pi_apply i).comp measurable_snd.fst).fst))
          | succ j =>
              exact (ih k (Nat.lt_of_succ_lt_succ hk) batchRef
                (fun i => preserveDirect (direct i)) (fun q => preserveDirect (saved q))
                j (Nat.lt_of_succ_lt_succ hj)).comp measurable_snd.snd.snd

/-- Equality with the existing raw-schedule coordinate observations, not a new
numerical noise process. The full original suffix remains in rawTapeEquiv. -/
theorem completed_eq_schedule (N k : ℕ) (hk : k<N) {Γ : Ctx}
    (old direct : Fin n → Ref Γ .point) (saved : RefMap Ξ Γ)
    (j : ℕ) (hj : j<k) (ω : Tape d (loop N old direct saved)) :
    completed c p slots en outer designated residual auxiliary finish N k hk old direct saved j hj
      (split (focus c p slots en outer designated residual auxiliary finish N k hk old direct saved).cut ω).1 =
    ((fun i => MeanExecutionSchedule.designatedNoise c p finish N
        (rawTapeEquiv c p slots en outer designated residual auxiliary finish d N old direct saved) j i ω),
     (fun i => MeanExecutionSchedule.residualNoise c p finish N
        (rawTapeEquiv c p slots en outer designated residual auxiliary finish d N old direct saved) j i ω)) := by
  induction N generalizing Γ k j with
  | zero => omega
  | succ N ih =>
      cases k with
      | zero => omega
      | succ k =>
          cases j with
          | zero => rfl
          | succ j =>
              exact ih k (Nat.lt_of_succ_lt_succ hk) batchRef
                (fun i => preserveDirect (direct i)) (fun q => preserveDirect (saved q))
                j (Nat.lt_of_succ_lt_succ hj) ω.2.2.2

end AcceleratedLogConcave.Oracle.CompletedPrefixDraws
