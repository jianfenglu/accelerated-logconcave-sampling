import AcceleratedLogConcave.Oracle.FixedTapeChildStability
import AcceleratedLogConcave.Oracle.RecursiveMeanFinalState
import AcceleratedLogConcave.Numerics.AffineBounds
import AcceleratedLogConcave.Numerics.Collocation

/-! Finite main-loop displacement for the actual stored-state recursion. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.FixedTapeStability
open TapeLowering AffineLowering NoisyLayer RecursiveMeanProgram
open RecursiveMeanContinuation SourceMeanLayer RetainedMeanFinalBatch
open scoped BigOperators

/-- Scalar recurrence used only to bound the actual interpreter state. -/
def growth (q B D : ℝ) (N : ℕ) : ℝ :=
  Numerics.Collocation.iteratePhi (fun x => q*x+B) D N

theorem growth_nonneg (q B D : ℝ) (hq : 0 ≤ q) (hB : 0 ≤ B) (hD : 0 ≤ D) (N : ℕ) :
    0 ≤ growth q B D N := by
  induction N with
  | zero => exact hD
  | succ N ih =>
    change 0 ≤ Numerics.Collocation.iteratePhi _ _ _
    rw [Numerics.Collocation.iteratePhi_succ]
    exact add_nonneg (mul_nonneg hq ih) hB

theorem growth_shift (q B D : ℝ) (N : ℕ) :
    growth q B (q*D+B) N = growth q B D (N+1) := by
  exact (Function.iterate_succ_apply (fun x => q*x+B) N D).symm

/-- Reuse the existing finite recurrence theorem with its exact forcing weights. -/
theorem growth_le (q B D : ℝ) (hq : 0 ≤ q) (N : ℕ) :
    growth q B D N ≤ q^N*D + B*∑ j ∈ Finset.range N, q^j := by
  apply Numerics.Collocation.error_le_uniform_finite_sum (growth q B D) q B N hq
  intro k _
  exact (congrArg (fun x => x ≤ q*growth q B D k+B)
    (Numerics.Collocation.iteratePhi_succ (fun x => q*x+B) D k)).mpr le_rfl

/-- Identical residual draws cancel before any norm estimate. -/
theorem noisyValues_sub_le (aSlots cSlots : Fin n → Fin n → Fin C)
    (direct : Fin n → Ref Γ .point) (input : Inputs d C) (env env' : Env d Γ)
    (Q Q' Z : Fin n → Point d) (a B D : ℝ) (hD : 0 ≤ D)
    (hrow : ∀ i, ∑ j, |input.coefficient (aSlots i j)| ≤ a)
    (hB : ∀ i, ‖storedPoint env (direct i)-storedPoint env' (direct i)‖ ≤ B)
    (hQ : ∀ j, ‖Q j-Q' j‖ ≤ D) (i : Fin n) :
    ‖noisyValues aSlots cSlots direct input env Q Z i -
      noisyValues aSlots cSlots direct input env' Q' Z i‖ ≤ B+a*D := by
  have hid : noisyValues aSlots cSlots direct input env Q Z i -
      noisyValues aSlots cSlots direct input env' Q' Z i =
      (storedPoint env (direct i)-storedPoint env' (direct i)) +
        ∑ j, input.coefficient (aSlots i j) • (Q j-Q' j) := by
    simp only [noisyValues,smul_sub,Finset.sum_sub_distrib]
    abel
  rw [hid]
  exact (norm_add_le _ _).trans (add_le_add (hB i)
    (Numerics.AffineGraph.norm_sum_smul_le_of_norm_le _ _ (hrow i) hD hQ))

section Main
variable (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (slots : Fin (publicSize c p) → Fin C)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (outer : ℕ → Origin) (designated residual : ℕ → Fin n → Origin)
    (auxiliary : ℕ → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (finish : ∀ {Δ : Ctx}, (Fin n → Ref Δ .point) →
      (Fin n → Ref Δ .point) → RefMap Ξ Δ → Prog C Δ τ)
    (T : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (coeff : ∀ i, Fin (c i) → ℝ)
    (G : Point d → Point d) (input : Inputs d C) (κ a B : ℝ)
    (hκ : 0 ≤ κ) (ha : 0 ≤ a) (hB0 : 0 ≤ B)
    (htable : ∀ i, input.coefficient ∘ (slots ∘ childSlot c p i) = matrixTable (T i) (coeff i))
    (hchild : ∀ i, ChildStable (p i) (coeff i) G κ)
    (hrow : ∀ i, ∑ j, |input.coefficient (slots (aSlot c p i j))| ≤ a)

include hκ ha hB0 htable hchild hrow

/-- Bound actual old-node readouts; contexts may grow and traces may differ. -/
theorem finalState_sub_le_growth (N : ℕ) {Γ : Ctx}
    (old direct : Fin n → Ref Γ .point) (saved : RefMap Ξ Γ)
    (env env' : Env d Γ)
    (tape : Tape d (iterateThen c p slots e outer designated residual auxiliary finish N old direct saved))
    (D0 : ℝ) (hD0 : 0 ≤ D0)
    (hB : ∀ i, ‖storedPoint env (direct i)-storedPoint env' (direct i)‖ ≤ B)
    (hD : ∀ i, ‖storedPoint env (old i)-storedPoint env' (old i)‖ ≤ D0) :
    let s := finalState c p slots e outer designated residual auxiliary finish G input N old direct saved env tape
    let s' := finalState c p slots e outer designated residual auxiliary finish G input N old direct saved env' tape
    ∀ i, ‖storedPoint s.env (s.old i)-storedPoint s'.env (s'.old i)‖ ≤ growth (κ*a) B D0 N := by
  induction N generalizing Γ D0 with
  | zero => exact hD
  | succ N ih =>
    let Q := fun i => childPoint (run (freshChild (p i) (e i) (slots ∘ childSlot c p i)
      (old i) (designated N i) (auxiliary N i)) G input env (tape.1 i))
    let Q' := fun i => childPoint (run (freshChild (p i) (e i) (slots ∘ childSlot c p i)
      (old i) (designated N i) (auxiliary N i)) G input env' (tape.1 i))
    let Z := fun i => (tape.2.1 i).1
    let X := noisyValues (fun i j => slots (aSlot c p i j))
      (fun i j => slots (residualSlot c p i j)) direct input env Q Z
    let X' := noisyValues (fun i j => slots (aSlot c p i j))
      (fun i j => slots (residualSlot c p i j)) direct input env' Q' Z
    have hQ (i : Fin n) : ‖Q i-Q' i‖ ≤ κ*D0 :=
      (freshChild_sub_le (p i) (e i) (slots ∘ childSlot c p i) (old i)
        (designated N i) (auxiliary N i) (T i) (coeff i) G input env env'
        (htable i) κ (hchild i) (tape.1 i)).trans (mul_le_mul_of_nonneg_left (hD i) hκ)
    have hX (i : Fin n) : ‖X i-X' i‖ ≤ κ*a*D0+B := by
      have h := noisyValues_sub_le (fun i j => slots (aSlot c p i j))
        (fun i j => slots (residualSlot c p i j)) direct input env env' Q Q' Z a B (κ*D0)
        (mul_nonneg hκ hD0) hrow hB hQ i
      convert h using 1
      ring
    have hi := ih batchRef (fun j => preserveDirect (direct j))
      (fun r => preserveDirect (saved r))
      (Env.prepend X (Env.prepend Z (Env.prepend Q env)))
      (Env.prepend X' (Env.prepend Z (Env.prepend Q' env'))) tape.2.2.2
      (κ*a*D0+B) (by positivity)
      (fun i => by
        rw [stored_preserveDirect env Q Z X, stored_preserveDirect env' Q' Z X']
        exact hB i)
      (fun i => by simpa only [prepend_batchRef] using hX i)
    simpa only [growth_shift,finalState,Q,Q',X,X',Z,childPoint] using hi

/-- Explicit finite sum for the actual final-state nodes. -/
theorem finalState_sub_le (N : ℕ) {Γ : Ctx}
    (old direct : Fin n → Ref Γ .point) (saved : RefMap Ξ Γ) (env env' : Env d Γ)
    (tape : Tape d (iterateThen c p slots e outer designated residual auxiliary finish N old direct saved))
    (D0 : ℝ) (hD0 : 0 ≤ D0)
    (hB : ∀ i, ‖storedPoint env (direct i)-storedPoint env' (direct i)‖ ≤ B)
    (hD : ∀ i, ‖storedPoint env (old i)-storedPoint env' (old i)‖ ≤ D0) :
    let s := finalState c p slots e outer designated residual auxiliary finish G input N old direct saved env tape
    let s' := finalState c p slots e outer designated residual auxiliary finish G input N old direct saved env' tape
    ∀ i, ‖storedPoint s.env (s.old i)-storedPoint s'.env (s'.old i)‖ ≤
      (κ*a)^N*D0 + B*∑ j ∈ Finset.range N, (κ*a)^j := by
  dsimp only
  intro i
  exact (finalState_sub_le_growth c p slots e outer designated residual auxiliary finish
    T coeff G input κ a B hκ ha hB0 htable hchild hrow N old direct saved env env' tape
    D0 hD0 hB hD i).trans (growth_le (κ*a) B D0 (mul_nonneg hκ ha) N)
end Main
end AcceleratedLogConcave.Oracle.FixedTapeStability
