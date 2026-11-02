import AcceleratedLogConcave.Oracle.RecursiveMeanOperational
import AcceleratedLogConcave.Oracle.FixedTapeChildStability
import AcceleratedLogConcave.Numerics.SharedLayerRms

/-! Chronological numerical adapter for the literal complete main-loop tape.
No fresh tape, product law, or independence is introduced. Outside the finite
execution the evaluator is the constant benchmark U, not zero: this makes its
benchmark error zero without requiring an absolute-state L2 hypothesis. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Oracle.MeanExecutionSchedule
open AffineLowering TapeLowering NoisyLayer RecursiveMeanProgram
open RecursiveMeanContinuation RetainedMeanFinalBatch FixedTapeStability SourceMeanLayer
open Numerics
open scoped BigOperators NNReal

variable (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
  (finish : ∀ {Δ : Ctx}, (Fin n → Ref Δ .point) →
    (Fin n → Ref Δ .point) → RefMap Ξ Δ → Prog C Δ τ)

/-- Index zero is the first executed layer, whose origin is N-1, not zero. -/
def inputAt : (N : ℕ) → {Γ : Ctx} →
    {old direct : Fin n → Ref Γ .point} → {saved : RefMap Ξ Γ} →
    RawData c p finish d N old direct saved → ℕ → Option (LayerInputs c p d)
  | 0, _, _, _, _, _, _ => none
  | _+1, _, _, _, _, data, 0 => some data.1
  | N+1, _, _, _, _, data, k+1 => inputAt N data.2 k

/-- Exactly the source program embedded by freshChild, including its designated
momentum, transformed Gaussian coordinates, and every residual/uniform slot. -/
def sourceValue
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (T : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (coeff : ∀ i, Fin (c i) → ℝ) (G : Point d → Point d)
    (data : LayerInputs c p d) (i : Fin n) (x : Point d) : Point d :=
  childPoint (run (p i) G ⟨coeff i,x,(data.1 i).1⟩ Env.empty
    (transformedSourceTape (p i) (e i) (T i) (data.1 i).2.1 (data.1 i).2.2))

variable (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (T : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (coeff : ∀ i, Fin (c i) → ℝ) (G : Point d → Point d)

/-- The sample may be the whole body tape, or any common space carrying it. -/
def evaluator {Ω : Type*} (N : ℕ) {old direct : Fin n → Ref Γ .point}
    {saved : RefMap Ξ Γ} (data : Ω → RawData c p finish d N old direct saved)
    (U : Fin n → Ω → Point d) (k : ℕ) (i : Fin n) (ω : Ω) (x : Point d) : Point d :=
  match inputAt c p finish N (data ω) k with
  | some v => sourceValue c p e T coeff G v i x
  | none => U i ω

def residualNoise {Ω : Type*} (N : ℕ) {old direct : Fin n → Ref Γ .point}
    {saved : RefMap Ξ Γ} (data : Ω → RawData c p finish d N old direct saved)
    (k : ℕ) (i : Fin n) (ω : Ω) : Point d :=
  match inputAt c p finish N (data ω) k with
  | some v => v.2 i
  | none => 0

/-- The exact entering designated momentum, shared by actual and benchmark calls. -/
def designatedNoise {Ω : Type*} (N : ℕ) {old direct : Fin n → Ref Γ .point}
    {saved : RefMap Ξ Γ} (data : Ω → RawData c p finish d N old direct saved)
    (k : ℕ) (i : Fin n) (ω : Ω) : Point d :=
  match inputAt c p finish N (data ω) k with
  | some v => (v.1 i).1
  | none => 0

theorem inputAt_none (N : ℕ) {Γ : Ctx} {old direct : Fin n → Ref Γ .point}
    {saved : RefMap Ξ Γ} (data : RawData c p finish d N old direct saved)
    (k : ℕ) (hk : N ≤ k) : inputAt c p finish N data k = none := by
  induction N generalizing Γ k with
  | zero => rfl
  | succ N ih =>
    cases k with
    | zero => omega
    | succ k => exact ih data.2 k (by omega)

/-- Use the actual child IH, rather than assume stability of an abstract M. -/
theorem evaluator_lipschitz {Ω : Type*} (N : ℕ)
    {old direct : Fin n → Ref Γ .point} {saved : RefMap Ξ Γ}
    (data : Ω → RawData c p finish d N old direct saved) (U : Fin n → Ω → Point d)
    (κ : ℝ≥0) (hchild : ∀ i, ChildStable (p i) (coeff i) G κ)
    (k : ℕ) (i : Fin n) (ω : Ω) :
    LipschitzWith κ (evaluator c p finish e T coeff G N data U k i ω) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm]
  unfold evaluator
  cases inputAt c p finish N (data ω) k with
  | none => simp only [sub_self,norm_zero]; positivity
  | some v => exact childStable_tape (p i) (coeff i) G κ (hchild i) _ x y _

/-- Direct numerical fold of the extracted execution schedule. -/
def fold (A R : Fin n → Fin n → ℝ) : (N : ℕ) → {Γ : Ctx} →
    {old direct : Fin n → Ref Γ .point} → {saved : RefMap Ξ Γ} →
    RawData c p finish d N old direct saved →
    (Fin n → Point d) → (Fin n → Point d) → Fin n → Point d
  | 0, _, _, _, _, _, _, initial => initial
  | N+1, _, _, _, _, data, b, initial =>
      fold A R N data.2 b (SharedLayerRms.layer b A R
        (fun i => sourceValue c p e T coeff G data.1 i (initial i)) data.1.2)

/-- A shift of the chronological schedule, not a reversal of the origin labels. -/
theorem iterate_tail {ι Ω E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : ι → Ω → E) (A R : ι → ι → ℝ)
    (M : ℕ → ι → Ω → E → E) (Z : ℕ → ι → Ω → E) (initial : ι → Ω → E)
    (N : ℕ) :
    SharedLayerRms.iterate b A R M Z initial (N+1) =
      SharedLayerRms.iterate b A R (fun k => M (k+1)) (fun k => Z (k+1))
        (SharedLayerRms.iterate b A R M Z initial 1) N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    conv_lhs => rw [SharedLayerRms.iterate]
    conv_rhs => rw [SharedLayerRms.iterate]
    rw [ih]

/-- The stored numerical fold is exactly the pre-existing RMS numerical iterate. -/
theorem fold_eq_iterate {Ω : Type*} (A R : Fin n → Fin n → ℝ)
    (N : ℕ) {Γ : Ctx} {old direct : Fin n → Ref Γ .point} {saved : RefMap Ξ Γ}
    (data : Ω → RawData c p finish d N old direct saved)
    (b initial U : Fin n → Ω → Point d) :
    (fun i ω => fold c p finish e T coeff G A R N (data ω)
      (fun j => b j ω) (fun j => initial j ω) i) =
      SharedLayerRms.iterate b A R
        (evaluator c p finish e T coeff G N data U)
        (residualNoise c p finish N data) initial N := by
  induction N generalizing Γ b initial U with
  | zero => rfl
  | succ N ih =>
    rw [iterate_tail]
    exact ih (fun ω => (data ω).2) b
        (fun i ω => SharedLayerRms.layer (fun j => b j ω) A R
          (fun j => sourceValue c p e T coeff G (data ω).1 j (initial j ω))
          (data ω).1.2 i) U

section Interpreter
variable (slots : Fin (publicSize c p) → Fin C)
    (outer : ℕ → Origin) (designated residual : ℕ → Fin n → Origin)
    (auxiliary : ℕ → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (A R : Fin n → Fin n → ℝ) (input : Inputs d C)
    (htable : input.coefficient ∘ slots = layerTable c p A R T coeff)

include htable in
/-- Literal finalState readout, proved from the freshChild interpreter equation.
The RHS is not supplied as a parent execution-correctness assumption. -/
theorem finalState_raw_old (N : ℕ) {Γ : Ctx}
    (old direct : Fin n → Ref Γ .point) (saved : RefMap Ξ Γ)
    (env : Env d Γ) (data : RawData c p finish d N old direct saved) :
    let st := finalState c p slots e outer designated residual auxiliary finish G input
      N old direct saved env
      ((rawTapeEquiv c p slots e outer designated residual auxiliary finish d N old direct saved).symm data)
    ∀ i, storedPoint st.env (st.old i) =
      fold c p finish e T coeff G A R N data
        (fun j => storedPoint env (direct j)) (fun j => storedPoint env (old j)) i := by
  dsimp only
  induction N generalizing Γ with
  | zero => intro i; rfl
  | succ N ih =>
    dsimp only [RawData] at data
    let Q := fun i => sourceValue c p e T coeff G data.1 i (storedPoint env (old i))
    let X := SharedLayerRms.layer (fun j => storedPoint env (direct j)) A R Q data.1.2
    have hq (i : Fin n) :
        childPoint (run (freshChild (p i) (e i) (slots ∘ childSlot c p i)
          (old i) (designated N i) (auxiliary N i)) G input env
          ((freshChildTapeEquiv (p i) (e i) (slots ∘ childSlot c p i)
            (old i) (designated N i) (auxiliary N i)).symm (data.1.1 i))) = Q i := by
      rw [run_freshChild (p i) (e i) (slots ∘ childSlot c p i) (old i)
        (designated N i) (auxiliary N i) (T i) (coeff i) G input env
        (funext fun j => (congrFun htable (childSlot c p i j)).trans
          (layerTable_child c p A R T coeff i j))]
      simp only [Equiv.apply_symm_apply,sourceValue,Q,childPoint]
    have hx : noisyValues (fun i j => slots (aSlot c p i j))
        (fun i j => slots (residualSlot c p i j)) direct input env Q data.1.2 = X := by
      funext i
      have ha (j : Fin n) := (congrFun htable (aSlot c p i j)).trans
        (layerTable_a c p A R T coeff i j)
      have hr (j : Fin n) := (congrFun htable (residualSlot c p i j)).trans
        (layerTable_residual c p A R T coeff i j)
      simp only [Function.comp_apply] at ha hr
      simp only [noisyValues,ha,hr,X,SharedLayerRms.layer]
    have hi := ih batchRef (fun j => preserveDirect (direct j))
      (fun r => preserveDirect (saved r))
      (Env.prepend X (Env.prepend data.1.2 (Env.prepend Q env))) data.2
    simp only [stored_preserveDirect,prepend_batchRef] at hi
    -- The inverse raw equivalence reduces to the existing layer packer.
    change (let st := (finalState c p slots e outer designated residual auxiliary finish G input N
        batchRef (fun j => preserveDirect (direct j)) (fun r => preserveDirect (saved r))
        (Env.prepend
          (noisyValues (fun i j => slots (aSlot c p i j))
            (fun i j => slots (residualSlot c p i j)) direct input env
            (fun i => childPoint (run (freshChild (p i) (e i) (slots ∘ childSlot c p i)
              (old i) (designated N i) (auxiliary N i)) G input env
              ((freshChildTapeEquiv (p i) (e i) (slots ∘ childSlot c p i)
                (old i) (designated N i) (auxiliary N i)).symm (data.1.1 i)))) data.1.2)
          (Env.prepend data.1.2 (Env.prepend
            (fun i => childPoint (run (freshChild (p i) (e i) (slots ∘ childSlot c p i)
              (old i) (designated N i) (auxiliary N i)) G input env
              ((freshChildTapeEquiv (p i) (e i) (slots ∘ childSlot c p i)
                (old i) (designated N i) (auxiliary N i)).symm (data.1.1 i)))) env)))
        ((rawTapeEquiv c p slots e outer designated residual auxiliary finish d N
          batchRef (fun j => preserveDirect (direct j))
          (fun r => preserveDirect (saved r))).symm data.2));
      ∀ i, storedPoint st.env (st.old i) =
        fold c p finish e T coeff G A R N data.2
          (fun j => storedPoint env (direct j)) X i)
    rw [funext hq, hx]
    exact hi

end Interpreter
end AcceleratedLogConcave.Oracle.MeanExecutionSchedule
