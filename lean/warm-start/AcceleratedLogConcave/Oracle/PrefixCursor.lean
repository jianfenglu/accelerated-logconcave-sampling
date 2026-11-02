import AcceleratedLogConcave.Oracle.MeanExecutionSchedule

/-! A deterministic cursor through the existing loop. It retains the original
suffix and reads only completed layers. Reconstructed locally because the
receiving checkpoint does not contain its pinned PrefixCursor source. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Oracle.RecursiveMeanContinuation
open AffineLowering TapeLowering NoisyLayer RecursiveMeanProgram SourceMeanLayer
open scoped BigOperators

variable (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
  (slots : Fin (publicSize c p) → Fin C)
  (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
  (outer : ℕ → Origin) (designated residual : ℕ → Fin n → Origin)
  (auxiliary : ℕ → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
  (finish : ∀ {Δ : Ctx}, (Fin n → Ref Δ .point) →
    (Fin n → Ref Δ .point) → RefMap Ξ Δ → Prog C Δ τ)

structure PrefixState (d : ℕ) where
  remaining : ℕ
  ctx : Ctx
  old : Fin n → Ref ctx .point
  direct : Fin n → Ref ctx .point
  saved : RefMap Ξ ctx
  env : Env d ctx
  tape : Tape d (iterateThen c p slots e outer designated residual auxiliary finish remaining old direct saved)

def prefixCursor (G : Point d → Point d) (input : Inputs d C) :
    (N k : ℕ) → {Γ : Ctx} → (old direct : Fin n → Ref Γ .point) →
    (saved : RefMap Ξ Γ) → Env d Γ →
    Tape d (iterateThen c p slots e outer designated residual auxiliary finish N old direct saved) →
    PrefixState c p slots e outer designated residual auxiliary finish d
  | N, 0, Γ, old, direct, saved, env, tape => ⟨N,Γ,old,direct,saved,env,tape⟩
  | 0, _+1, Γ, old, direct, saved, env, tape => ⟨0,Γ,old,direct,saved,env,tape⟩
  | N+1, k+1, _, old, direct, saved, env, tape =>
      let Q := fun i => (run (freshChild (p i) (e i) (slots ∘ childSlot c p i)
        (old i) (designated N i) (auxiliary N i)) G input env (tape.1 i)).value
      let Z := fun i => (tape.2.1 i).1
      let X := noisyValues (fun j l => slots (aSlot c p j l))
        (fun j l => slots (residualSlot c p j l)) direct input env Q Z
      prefixCursor G input N k batchRef (fun j => preserveDirect (direct j))
        (fun q => preserveDirect (saved q))
        (Env.prepend X (Env.prepend Z (Env.prepend Q env))) tape.2.2.2

end AcceleratedLogConcave.Oracle.RecursiveMeanContinuation

namespace AcceleratedLogConcave.Oracle.MeanExecutionSchedule
open AffineLowering TapeLowering NoisyLayer RecursiveMeanProgram
open RecursiveMeanContinuation SourceMeanLayer Numerics RetainedMeanFinalBatch FixedTapeStability
open scoped BigOperators

variable (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
  (finish : ∀ {Δ : Ctx}, (Fin n → Ref Δ .point) →
    (Fin n → Ref Δ .point) → RefMap Ξ Δ → Prog C Δ τ)
  (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
  (T : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Fin (tapeShape (p i)).gaussianBlocks → ℝ)
  (coeff : ∀ i, Fin (c i) → ℝ) (G : Point d → Point d)

def prefixFold (A R : Fin n → Fin n → ℝ) : (N k : ℕ) → {Γ : Ctx} →
    {old direct : Fin n → Ref Γ .point} → {saved : RefMap Ξ Γ} →
    RawData c p finish d N old direct saved →
    (Fin n → Point d) → (Fin n → Point d) → Fin n → Point d
  | _, 0, _, _, _, _, _, _, initial => initial
  | 0, _+1, _, _, _, _, _, _, initial => initial
  | N+1, k+1, _, _, _, _, data, b, initial =>
      prefixFold A R N k data.2 b (SharedLayerRms.layer b A R
        (fun i => sourceValue c p e T coeff G data.1 i (initial i)) data.1.2)

theorem prefixFold_eq_iterate {Ω : Type*} (A R : Fin n → Fin n → ℝ)
    (N k : ℕ) (hk : k ≤ N) {Γ : Ctx}
    {old direct : Fin n → Ref Γ .point} {saved : RefMap Ξ Γ}
    (data : Ω → RawData c p finish d N old direct saved)
    (b initial U : Fin n → Ω → Point d) :
    (fun i ω => prefixFold c p finish e T coeff G A R N k (data ω)
      (fun j => b j ω) (fun j => initial j ω) i) =
      SharedLayerRms.iterate b A R (evaluator c p finish e T coeff G N data U)
        (residualNoise c p finish N data) initial k := by
  induction k generalizing N Γ b initial U with
  | zero => cases N <;> rfl
  | succ k ih =>
      cases N with
      | zero => omega
      | succ N =>
          rw [iterate_tail]
          exact ih N (by omega) (fun ω => (data ω).2) b
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
/-- Literal entering-state readout, proved from the freshChild interpreter equation.
The RHS is not supplied as a parent execution-correctness assumption. -/
theorem prefixCursor_raw_old (N k : ℕ) (hk : k ≤ N) {Γ : Ctx}
    (old direct : Fin n → Ref Γ .point) (saved : RefMap Ξ Γ)
    (env : Env d Γ) (data : RawData c p finish d N old direct saved) :
    let st := prefixCursor c p slots e outer designated residual auxiliary finish G input
      N k old direct saved env
      ((rawTapeEquiv c p slots e outer designated residual auxiliary finish d N old direct saved).symm data)
    ∀ i, storedPoint st.env (st.old i) =
      prefixFold c p finish e T coeff G A R N k data
        (fun j => storedPoint env (direct j)) (fun j => storedPoint env (old j)) i := by
  dsimp only
  induction k generalizing N Γ with
  | zero => intro i; cases N <;> rfl
  | succ k ih =>
    cases N with
    | zero => omega
    | succ N =>
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
      have hi := ih N (by omega) batchRef (fun j => preserveDirect (direct j))
        (fun r => preserveDirect (saved r))
        (Env.prepend X (Env.prepend data.1.2 (Env.prepend Q env))) data.2
      simp only [stored_preserveDirect,prepend_batchRef] at hi
      -- The inverse raw equivalence reduces to the existing layer packer.
      change (let st := (prefixCursor c p slots e outer designated residual auxiliary finish G input N k
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
          prefixFold c p finish e T coeff G A R N k data.2
            (fun j => storedPoint env (direct j)) X i)
      rw [funext hq, hx]
      exact hi
  
end Interpreter
end AcceleratedLogConcave.Oracle.MeanExecutionSchedule
