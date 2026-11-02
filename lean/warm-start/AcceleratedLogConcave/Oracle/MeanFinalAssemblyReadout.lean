import AcceleratedLogConcave.Oracle.MeanFinalBatchCoupling
import AcceleratedLogConcave.Oracle.MeanAssemblyJointLaw

/-! The designated values read at the actual paid final cut are the same
incoming assembled coordinates, even after every complete main layer. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.MeanFinalAssemblyReadout
open AffineLowering TapeLowering NoisyLayer SourceMeanLayer RecursiveMeanProgram
open RecursiveMeanContinuation TailOccurrenceCut TailCut CanonicalTapeLaw
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
set_option maxHeartbeats 1200000

section Saved
variable {n C d : ℕ} {Ξ : Ctx} {τ : Ty}
  (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
  (slots : Fin (publicSize c p) → Fin C)
  (en : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
  (outer : ℕ → Origin) (designated residual : ℕ → Fin n → Origin)
  (auxiliary : ℕ → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
  (finish : ∀ {Δ : Ctx}, (Fin n → Ref Δ .point) →
    (Fin n → Ref Δ .point) → RefMap Ξ Δ → Prog C Δ τ)
  (G : Point d → Point d) (input : Inputs d C)

theorem finish_saved : ∀ (N : ℕ) {Γ : Ctx}
    (old direct : Fin n → Ref Γ .point) (saved : RefMap Ξ Γ)
    (env : Env d Γ)
    (h : Prefix d (atFinish c p slots en outer designated residual auxiliary finish N old direct saved).cut)
    (r : Ref Ξ .point),
    let f := atFinish c p slots en outer designated residual auxiliary finish N old direct saved
    storedPoint (envAt G input f.cut env h) (f.saved r) = storedPoint env (saved r) := by
  intro N
  induction N with
  | zero => intros; rfl
  | succ N ih =>
      intro Γ old direct saved env h r
      dsimp only [atFinish, envAt]
      rw [ih]
      exact stored_preserveDirect env _ _ _ (saved r)
end Saved

/-- Composition follows the same original tape, with its exact two splits. -/
theorem envAt_trans_split {c d : ℕ} {Γ Δ Ξ : Ctx} {τ σ υ : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ σ} {r : Prog c Ξ υ}
    (inner : TailCut r q) (outer : TailCut q p)
    (G : Point d → Point d) (input : Inputs d c) (env : Env d Γ) (ω : Tape d p) :
    ∀ {ty : Ty} (ref : Ref Ξ ty),
    envAt G input (trans inner outer) env (split (trans inner outer) ω).1 ref =
      envAt G input inner (envAt G input outer env (split outer ω).1)
        (split inner (split outer ω).2).1 ref := by
  induction outer with
  | here => intro ty ref; rfl
  | step o instr next cut ih => exact ih _ _
  | batch o children next cut ih => exact ih _ _

private theorem prepend_batchRef_value {d n : ℕ} {Γ : Ctx}
    (values : Fin n → Point d) (env : Env d Γ) (i : Fin n) :
    Env.prepend values env (batchRef i) = values i := prepend_batchRef values env i

section Actual
open Numerics.AffineGraph SourceMeanExecutable
variable {m n a h d : ℕ} (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
    (main : Fin n → ExecutableData) (final : Fin m → ExecutableData) (sampling : ExecutableData)
    (N : ℕ)
local notation "c" => (fun i => (main i).size)
local notation "p" => (fun i => (main i).program)
local notation "en" => (fun i => (main i).enumeration)
local notation "F" => SourceMeanExecutionRms.finish (a := a) (h := h) M nodes main final sampling
local notation "host" => SourceMeanExecutable.program M nodes anchors seeds main final sampling N
local notation "foc" => MeanFinalBatchCoupling.finishFocus M nodes anchors seeds main final sampling N
local notation "bc" => MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N

/-- Every originally cached reference survives initialization and all main
layers at the literal final cut, independently of every executed child value. -/
theorem full_saved_readout (G : Point d → Point d)
    (input : Inputs d (size (a := a) main final sampling)) (ω : Tape d host)
    (ref : Ref (SourceMeanExecutionRms.Ready n m h) .point) :
    storedPoint (envAt G input (foc).cut Env.empty (split (foc).cut ω).1) ((foc).saved ref) =
      storedPoint (envAt G input bc Env.empty (split bc ω).1) ref := by
  let f := atFinish c p (mainSlot (a := a) main final sampling) en layerOrigin
    mainDesignated residualOrigin (mainAuxiliary main) F N batchRef
    (fun i => RefMap.shiftMany n (RefMap.shiftMany n (MeanExecutablePrefix.direct i)))
    (fun q => RefMap.shiftMany n (RefMap.shiftMany n q))
  let hb : TailCut (F f.old f.direct f.saved)
      (body (a := a) (h := h) M nodes main final sampling N) := by
    unfold body NonterminalMeanBlock.code initializeCenters
    exact .batch _ _ _ (.batch _ _ _ f.cut)
  have hcut : (foc).cut = trans hb bc := by rfl
  rw [hcut]
  change envAt G input (trans hb bc) Env.empty (split (trans hb bc) ω).1 (f.saved ref) = _
  rw [envAt_trans_split]
  dsimp only [hb,envAt,split]
  change storedPoint (envAt G input f.cut _ (split f.cut (split bc ω).2.2.2).1)
    (f.saved ref) = _
  rw [finish_saved]
  simp only [MeanExecutablePrefix.stored_shiftMany]

/-- The ACTUAL final Pi readout equals the incoming literal assembly row on
the same original full tape and original retained input. -/
theorem final_designated_literal (G : Point d → Point d)
    (input : Inputs d (size (a := a) main final sampling)) (ω : Tape d host) (i : Fin m) :
    storedPoint (envAt G input (foc).cut Env.empty (split (foc).cut ω).1)
      ((foc).saved (MeanExecutablePrefix.designated i)) =
    MeanExecutablePrefix.assemblyValues
      (prefixSlot (a := a) main final sampling ∘ PrefixPublicTable.assemblySlot) input
      input.momentum (MeanAssemblyJointLaw.raw M nodes anchors seeds main final sampling N ω) i.succ := by
  rw [full_saved_readout]
  change storedPoint (Env.prepend _ (Env.prepend _ (Env.prepend _ (Env.prepend _
    (Env.prepend _ (Env.prepend _ ((Env.cons (τ := .point) input.momentum (Env.cons (τ := .point) input.center Env.empty)))))))))
    (MeanExecutablePrefix.designated i) = _
  simp only [MeanExecutablePrefix.designated,storedPoint]
  erw [prepend_shiftMany,prepend_shiftMany]
  erw [prepend_batchRef_value]
  erw [MeanExecutablePrefix.run_assemblyRow]
  rfl

/-- Identification with the concrete Gaussian assembly at the actual source
public table. All originalP/reconstruction correlations remain intact. -/
theorem final_designated_assembled (G : Point d → Point d) (r σ Ds δ t w : ℝ)
    (x P : Point d) (ω : Tape d host) (i : Fin m) :
    storedPoint (envAt G
      (⟨table M nodes anchors r σ Ds δ t w main final sampling,x,P⟩ : Inputs d _)
      (foc).cut Env.empty (split (foc).cut ω).1)
      ((foc).saved (MeanExecutablePrefix.designated i)) =
    MeanAssemblyJointLaw.assembled M nodes anchors seeds main final sampling N (P,ω) (some i.succ) := by
  rw [final_designated_literal]
  rw [MeanExecutablePrefix.assemblyValues_eq_active
    (assembly M) (MeanAssemblyJointLaw.assembly_mass M)]
  · rfl
  · funext j
    simp only [Function.comp_apply, table_prefix, PrefixPublicTable.table_assembly]
end Actual

end AcceleratedLogConcave.Oracle.MeanFinalAssemblyReadout
