import AcceleratedLogConcave.Oracle.SourceMeanShift
import AcceleratedLogConcave.Oracle.SamplingReadoutStability

/-! Actual mean-body coefficient transport and specialization of the existing
finite block estimate. No prefix semantics or recursive induction is rebuilt. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Oracle.SourceMeanStability
open Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer RecursiveMeanProgram
open RecursiveMeanContinuation RetainedMeanFinalBatch FixedTapeStability
open SourceMeanExecutable SourceMeanShift CovarianceSetup
open scoped BigOperators

variable (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
    (r σ Ds δ t w : ℝ) (main : Fin n → ExecutableData)
    (final : Fin m → ExecutableData) (sampling : ExecutableData)
local notation "tbl" => SourceMeanExecutable.table M nodes anchors r σ Ds δ t w main final sampling

theorem main_table (i : Fin n) :
    tbl ∘ (mainSlot (a := a) main final sampling ∘
      childSlot (fun i => (main i).size) (fun i => (main i).program) i) =
    matrixTable (childRoot (RecursiveMeanPublicTable.centerNoise r M.R Ds)
      (M.radius r (nodes i)) (main i).shiftVector) (main i).coefficient := by
  funext j
  dsimp only [Function.comp_apply]
  erw [SourceMeanExecutable.table_main]
  exact layerTable_child (fun i => (main i).size) (fun i => (main i).program)
    (fun i j => M.matrix r σ (nodes i) (nodes j))
    (residualRoot (fun i j => M.matrix r σ (nodes i) (nodes j))
      (RecursiveMeanPublicTable.centerNoise r M.R Ds) (rowBound (m := m) r σ δ t w))
    (fun i => childRoot (RecursiveMeanPublicTable.centerNoise r M.R Ds)
      (M.radius r (nodes i)) (main i).shiftVector) (fun i => (main i).coefficient) i j

/-- At a fixed stored environment, the actual mean body ignores host x and P. -/
theorem body_same_coefficients (N : ℕ) (G : Point d → Point d) (x P y Q : Point d)
    (env : Env d (MeanExecutablePrefix.readyCtx n (m+1) h [.point,.point]))
    (tape : Tape d (body (a := a) (h := h) M nodes main final sampling N)) :
    childPoint (run (body (a := a) (h := h) M nodes main final sampling N)
      G ⟨tbl,y,Q⟩ env tape) =
    childPoint (run (body (a := a) (h := h) M nodes main final sampling N)
      G ⟨tbl,x,P⟩ env tape) := by
  dsimp only [body,NonterminalMeanBlock.code] at tape ⊢
  rw [run_initialize,run_initialize]
  apply FixedTapeSampling.iterateThen_same_coefficients
    (fun i => (main i).size) (fun i => (main i).program)
    (mainSlot (a := a) main final sampling) (fun i => (main i).enumeration)
    layerOrigin mainDesignated residualOrigin (mainAuxiliary main) _
    (fun i => childRoot (RecursiveMeanPublicTable.centerNoise r M.R Ds)
      (M.radius r (nodes i)) (main i).shiftVector) (fun i => (main i).coefficient)
    G ⟨tbl,x,P⟩ ⟨tbl,y,Q⟩ rfl
    (main_table M nodes anchors r σ Ds δ t w main final sampling)
  intro Δ old dir saved ρ tail
  have ht : tbl ∘ correctionSlot (a := a) main final sampling =
      RetainedMeanCorrection.table σ (Numerics.GaussLegendre.weight m)
        (fun _ => RecursiveMeanPublicTable.finalWidth M.R σ) := by
    funext j
    exact table_correction M nodes anchors r σ Ds δ t w main final sampling j
  rw [run_paidCorrection _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ht,
    run_paidCorrection _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ht]
  dsimp only [childPoint,pointResult]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hf : tbl ∘ finalSlot (a := a) main final sampling i =
      matrixTable (childRoot (RecursiveMeanPublicTable.centerNoise r M.R Ds)
        (r*M.R) (final i).shiftVector) (final i).coefficient := by
    funext j
    exact table_final M nodes anchors r σ Ds δ t w main final sampling i j
  rw [run_designatedChild _ _ _ _ _ _ _ _ _ _ _ hf,
    run_designatedChild _ _ _ _ _ _ _ _ _ _ _ hf]

/-- The existing initialized block bound, with literal source table and final weights. -/
theorem body_sub_le (N : ℕ) (G : Point d → Point d) (x P : Point d)
    (κ A B : ℝ) (hm : 0 < m) (hκ : 0 ≤ κ) (hA : 0 ≤ A) (hB0 : 0 ≤ B)
    (hmain : ∀ i, ChildStable (main i).program (main i).coefficient G κ)
    (hfinal : ∀ i, ChildStable (final i).program (final i).coefficient G κ)
    (hrow : ∀ i : M.MeanNode, ∑ j, |M.matrix r σ i j| ≤ A)
    (env env' : Env d (MeanExecutablePrefix.readyCtx n (m+1) h [.point,.point]))
    (hP : storedPoint env (MeanExecutablePrefix.saved .here) =
      storedPoint env' (MeanExecutablePrefix.saved .here))
    (hdes : ∀ i, storedPoint env (MeanExecutablePrefix.designated i) =
      storedPoint env' (MeanExecutablePrefix.designated i))
    (hB : ∀ i, ‖storedPoint env (MeanExecutablePrefix.direct i) -
      storedPoint env' (MeanExecutablePrefix.direct i)‖ ≤ B)
    (tape : Tape d (body (a := a) (h := h) M nodes main final sampling N)) :
    ‖childPoint (run (body (a := a) (h := h) M nodes main final sampling N) G ⟨tbl,x,P⟩ env tape) -
      childPoint (run (body (a := a) (h := h) M nodes main final sampling N) G ⟨tbl,x,P⟩ env' tape)‖ ≤
      κ*B*∑ j ∈ Finset.range (N+1), (κ*A)^j := by
  apply FixedTapeStability.code_sub_le
    (fun i => (main i).size) (fun i => (main i).program)
    (mainSlot (a := a) main final sampling) (fun i => (main i).enumeration)
    (fun i => (final i).size) (fun i => (final i).program) (fun i => (final i).enumeration)
    (finalSlot (a := a) main final sampling) (correctionSlot (a := a) main final sampling)
    (rhoSlot (a := a) main final sampling) (MeanExecutablePrefix.saved .here)
    MeanExecutablePrefix.designated MeanExecutablePrefix.direct (fun i => nodes.symm (.center M i))
    initialOrigin layerOrigin mainDesignated residualOrigin (mainAuxiliary main)
    finalOrigin (finalAuxiliary final)
    (fun i => childRoot (RecursiveMeanPublicTable.centerNoise r M.R Ds)
      (M.radius r (nodes i)) (main i).shiftVector) (fun i => (main i).coefficient)
    (fun i => childRoot (RecursiveMeanPublicTable.centerNoise r M.R Ds)
      (r*M.R) (final i).shiftVector) (fun i => (final i).coefficient)
    σ (Numerics.GaussLegendre.weight m) (fun _ => RecursiveMeanPublicTable.finalWidth M.R σ)
    G ⟨tbl,x,P⟩ κ A B hκ hA hB0
    (main_table M nodes anchors r σ Ds δ t w main final sampling) hmain
    ?_ ?_ hfinal ?_ ?_ N env env' hP hdes hB tape
  · intro i
    have he (j : Fin n) : tbl (mainSlot (a := a) main final sampling
        (aSlot (fun i => (main i).size) (fun i => (main i).program) i j)) =
        M.matrix r σ (nodes i) (nodes j) := by
      simp only [table_main,mainTable,RecursiveMeanPublicTable.sourceLayerTable,layerTable_a]
    simp only [he]
    exact (nodes.sum_comp (fun j => |M.matrix r σ (nodes i) j|)).trans_le (hrow (nodes i))
  · intro i
    funext j
    exact table_final M nodes anchors r σ Ds δ t w main final sampling i j
  · funext j
    exact table_correction M nodes anchors r σ Ds δ t w main final sampling j
  · exact (MeanGeometry.sum_abs_meanOutput_weights hm).le

end AcceleratedLogConcave.Oracle.SourceMeanStability
