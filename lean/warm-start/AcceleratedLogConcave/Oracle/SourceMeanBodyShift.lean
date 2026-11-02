import AcceleratedLogConcave.Oracle.SourceMeanShift
import AcceleratedLogConcave.Oracle.MeanBlockShift

/-! The actual source mean's initialized synchronous body preserves its complete
Result under the calculated child shifts. Source routing and active-center
invariance are proved from the constructed graph and public table. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.SourceMeanBodyShift
open Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open ChildAbsorption CovarianceSetup LayerShift ExecutableShiftWeights
open SourceMeanExecutable SourceMeanShift

variable (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
    (r σ Ds δ t w : ℝ) (main : Fin n → ExecutableData) (final : Fin m → ExecutableData)
    (sampling : ExecutableData)

def config (layers : ℕ) :
    MeanBlockShift.Config n m (SourceMeanExecutable.size (a := a) main final sampling)
      (fun i => (main i).size) (fun i => (final i).size)
      (fun i => (main i).program) (fun i => (final i).program) where
  mainSlots := mainSlot (a := a) main final sampling
  mainEquiv i := (main i).enumeration
  finalSlots := finalSlot (a := a) main final sampling
  finalEquiv i := (final i).enumeration
  correctionSlots := correctionSlot (a := a) main final sampling
  noise := rhoSlot (a := a) main final sampling
  active i := nodes.symm (.center M i)
  initialOrigin := initialOrigin
  layerOrigin := layerOrigin
  mainDesignated := mainDesignated
  mainResidual := residualOrigin
  mainAuxiliary := mainAuxiliary main
  finalOrigin := finalOrigin
  finalAuxiliary := finalAuxiliary final
  layers := layers

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem translation (layers : ℕ) (hr : 0 < r)
    (hm : ∀ i, Admissible (RecursiveMeanPublicTable.centerNoise r M.R Ds)
      (M.radius r (nodes i)) Ds (main i).shiftVector)
    (hsm : ∀ i, QueryShift (main i).program (main i).enumeration
      (main i).coefficient (M.radius r (nodes i)) (main i).shiftVector)
    (G : Point d → Point d) (x P Δ : Point d)
    (env env' : Env d (MeanExecutablePrefix.readyCtx n (m+1) h [.point,.point]))
    (hdir : ∀ i, storedPoint env' (MeanExecutablePrefix.direct i) =
      storedPoint env (MeanExecutablePrefix.direct i) + centerShift M nodes r σ i • Δ)
    (hP : storedPoint env' (MeanExecutablePrefix.saved (.here : Ref [.point,.point] .point)) =
      storedPoint env (MeanExecutablePrefix.saved (.here : Ref [.point,.point] .point)))
    (hdes : ∀ i : Fin m, storedPoint env' (MeanExecutablePrefix.designated i) =
      storedPoint env (MeanExecutablePrefix.designated i))
    (tape : Tape d (body (a := a) (h := h) M nodes main final sampling layers)) :
    let coeff := SourceMeanExecutable.table M nodes anchors r σ Ds δ t w main final sampling
    run (body (a := a) (h := h) M nodes main final sampling layers) G ⟨coeff,x+Δ,P⟩ env'
      (translate (body (a := a) (h := h) M nodes main final sampling layers)
        (bodyShift M nodes r σ Ds main final sampling layers) r Δ tape) =
    run (body (a := a) (h := h) M nodes main final sampling layers) G ⟨coeff,x,P⟩ env tape := by
  let coeff := SourceMeanExecutable.table M nodes anchors r σ Ds δ t w main final sampling
  have htm (i : Fin n) : coeff ∘ (mainSlot (a := a) main final sampling ∘
      childSlot (fun i => (main i).size) (fun i => (main i).program) i) =
      matrixTable (childRoot (RecursiveMeanPublicTable.centerNoise r M.R Ds)
        (M.radius r (nodes i)) (main i).shiftVector) (main i).coefficient := by
    funext j
    dsimp only [Function.comp_apply, coeff]
    erw [SourceMeanExecutable.table_main]
    exact layerTable_child (fun i => (main i).size) (fun i => (main i).program)
      (fun i j => M.matrix r σ (nodes i) (nodes j))
      (residualRoot (fun i j => M.matrix r σ (nodes i) (nodes j))
        (RecursiveMeanPublicTable.centerNoise r M.R Ds) (rowBound (m := m) r σ δ t w))
      (fun i => childRoot (RecursiveMeanPublicTable.centerNoise r M.R Ds)
        (M.radius r (nodes i)) (main i).shiftVector) (fun i => (main i).coefficient) i j
  have htc : coeff ∘ correctionSlot (a := a) main final sampling =
      RetainedMeanCorrection.table σ (Numerics.GaussLegendre.weight m)
        (fun _ => RecursiveMeanPublicTable.finalWidth M.R σ) := by
    funext j
    exact SourceMeanExecutable.table_correction M nodes anchors r σ Ds δ t w main final sampling j
  exact MeanBlockShift.translation (config (a := a) M nodes main final sampling layers)
    (MeanExecutablePrefix.saved .here) MeanExecutablePrefix.designated MeanExecutablePrefix.direct
    (RecursiveMeanPublicTable.centerNoise r M.R Ds) r Ds
    (fun i => M.radius r (nodes i)) (centerShift M nodes r σ)
    (fun i => (main i).shiftVector) (fun i => (main i).coefficient) hm hr hsm
    σ (Numerics.GaussLegendre.weight m) (fun _ => RecursiveMeanPublicTable.finalWidth M.R σ)
    G ⟨coeff,x,P⟩ ⟨coeff,x+Δ,P⟩ rfl Δ htm htc (centerShift_active M nodes r σ hr)
    env env' hdir hP hdes tape

end AcceleratedLogConcave.Oracle.SourceMeanBodyShift
