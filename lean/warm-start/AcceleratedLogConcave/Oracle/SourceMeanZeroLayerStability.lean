import AcceleratedLogConcave.Oracle.FixedTapeZeroLayerStability
import AcceleratedLogConcave.Oracle.SourceMeanExecutableStability

/-! Whole-source zero-layer stability. Main carriers and privateShift stay literal,
while only active-final and private-sampler stability hypotheses are required. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Oracle.SourceMeanStability
open Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer RecursiveMeanProgram
open RecursiveMeanContinuation RetainedMeanFinalBatch FixedTapeStability
open SourceMeanExecutable SourceMeanShift CovarianceSetup
open scoped BigOperators

variable {d m n a h : ℕ}
variable (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
    (r σ Ds δ t w : ℝ) (main : Fin n → ExecutableData)
    (final : Fin m → ExecutableData) (sampling : ExecutableData)
local notation "tbl" => SourceMeanExecutable.table M nodes anchors r σ Ds δ t w main final sampling

theorem body_zero_sub_le (G : Point d → Point d) (x P : Point d)
    (κ B : ℝ) (hm : 0 < m) (hκ : 0 ≤ κ) (hB0 : 0 ≤ B)
    (hfinal : ∀ i, ChildStable (final i).program (final i).coefficient G κ)
    (env env' : Env d (MeanExecutablePrefix.readyCtx n (m+1) h [.point,.point]))
    (hP : storedPoint env (MeanExecutablePrefix.saved .here) =
      storedPoint env' (MeanExecutablePrefix.saved .here))
    (hdes : ∀ i, storedPoint env (MeanExecutablePrefix.designated i) =
      storedPoint env' (MeanExecutablePrefix.designated i))
    (hB : ∀ i, ‖storedPoint env (MeanExecutablePrefix.direct i) -
      storedPoint env' (MeanExecutablePrefix.direct i)‖ ≤ B)
    (tape : Tape d (body (a := a) (h := h) M nodes main final sampling 0)) :
    ‖childPoint (run (body (a := a) (h := h) M nodes main final sampling 0) G ⟨tbl,x,P⟩ env tape) -
      childPoint (run (body (a := a) (h := h) M nodes main final sampling 0) G ⟨tbl,x,P⟩ env' tape)‖ ≤
      κ*B := by
  apply FixedTapeStability.code_zero_sub_le
    (fun i => (main i).size) (fun i => (main i).program)
    (mainSlot (a := a) main final sampling) (fun i => (main i).enumeration)
    (fun i => (final i).size) (fun i => (final i).program) (fun i => (final i).enumeration)
    (finalSlot (a := a) main final sampling) (correctionSlot (a := a) main final sampling)
    (rhoSlot (a := a) main final sampling) (MeanExecutablePrefix.saved .here)
    MeanExecutablePrefix.designated MeanExecutablePrefix.direct (fun i => nodes.symm (.center M i))
    initialOrigin layerOrigin mainDesignated residualOrigin (mainAuxiliary main)
    finalOrigin (finalAuxiliary final)
    (fun i => childRoot (RecursiveMeanPublicTable.centerNoise r M.R Ds)
      (r*M.R) (final i).shiftVector) (fun i => (final i).coefficient)
    σ (Numerics.GaussLegendre.weight m) (fun _ => RecursiveMeanPublicTable.finalWidth M.R σ)
    G ⟨tbl,x,P⟩ κ B hκ hB0
    ?_ hfinal ?_ ?_ env env' hP hdes hB tape
  · intro i
    funext j
    exact table_final M nodes anchors r σ Ds δ t w main final sampling i j
  · funext j
    exact table_correction M nodes anchors r σ Ds δ t w main final sampling j
  · exact (MeanGeometry.sum_abs_meanOutput_weights hm).le

/-- A cached actual body may change both its host center and private position.
The private displacement premise is local; no whole-source bound is supplied. -/
private theorem cached_body_zero_sub_le (G : Point d → Point d)
    (x y P U V : Point d) (raw : Fin (m+1) → Point d) (Z : Fin h → Point d)
    (κ κs : ℝ) (hm : 0 < m) (hr : 0 ≤ r) (hκ : 0 ≤ κ) (hκs : 0 ≤ κs)
    (hpsi : M.psi ≤ M.R^4)
    (hfinal : ∀ i, ChildStable (final i).program (final i).coefficient G κ)
    (hU : ‖U-V‖ ≤ κs*‖x-y‖)
    (tape : Tape d (body (a := a) (h := h) M nodes main final sampling 0)) :
    ‖childPoint (run (body (a := a) (h := h) M nodes main final sampling 0) G ⟨tbl,x,P⟩
        (cache M nodes anchors seeds r σ Ds δ t w main final sampling x P U raw Z) tape) -
      childPoint (run (body (a := a) (h := h) M nodes main final sampling 0) G ⟨tbl,y,P⟩
        (cache M nodes anchors seeds r σ Ds δ t w main final sampling y P V raw Z) tape)‖ ≤
      κ*(1+r*(backwardEnd M.R)^2*κs)*‖x-y‖ := by
  let env : Env d (MeanExecutablePrefix.readyCtx n (m+1) h [.point,.point]) :=
    cache M nodes anchors seeds r σ Ds δ t w main final sampling x P U raw Z
  let env' : Env d (MeanExecutablePrefix.readyCtx n (m+1) h [.point,.point]) :=
    cache M nodes anchors seeds r σ Ds δ t w main final sampling y P V raw Z
  have hd (i : Fin n) : ‖storedPoint env (MeanExecutablePrefix.direct i) -
      storedPoint env' (MeanExecutablePrefix.direct i)‖ ≤
        (1+r*(backwardEnd M.R)^2*κs)*‖x-y‖ :=
    cache_direct_sub_le M nodes anchors seeds r σ Ds δ t w main final sampling
      x y P U V raw Z κs hr hpsi hU i
  have hb := body_zero_sub_le M nodes anchors r σ Ds δ t w main final sampling G x P κ
    ((1+r*(backwardEnd M.R)^2*κs)*‖x-y‖) hm hκ (by positivity) hfinal
    env env' (by simp only [env,env',cache_retained])
    (fun i => by simp only [env,env',cache_designated]) hd tape
  have hc := body_same_coefficients (h := h) M nodes anchors r σ Ds δ t w main final sampling
    0 G x P y P env' tape
  rw [← hc] at hb
  simpa only [mul_assoc] using hb

variable (privateShift : GaussianSlot sampling.program → ℝ)
    (G : Point d → Point d) (κ κs : ℝ)
    (hm : 0 < m) (hr : 0 ≤ r) (hκ : 0 ≤ κ) (hκs : 0 ≤ κs)
    (hpsi : M.psi ≤ M.R^4)
    (hfinal : ∀ i, ChildStable (final i).program (final i).coefficient G κ)
    (hs : ChildStable sampling.program sampling.coefficient G κs)
include hm hr hκ hκs hpsi hfinal hs

theorem build_zero_sub_le (P x y : Point d)
    (tape : Tape d (build M nodes anchors seeds r σ Ds δ t w main final sampling 0 privateShift).program) :
    ‖childPoint (run (build M nodes anchors seeds r σ Ds δ t w main final sampling 0 privateShift).program
        G ⟨tbl,x,P⟩ Env.empty tape) -
      childPoint (run (build M nodes anchors seeds r σ Ds δ t w main final sampling 0 privateShift).program
        G ⟨tbl,y,P⟩ Env.empty tape)‖ ≤
      κ*(1+r*(backwardEnd M.R)^2*κs)*‖x-y‖ := by
  generalize hN : (0 : ℕ) = N at tape ⊢
  let U (z : Point d) : Point d := childPoint (run (sampling.program.embed
      (prefixSlot (a := a) main final sampling ∘ PrefixPublicTable.privateSlot)
      (.there .here) .here) G ⟨tbl,z,P⟩ (inputEnv z P) (tape.2.2.1 0))
  let raw : Fin (m+1) → Point d := fun i => (tape.2.2.2.2.1 i).1
  let Z : Fin h → Point d := fun i => (tape.2.2.2.2.2.2.1 i).1
  have hU := private_sub_le M nodes anchors r σ Ds δ t w main final sampling G x y P κs hs (tape.2.2.1 0)
  have hb : ‖childPoint (run (body (a := a) (h := h) M nodes main final sampling N) G ⟨tbl,x,P⟩
        (cache M nodes anchors seeds r σ Ds δ t w main final sampling x P (U x) raw Z) tape.2.2.2.2.2.2.2.2) -
      childPoint (run (body (a := a) (h := h) M nodes main final sampling N) G ⟨tbl,y,P⟩
        (cache M nodes anchors seeds r σ Ds δ t w main final sampling y P (U y) raw Z) tape.2.2.2.2.2.2.2.2)‖ ≤
      κ*(1+r*(backwardEnd M.R)^2*κs)*‖x-y‖ := by
    subst N
    exact cached_body_zero_sub_le M nodes anchors seeds r σ Ds δ t w main final sampling
      G x y P (U x) (U y) raw Z κ κs hm hr hκ hκs hpsi hfinal hU tape.2.2.2.2.2.2.2.2
  change ‖childPoint (run (incoming M nodes anchors seeds main final sampling N) G ⟨tbl,x,P⟩
      (inputEnv x P) tape.2.2) -
    childPoint (run (incoming M nodes anchors seeds main final sampling N) G ⟨tbl,y,P⟩
      (inputEnv y P) tape.2.2)‖ ≤ _
  rw [run_incoming,run_incoming]
  simpa only [childPoint,U,raw,Z] using hb

/-- The actual source build is stable on every entering P and full residual tape. -/
theorem build_zero_childStable :
    ChildStable (build M nodes anchors seeds r σ Ds δ t w main final sampling 0 privateShift).program
      (build M nodes anchors seeds r σ Ds δ t w main final sampling 0 privateShift).coefficient G
      (κ*(1+r*(backwardEnd M.R)^2*κs)) := by
  intro P x y z rest
  have hb := build_zero_sub_le M nodes anchors seeds r σ Ds δ t w main final sampling privateShift
    G κ κs hm hr hκ hκs hpsi hfinal hs P x y (joinTape _ z rest)
  simpa only [SourceMeanExecutable.build,mul_assoc,mul_left_comm,mul_comm] using hb

end AcceleratedLogConcave.Oracle.SourceMeanStability
