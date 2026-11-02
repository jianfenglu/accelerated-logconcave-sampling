import AcceleratedLogConcave.Oracle.SourceMeanInputStability

/-! Whole-source mean stability on one actual raw tape. Private, main and final
child stability remain explicit IHs; no rank or schedule closure is asserted. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Oracle.SourceMeanStability
open Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open RetainedMeanFinalBatch FixedTapeStability SourceMeanExecutable SourceMeanShift
open scoped BigOperators

variable (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
    (r σ Ds δ t w : ℝ) (main : Fin n → ExecutableData)
    (final : Fin m → ExecutableData) (sampling : ExecutableData)
local notation "tbl" => SourceMeanExecutable.table M nodes anchors r σ Ds δ t w main final sampling

/-- Both the external center and the actual private-position anchor may vary. -/
theorem direct_sub (x y U V G0 : Point d) (ζ : Fin m → M.Kernel → Point d)
    (i : M.MeanNode) :
    M.direct r σ x (backwardEnd M.R • U) G0 ζ i -
      M.direct r σ y (backwardEnd M.R • V) G0 ζ i =
      (x-y) + ((r*M.positionCoeff i)*backwardEnd M.R) • (U-V) := by
  rw [← position_coefficient M r σ i]
  simp only [MeanGeometry.direct,Fintype.sum_sum_type,MeanGeometry.anchorValues,
    Fintype.sum_unique,MeanGeometry.positionAtom,smul_sub,smul_smul]
  abel

/-- The real stored direct vector obeys the private-child displacement estimate. -/
theorem cache_direct_sub_le (x y P U V : Point d)
    (raw : Fin (m+1) → Point d) (Z : Fin h → Point d)
    (κs : ℝ) (hr : 0 ≤ r) (hpsi : M.psi ≤ M.R^4)
    (hU : ‖U-V‖ ≤ κs*‖x-y‖) (i : Fin n) :
    ‖storedPoint (cache M nodes anchors seeds r σ Ds δ t w main final sampling x P U raw Z)
        (MeanExecutablePrefix.direct i) -
      storedPoint (cache M nodes anchors seeds r σ Ds δ t w main final sampling y P V raw Z)
        (MeanExecutablePrefix.direct i)‖ ≤ (1+r*(backwardEnd M.R)^2*κs)*‖x-y‖ := by
  rw [cache_direct,cache_direct,direct_sub]
  have hc := M.positionCoeff_mem hpsi (nodes i)
  have hb := M.backwardEnd_pos.le
  have ha : 0 ≤ (r*M.positionCoeff (nodes i))*backwardEnd M.R :=
    mul_nonneg (mul_nonneg hr hc.1) hb
  have hle : (r*M.positionCoeff (nodes i))*backwardEnd M.R ≤ r*(backwardEnd M.R)^2 := by
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc.2 hr) hb]
  calc
    _ ≤ ‖x-y‖ + ‖((r*M.positionCoeff (nodes i))*backwardEnd M.R) • (U-V)‖ := norm_add_le _ _
    _ = ‖x-y‖ + ((r*M.positionCoeff (nodes i))*backwardEnd M.R)*‖U-V‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha]
    _ ≤ ‖x-y‖ + (r*(backwardEnd M.R)^2)*(κs*‖x-y‖) := by
      exact add_le_add_right (mul_le_mul hle hU (norm_nonneg _) (by positivity)) _
    _ = _ := by ring

/-- Stability of the literal private embedded run, on its unchanged complete tape. -/
theorem private_sub_le (G : Point d → Point d) (x y P : Point d) (κs : ℝ)
    (hs : ChildStable sampling.program sampling.coefficient G κs)
    (tape : Tape d (sampling.program.embed
      (prefixSlot (a := a) main final sampling ∘ PrefixPublicTable.privateSlot)
      (.there .here) .here)) :
    ‖childPoint (run (sampling.program.embed
        (prefixSlot (a := a) main final sampling ∘ PrefixPublicTable.privateSlot)
        (.there .here) .here) G ⟨tbl,x,P⟩ (inputEnv x P) tape) -
      childPoint (run (sampling.program.embed
        (prefixSlot (a := a) main final sampling ∘ PrefixPublicTable.privateSlot)
        (.there .here) .here) G ⟨tbl,y,P⟩ (inputEnv y P) tape)‖ ≤ κs*‖x-y‖ := by
  rw [run_embed_every_tape,run_embed_every_tape]
  simp only [SourceMeanShift.private_table,inputEnv,Env.cons_here,Env.cons_there]
  exact childStable_tape sampling.program sampling.coefficient G κs hs P x y _

section Whole
variable (N : ℕ) (privateShift : GaussianSlot sampling.program → ℝ)
    (G : Point d → Point d) (κ κs A : ℝ)
    (hm : 0 < m) (hr : 0 ≤ r) (hκ : 0 ≤ κ) (hκs : 0 ≤ κs) (hA : 0 ≤ A)
    (hpsi : M.psi ≤ M.R^4)
    (hmain : ∀ i, ChildStable (main i).program (main i).coefficient G κ)
    (hfinal : ∀ i, ChildStable (final i).program (final i).coefficient G κ)
    (hs : ChildStable sampling.program sampling.coefficient G κs)
    (hrow : ∀ i : M.MeanNode, ∑ j, |M.matrix r σ i j| ≤ A)
include hm hr hκ hκs hA hpsi hmain hfinal hs hrow

/-- Actual whole-source execution, including the private run and literal prefix. -/
theorem build_sub_le (P x y : Point d)
    (tape : Tape d (build M nodes anchors seeds r σ Ds δ t w main final sampling N privateShift).program) :
    ‖childPoint (run (build M nodes anchors seeds r σ Ds δ t w main final sampling N privateShift).program
        G ⟨tbl,x,P⟩ Env.empty tape) -
      childPoint (run (build M nodes anchors seeds r σ Ds δ t w main final sampling N privateShift).program
        G ⟨tbl,y,P⟩ Env.empty tape)‖ ≤
      κ*(1+r*(backwardEnd M.R)^2*κs)*‖x-y‖*∑ j ∈ Finset.range (N+1), (κ*A)^j := by
  let U (z : Point d) : Point d := childPoint (run (sampling.program.embed
      (prefixSlot (a := a) main final sampling ∘ PrefixPublicTable.privateSlot)
      (.there .here) .here) G ⟨tbl,z,P⟩ (inputEnv z P) (tape.2.2.1 0))
  let raw : Fin (m+1) → Point d := fun i => (tape.2.2.2.2.1 i).1
  let Z : Fin h → Point d := fun i => (tape.2.2.2.2.2.2.1 i).1
  let env (z : Point d) : Env d (MeanExecutablePrefix.readyCtx n (m+1) h [.point,.point]) :=
    cache M nodes anchors seeds r σ Ds δ t w main final sampling z P (U z) raw Z
  have hU := private_sub_le M nodes anchors r σ Ds δ t w main final sampling G x y P κs hs (tape.2.2.1 0)
  have hd (i : Fin n) : ‖storedPoint (env x) (MeanExecutablePrefix.direct i) -
      storedPoint (env y) (MeanExecutablePrefix.direct i)‖ ≤
        (1+r*(backwardEnd M.R)^2*κs)*‖x-y‖ :=
    cache_direct_sub_le M nodes anchors seeds r σ Ds δ t w main final sampling
      x y P (U x) (U y) raw Z κs hr hpsi hU i
  have hb := body_sub_le M nodes anchors r σ Ds δ t w main final sampling N G x P κ A
    ((1+r*(backwardEnd M.R)^2*κs)*‖x-y‖) hm hκ hA (by positivity) hmain hfinal hrow
    (env x) (env y) (by simp only [env,cache_retained])
    (fun i => by simp only [env,cache_designated]) hd tape.2.2.2.2.2.2.2.2
  have hc := body_same_coefficients (h := h) M nodes anchors r σ Ds δ t w main final sampling
    N G x P y P (env y) tape.2.2.2.2.2.2.2.2
  rw [← hc] at hb
  change ‖childPoint (run (incoming M nodes anchors seeds main final sampling N) G ⟨tbl,x,P⟩
      (inputEnv x P) tape.2.2) -
    childPoint (run (incoming M nodes anchors seeds main final sampling N) G ⟨tbl,y,P⟩
      (inputEnv y P) tape.2.2)‖ ≤ _
  rw [run_incoming,run_incoming]
  simpa only [childPoint,env,U,raw,Z,mul_assoc] using hb

/-- The actual source build is stable on every entering P and full residual tape. -/
theorem build_childStable :
    ChildStable (build M nodes anchors seeds r σ Ds δ t w main final sampling N privateShift).program
      (build M nodes anchors seeds r σ Ds δ t w main final sampling N privateShift).coefficient G
      (κ*(1+r*(backwardEnd M.R)^2*κs)*∑ j ∈ Finset.range (N+1), (κ*A)^j) := by
  intro P x y z rest
  have hb := build_sub_le M nodes anchors seeds r σ Ds δ t w main final sampling N privateShift
    G κ κs A hm hr hκ hκs hA hpsi hmain hfinal hs hrow P x y (joinTape _ z rest)
  simpa only [SourceMeanExecutable.build,mul_assoc,mul_left_comm,mul_comm] using hb
end Whole

end AcceleratedLogConcave.Oracle.SourceMeanStability
