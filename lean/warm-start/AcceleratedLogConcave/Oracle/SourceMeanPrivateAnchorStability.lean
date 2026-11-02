import AcceleratedLogConcave.Oracle.SourceMeanZeroLayerStability

/-! Private-anchor replacement in the literal source body. 
not compiler-checked here. The external center, original retained momentum,
assembly/flow arrays and COMPLETE body tape are identical on both sides.
This is propagation, not private accuracy or an execution/reference coupling. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Oracle.SourceMeanPrivateAnchorStability
open Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open RetainedMeanFinalBatch FixedTapeStability SourceMeanExecutable SourceMeanShift
open SourceMeanStability
open scoped BigOperators

variable {d m n a h : ℕ}
variable (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
    (r σ Ds δ t w : ℝ) (main : Fin n → ExecutableData)
    (final : Fin m → ExecutableData) (sampling : ExecutableData)
local notation "tbl" => SourceMeanExecutable.table M nodes anchors r σ Ds δ t w main final sampling

/-- Only notation for the actual body, not a replacement compiler. -/
def output (N : ℕ) (G : Point d → Point d) (x P U : Point d)
    (raw : Fin (m+1) → Point d) (Z : Fin h → Point d)
    (τ : Tape d (body (a := a) (h := h) M nodes main final sampling N)) : Point d :=
  childPoint (run (body (a := a) (h := h) M nodes main final sampling N) G ⟨tbl,x,P⟩
    (cache M nodes anchors seeds r σ Ds δ t w main final sampling x P U raw Z) τ)

/-- There are two factors of b: the literal U ↦ bU cache scaling and
positionCoeff ≤ b. No replacement of source r, σ or any child width occurs. -/
theorem cache_direct_private_sub_le (x P U V : Point d)
    (raw : Fin (m+1) → Point d) (Z : Fin h → Point d)
    (hr : 0 ≤ r) (hpsi : M.psi ≤ M.R^4) (i : Fin n) :
    ‖storedPoint (cache M nodes anchors seeds r σ Ds δ t w main final sampling x P U raw Z)
        (MeanExecutablePrefix.direct i) -
      storedPoint (cache M nodes anchors seeds r σ Ds δ t w main final sampling x P V raw Z)
        (MeanExecutablePrefix.direct i)‖ ≤ r*(backwardEnd M.R)^2*‖U-V‖ := by
  rw [cache_direct, cache_direct, direct_sub, sub_self, zero_add]
  have hc := M.positionCoeff_mem hpsi (nodes i)
  have hb := M.backwardEnd_pos.le
  have ha : 0 ≤ (r*M.positionCoeff (nodes i))*backwardEnd M.R :=
    mul_nonneg (mul_nonneg hr hc.1) hb
  have hle : (r*M.positionCoeff (nodes i))*backwardEnd M.R ≤ r*(backwardEnd M.R)^2 := by
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc.2 hr) hb]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
  exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)

/-- Explicit finite coefficient. No schedule-smallness is claimed. -/
def coefficient (N : ℕ) (κ A : ℝ) : ℝ :=
  κ*r*(backwardEnd M.R)^2 * ∑ j ∈ Finset.range (N+1), (κ*A)^j

theorem coefficient_nonneg (N : ℕ) (κ A : ℝ)
    (hr : 0 ≤ r) (hκ : 0 ≤ κ) (hA : 0 ≤ A) :
    0 ≤ coefficient M r N κ A := by
  unfold coefficient
  positivity

/-- Arbitrary anchors, with literally unchanged outer coordinates and tail. -/
theorem output_sub_le (N : ℕ) (G : Point d → Point d) (κ A : ℝ)
    (hm : 0 < m) (hr : 0 ≤ r) (hκ : 0 ≤ κ) (hA : 0 ≤ A)
    (hpsi : M.psi ≤ M.R^4)
    (hmain : ∀ i, ChildStable (main i).program (main i).coefficient G κ)
    (hfinal : ∀ i, ChildStable (final i).program (final i).coefficient G κ)
    (hrow : ∀ i : M.MeanNode, ∑ j, |M.matrix r σ i j| ≤ A)
    (x P U V : Point d) (raw : Fin (m+1) → Point d) (Z : Fin h → Point d)
    (τ : Tape d (body (a := a) (h := h) M nodes main final sampling N)) :
    ‖output M nodes anchors seeds r σ Ds δ t w main final sampling N G x P U raw Z τ -
      output M nodes anchors seeds r σ Ds δ t w main final sampling N G x P V raw Z τ‖ ≤
      coefficient M r N κ A * ‖U-V‖ := by
  have hb := body_sub_le M nodes anchors r σ Ds δ t w main final sampling N G x P κ A
    (r*(backwardEnd M.R)^2*‖U-V‖) hm hκ hA (by positivity) hmain hfinal hrow
    (cache M nodes anchors seeds r σ Ds δ t w main final sampling x P U raw Z)
    (cache M nodes anchors seeds r σ Ds δ t w main final sampling x P V raw Z)
    (by simp only [cache_retained]) (fun i => by simp only [cache_designated])
    (cache_direct_private_sub_le M nodes anchors seeds r σ Ds δ t w main final sampling
      x P U V raw Z hr hpsi) τ
  simpa only [output, coefficient, mul_assoc, mul_left_comm, mul_comm] using hb

/-- Zero layers need final children only; no unused main or private-child IH. -/
theorem output_zero_sub_le (G : Point d → Point d) (κ : ℝ)
    (hm : 0 < m) (hr : 0 ≤ r) (hκ : 0 ≤ κ) (hpsi : M.psi ≤ M.R^4)
    (hfinal : ∀ i, ChildStable (final i).program (final i).coefficient G κ)
    (x P U V : Point d) (raw : Fin (m+1) → Point d) (Z : Fin h → Point d)
    (τ : Tape d (body (a := a) (h := h) M nodes main final sampling 0)) :
    ‖output M nodes anchors seeds r σ Ds δ t w main final sampling 0 G x P U raw Z τ -
      output M nodes anchors seeds r σ Ds δ t w main final sampling 0 G x P V raw Z τ‖ ≤
      (κ*r*(backwardEnd M.R)^2) * ‖U-V‖ := by
  have hb := body_zero_sub_le M nodes anchors r σ Ds δ t w main final sampling G x P κ
    (r*(backwardEnd M.R)^2*‖U-V‖) hm hκ (by positivity) hfinal
    (cache M nodes anchors seeds r σ Ds δ t w main final sampling x P U raw Z)
    (cache M nodes anchors seeds r σ Ds δ t w main final sampling x P V raw Z)
    (by simp only [cache_retained]) (fun i => by simp only [cache_designated])
    (cache_direct_private_sub_le M nodes anchors seeds r σ Ds δ t w main final sampling
      x P U V raw Z hr hpsi) τ
  simpa only [output, mul_assoc] using hb

/-- The actual incoming execution is precisely output at its actual private result.
The assembly, flow and entire body tail are projections of the SAME incoming tape. -/
theorem incoming_eq_output (N : ℕ) (G : Point d → Point d) (x P : Point d)
    (τ : Tape d (incoming M nodes anchors seeds main final sampling N)) :
    childPoint (run (incoming M nodes anchors seeds main final sampling N) G ⟨tbl,x,P⟩
      (inputEnv x P) τ) =
    output M nodes anchors seeds r σ Ds δ t w main final sampling N G x P
      (childPoint (run (sampling.program.embed
        (prefixSlot (a := a) main final sampling ∘ PrefixPublicTable.privateSlot)
        (.there .here) .here) G ⟨tbl,x,P⟩ (inputEnv x P) (τ.1 0)))
      (fun i => (τ.2.2.1 i).1) (fun i => (τ.2.2.2.2.1 i).1) τ.2.2.2.2.2.2 := by
  rw [run_incoming]
  rfl

/-- The full build, including its two input instructions, is the same output.
The privateShift stays in the literal build and is not changed or normalized. -/
theorem build_eq_output (N : ℕ) (privateShift : GaussianSlot sampling.program → ℝ)
    (G : Point d → Point d) (x P : Point d)
    (τ : Tape d (build M nodes anchors seeds r σ Ds δ t w main final sampling N privateShift).program) :
    childPoint (run (build M nodes anchors seeds r σ Ds δ t w main final sampling N privateShift).program
      G ⟨tbl,x,P⟩ Env.empty τ) =
    output M nodes anchors seeds r σ Ds δ t w main final sampling N G x P
      (childPoint (run (sampling.program.embed
        (prefixSlot (a := a) main final sampling ∘ PrefixPublicTable.privateSlot)
        (.there .here) .here) G ⟨tbl,x,P⟩ (inputEnv x P) (τ.2.2.1 0)))
      (fun i => (τ.2.2.2.2.1 i).1) (fun i => (τ.2.2.2.2.2.2.1 i).1)
      τ.2.2.2.2.2.2.2.2 := by
  change childPoint (run (incoming M nodes anchors seeds main final sampling N)
    G ⟨tbl,x,P⟩ (inputEnv x P) τ.2.2) = _
  exact incoming_eq_output M nodes anchors seeds r σ Ds δ t w main final sampling N G x P τ.2.2

end AcceleratedLogConcave.Oracle.SourceMeanPrivateAnchorStability
