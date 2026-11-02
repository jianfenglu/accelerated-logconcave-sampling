import AcceleratedLogConcave.Oracle.SourceMeanPrivateAnchorStability
import AcceleratedLogConcave.Oracle.PrivateAnchorRmsHelpers
import AcceleratedLogConcave.Oracle.SamplingCanonicalTapeMeasurability

/-! Arbitrary common measure: correlations and random incoming coordinates are
allowed. Only the ANCHOR DIFFERENCE needs L2, not either anchor or either output.
Source candidate only; receiving-side Lean replay is mandatory. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Oracle.SourceMeanPrivateAnchorStability
open MeasureTheory Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open RetainedMeanFinalBatch FixedTapeStability SourceMeanExecutable SourceMeanShift
open OperationalMeasurability CanonicalTapeMeasurability AnchorRmsHelpers
open scoped BigOperators ENNReal

variable {d m n a h : ℕ}
variable (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
    (r σ Ds δ t w : ℝ) (main : Fin n → ExecutableData)
    (final : Fin m → ExecutableData) (sampling : ExecutableData)
variable {Ω : Type*} [MeasurableSpace Ω]
local notation "tbl" => SourceMeanExecutable.table M nodes anchors r σ Ds δ t w main final sampling

/-- The concrete cache is measurable whenever its ordinary point coordinates are.
No measurable-space instance is installed on an environment carrier. -/
theorem cache_path_measurable (x P U : Ω → Point d)
    (raw : Ω → Fin (m+1) → Point d) (Z : Ω → Fin h → Point d)
    (hx : Measurable x) (hP : Measurable P) (hU : Measurable U)
    (hraw : ∀ i, Measurable (fun ω => raw ω i))
    (hZ : ∀ i, Measurable (fun ω => Z ω i)) :
    EnvPathMeasurable (fun ω => cache M nodes anchors seeds r σ Ds δ t w main final sampling
      (x ω) (P ω) (U ω) (raw ω) (Z ω)) := by
  have hY : Measurable (β := Point d) (fun ω => backwardEnd M.R • U ω) :=
    (measurable_const : Measurable (fun _ : Ω => (backwardEnd M.R : ℝ))).smul hU
  have hsplit (i : Fin (m+1)) : Measurable (β := Point d) (fun ω =>
      splitValues M nodes anchors r σ Ds δ t w main final sampling (P ω) (raw ω) i) := by
    let slots : Fin ((m+1)*(m+1)+(m+1)) →
        Fin (SourceMeanExecutable.size (a := a) main final sampling) :=
      SourceMeanExecutable.prefixSlot (a := a) main final sampling ∘
        PrefixPublicTable.assemblySlot (privateC := sampling.size) (f := m+1) (n := n) (a := a)
    unfold splitValues MeanExecutablePrefix.assemblyValues
    exact ((measurable_const : Measurable (fun _ : Ω =>
      (tbl (slots (Fin.natAdd ((m+1)*(m+1)) i)) : ℝ))).smul hP).add
      (Finset.measurable_sum _ (fun j _ =>
        (measurable_const : Measurable (fun _ : Ω =>
          (tbl (slots (matrixIndex (m+1) i j)) : ℝ))).smul (hraw j)))
  have hanchor (i : M.Anchor) : Measurable (β := Point d) (fun ω => M.anchorValues
      (backwardEnd M.R • U ω)
      (splitValues M nodes anchors r σ Ds δ t w main final sampling (P ω) (raw ω) 0)
      (fun b ρ => Z ω (seeds.symm (b,ρ))) i) := by
    rcases i with i | i
    · exact hY
    · rcases i with i | ⟨b,ρ⟩
      · exact hsplit 0
      · exact hZ (seeds.symm (b,ρ))
  have hdir (i : Fin n) : Measurable (β := Point d) (fun ω => M.direct r σ (x ω)
      (backwardEnd M.R • U ω)
      (splitValues M nodes anchors r σ Ds δ t w main final sampling (P ω) (raw ω) 0)
      (fun b ρ => Z ω (seeds.symm (b,ρ))) (nodes i)) := by
    unfold MeanGeometry.direct
    exact hx.add (Finset.measurable_sum _ (fun j _ =>
      (measurable_const : Measurable (fun _ : Ω =>
        (M.centerForm r σ (nodes i) (Sum.inl j) : ℝ))).smul (hanchor j)))
  unfold cache
  apply envPathMeasurable_prepend _ _ _ hdir
  apply envPathMeasurable_prepend _ _ _ hZ
  apply envPathMeasurable_prepend _ _ _ hsplit
  apply envPathMeasurable_prepend _ _ _ hraw
  apply envPathMeasurable_prepend _ _ _ (fun _ => hY)
  apply envPathMeasurable_prepend _ _ _ (fun _ => hU)
  exact envPathMeasurable_cons (d := d) (τ := .point) _ _ hP
    (envPathMeasurable_cons (d := d) (τ := .point) _ _ hx envPathMeasurable_empty)

/-- Literal interpreter measurability with actual cache-coordinate measurability.
The premise is about stored inputs, not output accuracy or output moments. -/
theorem output_measurable (N : ℕ) (G : Point d → Point d) (hG : Measurable G)
    (x P U : Ω → Point d) (raw : Ω → Fin (m+1) → Point d) (Z : Ω → Fin h → Point d)
    (τ : Ω → Tape d (body (a := a) (h := h) M nodes main final sampling N))
    (hx : Measurable x) (hP : Measurable P)
    (hc : EnvPathMeasurable (fun ω =>
      cache M nodes anchors seeds r σ Ds δ t w main final sampling (x ω) (P ω) (U ω) (raw ω) (Z ω)))
    (hτ : TapePathMeasurable (body (a := a) (h := h) M nodes main final sampling N) τ) :
    Measurable (fun ω => output M nodes anchors seeds r σ Ds δ t w main final sampling
      N G (x ω) (P ω) (U ω) (raw ω) (Z ω) (τ ω)) := by
  exact run_value (body (a := a) (h := h) M nodes main final sampling N) G hG
    (fun ω => ⟨tbl,x ω,P ω⟩)
    (fun ω => cache M nodes anchors seeds r σ Ds δ t w main final sampling
      (x ω) (P ω) (U ω) (raw ω) (Z ω)) τ
    (fun _ => measurable_const) hx hP hc hτ

/-- Explicit discharge of the later difference-measurability premise from
ordinary random coordinates and the literal full-tape path. -/
theorem output_difference_aestronglyMeasurable (N : ℕ)
    (G : Point d → Point d) (hG : Measurable G) (μ : Measure Ω)
    (x P U V : Ω → Point d) (raw : Ω → Fin (m+1) → Point d) (Z : Ω → Fin h → Point d)
    (τ : Ω → Tape d (body (a := a) (h := h) M nodes main final sampling N))
    (hx : Measurable x) (hP : Measurable P) (hU : Measurable U) (hV : Measurable V)
    (hraw : ∀ i, Measurable (fun ω => raw ω i))
    (hZ : ∀ i, Measurable (fun ω => Z ω i))
    (hτ : TapePathMeasurable (body (a := a) (h := h) M nodes main final sampling N) τ) :
    AEStronglyMeasurable (fun ω =>
      output M nodes anchors seeds r σ Ds δ t w main final sampling N G
        (x ω) (P ω) (U ω) (raw ω) (Z ω) (τ ω) -
      output M nodes anchors seeds r σ Ds δ t w main final sampling N G
        (x ω) (P ω) (V ω) (raw ω) (Z ω) (τ ω)) μ := by
  have hcu : EnvPathMeasurable (fun ω =>
      cache M nodes anchors seeds r σ Ds δ t w main final sampling
        (x ω) (P ω) (U ω) (raw ω) (Z ω)) :=
    cache_path_measurable M nodes anchors seeds r σ Ds δ t w main final sampling
      x P U raw Z hx hP hU hraw hZ
  have hcv : EnvPathMeasurable (fun ω =>
      cache M nodes anchors seeds r σ Ds δ t w main final sampling
        (x ω) (P ω) (V ω) (raw ω) (Z ω)) :=
    cache_path_measurable M nodes anchors seeds r σ Ds δ t w main final sampling
      x P V raw Z hx hP hV hraw hZ
  exact ((output_measurable M nodes anchors seeds r σ Ds δ t w main final sampling
    N G hG x P U raw Z τ hx hP hcu hτ).sub
    (output_measurable M nodes anchors seeds r σ Ds δ t w main final sampling
    N G hG x P V raw Z τ hx hP hcv hτ)).aestronglyMeasurable

section CommonMeasure
variable (N : ℕ) (G : Point d → Point d) (κ A : ℝ)
    (hm : 0 < m) (hr : 0 ≤ r) (hκ : 0 ≤ κ) (hA : 0 ≤ A)
    (hpsi : M.psi ≤ M.R^4)
    (hmain : ∀ i, ChildStable (main i).program (main i).coefficient G κ)
    (hfinal : ∀ i, ChildStable (final i).program (final i).coefficient G κ)
    (hrow : ∀ i : M.MeanNode, ∑ j, |M.matrix r σ i j| ≤ A)
    (μ : Measure Ω) (x P U V : Ω → Point d)
    (raw : Ω → Fin (m+1) → Point d) (Z : Ω → Fin h → Point d)
    (τ : Ω → Tape d (body (a := a) (h := h) M nodes main final sampling N))
local notation "out" => fun W ω => output M nodes anchors seeds r σ Ds δ t w main final sampling
  N G (x ω) (P ω) (W ω) (raw ω) (Z ω) (τ ω)
include hm hr hκ hA hpsi hmain hfinal hrow

/-- No separate absolute moments, independence, or reference coupling premise. -/
theorem output_difference_memLp_and_eLpNorm_le
    (hout : AEStronglyMeasurable (fun ω => out U ω - out V ω) μ)
    (hUV : MemLp (fun ω => U ω - V ω) 2 μ) :
    MemLp (fun ω => out U ω - out V ω) 2 μ ∧
    eLpNorm (fun ω => out U ω - out V ω) 2 μ ≤
      ENNReal.ofReal (coefficient M r N κ A) * eLpNorm (fun ω => U ω - V ω) 2 μ := by
  apply memLp_two_and_eLpNorm_le_of_norm_le_mul hout hUV
  intro ω
  exact output_sub_le M nodes anchors seeds r σ Ds δ t w main final sampling N G κ A
    hm hr hκ hA hpsi hmain hfinal hrow (x ω) (P ω) (U ω) (V ω) (raw ω) (Z ω) (τ ω)

/-- Real RMS of the executed-body difference under any common measure. -/
theorem output_rms_difference_le
    (hout : AEStronglyMeasurable (fun ω => out U ω - out V ω) μ)
    (hUV : MemLp (fun ω => U ω - V ω) 2 μ) :
    Real.sqrt (∫ ω, ‖out U ω - out V ω‖^2 ∂μ) ≤
      coefficient M r N κ A * Real.sqrt (∫ ω, ‖U ω - V ω‖^2 ∂μ) := by
  apply rms_le_of_norm_le_mul hout hUV (coefficient_nonneg M r N κ A hr hκ hA)
  intro ω
  exact output_sub_le M nodes anchors seeds r σ Ds δ t w main final sampling N G κ A
    hm hr hκ hA hpsi hmain hfinal hrow (x ω) (P ω) (U ω) (V ω) (raw ω) (Z ω) (τ ω)
end CommonMeasure
/-- Zero-layer RMS supplier: no main-child stability or row bound is required. -/
theorem output_zero_rms_difference_le (G : Point d → Point d) (κ : ℝ)
    (hm : 0 < m) (hr : 0 ≤ r) (hκ : 0 ≤ κ) (hpsi : M.psi ≤ M.R^4)
    (hfinal : ∀ i, ChildStable (final i).program (final i).coefficient G κ)
    (μ : Measure Ω) (x P U V : Ω → Point d)
    (raw : Ω → Fin (m+1) → Point d) (Z : Ω → Fin h → Point d)
    (τ : Ω → Tape d (body (a := a) (h := h) M nodes main final sampling 0))
    (hout : AEStronglyMeasurable (fun ω =>
      output M nodes anchors seeds r σ Ds δ t w main final sampling 0 G
        (x ω) (P ω) (U ω) (raw ω) (Z ω) (τ ω) -
      output M nodes anchors seeds r σ Ds δ t w main final sampling 0 G
        (x ω) (P ω) (V ω) (raw ω) (Z ω) (τ ω)) μ)
    (hUV : MemLp (fun ω => U ω - V ω) 2 μ) :
    Real.sqrt (∫ ω, ‖output M nodes anchors seeds r σ Ds δ t w main final sampling 0 G
        (x ω) (P ω) (U ω) (raw ω) (Z ω) (τ ω) -
      output M nodes anchors seeds r σ Ds δ t w main final sampling 0 G
        (x ω) (P ω) (V ω) (raw ω) (Z ω) (τ ω)‖^2 ∂μ) ≤
      (κ*r*(backwardEnd M.R)^2) * Real.sqrt (∫ ω, ‖U ω - V ω‖^2 ∂μ) := by
  apply rms_le_of_norm_le_mul hout hUV (by positivity)
  intro ω
  exact output_zero_sub_le M nodes anchors seeds r σ Ds δ t w main final sampling G κ
    hm hr hκ hpsi hfinal (x ω) (P ω) (U ω) (V ω) (raw ω) (Z ω) (τ ω)

end AcceleratedLogConcave.Oracle.SourceMeanPrivateAnchorStability
