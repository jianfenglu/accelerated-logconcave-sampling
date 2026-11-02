import AcceleratedLogConcave.Numerics.SmoothKernelReplacement

/-! Explicit low-order bounds for the actual smooth replacement on the closed
source interval. The common-seed pullback is an isometry, and ordinary first
derivatives agree even at the endpoints. These estimates do not supply the
order-(m+2) envelope required by the numerical receiver. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option autoImplicit false
namespace AcceleratedLogConcave.Numerics.MeanResidualBridge
open MeanFlowLp AffineGraph AffineGraph.MeanGeometry Analysis.PositiveVarianceSlab
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

/-- The actual fixed common-seed pullback preserves distances. -/
theorem isometry_kernelPullback (d : MeanFlowLp.Data ι m) (j : Fin m) :
    Isometry (kernelPullback d j) :=
  (Lp.compMeasurePreservingₗᵢ (p := 2) ℝ (phase d (centerNode j))
    (kernel_phase_preserving d (centerNode j))).isometry

/-- No dimension or time factor is lost on passage to the common seed. -/
theorem norm_kernelPullback (d : MeanFlowLp.Data ι m) (j : Fin m)
    (u : Lp E 2 (KernelFlowLp.seedMeasure (kernelData d))) :
    ‖kernelPullback d j u‖ = ‖u‖ :=
  (Lp.compMeasurePreservingₗᵢ (p := 2) ℝ (phase d (centerNode j))
    (kernel_phase_preserving d (centerNode j))).norm_map u

/-- Closed-slab agreement determines the ordinary derivative, including at
zero and the terminal endpoint, because the replacement is differentiable
on a genuine neighborhood of the slab. -/
theorem hasDerivAt_smoothKernel_source (d : MeanFlowLp.Data ι m) (j : Fin m)
    {t : ℝ} (ht : t ∈ Icc 0 (backwardEnd d.G.R)) :
    HasDerivAt (smoothKernel d j) ((d.r * t) • MeanFlowLp.integrandLp d j t) t := by
  have hn := source_subset d.G.backwardEnd_pos.le d.G.backwardEnd_lt_one ht
  have hd : DifferentiableAt ℝ (smoothKernel d j) t :=
    ((contDiffOn_smoothKernel d j 1).contDiffAt (isOpen_Ioo.mem_nhds hn)).differentiableAt_one
  have hu := uniqueDiffOn_Icc d.G.backwardEnd_pos t ht
  have hh : HasDerivWithinAt (smoothKernel d j)
      ((d.r * t) • MeanFlowLp.integrandLp d j t) (Icc 0 (backwardEnd d.G.R)) t :=
    (hasDerivAt_kernelLp d j t).hasDerivWithinAt.congr_of_mem
      (smoothKernel_agreement d j) ht
  have he := (hd.hasDerivAt.hasDerivWithinAt.derivWithin hu).symm.trans (hh.derivWithin hu)
  simpa only [he] using hd.hasDerivAt

theorem deriv_smoothKernel_source (d : MeanFlowLp.Data ι m) (j : Fin m)
    {t : ℝ} (ht : t ∈ Icc 0 (backwardEnd d.G.R)) :
    deriv (smoothKernel d j) t = (d.r * t) • MeanFlowLp.integrandLp d j t :=
  (hasDerivAt_smoothKernel_source d j ht).deriv

/-- Explicit first-derivative bound with the vanishing factor t and the
physical square-root dimension dependence. -/
theorem norm_deriv_smoothKernel_le (d : MeanFlowLp.Data ι m) (j : Fin m)
    {t : ℝ} (ht : t ∈ Icc 0 (backwardEnd d.G.R)) :
    ‖deriv (smoothKernel d j) t‖ ≤
      Real.exp 1 * d.r ^ 2 * d.ell * t * Real.sqrt (Module.finrank ℝ E) := by
  rw [deriv_smoothKernel_source d j ht, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg d.hr.le ht.1), MeanFlowLp.integrandLp, norm_kernelPullback]
  calc
    (d.r * t) * ‖KernelFlowLp.integrandLp (kernelData d) t‖ ≤
        (d.r * t) * (Real.exp 1 * (d.r * d.ell) * Real.sqrt (Module.finrank ℝ E)) :=
      mul_le_mul_of_nonneg_left (KernelFlowLp.norm_integrandLp_le (kernelData d) t)
        (mul_nonneg d.hr.le ht.1)
    _ = _ := by ring

/-- The exact existing zeroth-order source envelope survives the replacement
and the common-seed isometry, including its terminal vanishing factor. -/
theorem norm_smoothKernel_le (d : MeanFlowLp.Data ι m) (j : Fin m)
    {t : ℝ} (ht : t ∈ Icc 0 (backwardEnd d.G.R)) :
    ‖smoothKernel d j t‖ ≤
      (Real.exp 1 * d.r ^ 2 * d.ell / 2 * ((backwardEnd d.G.R) ^ 2 - t ^ 2)) *
        Real.sqrt (Module.finrank ℝ E) := by
  rw [smoothKernel, norm_kernelPullback, KernelFlowLp.smoothExtensionLp_eq (kernelData d) ht]
  exact KernelFlowLp.norm_extensionLp_le (kernelData d) ht

end AcceleratedLogConcave.Numerics.MeanResidualBridge
