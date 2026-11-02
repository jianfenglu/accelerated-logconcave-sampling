import AcceleratedLogConcave.Numerics.SmoothBackwardReplacement
import AcceleratedLogConcave.Numerics.SmoothKernelReplacement

/-! The original-data backward and kernel replacements on one receiver.
Only these two fields change. This does not assert full Regularity. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology
set_option autoImplicit false
namespace AcceleratedLogConcave.Numerics.MeanResidualBridge
open MeanFlowLp AffineGraph AffineGraph.MeanGeometry
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

def curvesWithBackwardKernel (d : Data ι m) : AffineResidual.Mean.Curves d.G (H d) :=
  { curvesWithBackward d with kernel := smoothKernel d }

theorem backwardKernel_equations (d : Data ι m) (U : H d → ℝ → H d)
    (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U) :
    AffineResidual.Mean.Equations d.G (curvesWithBackwardKernel d)
      U d.r d.sigma 0 (initialPosition d) (initialScore d) (initialNoise d) := by
  have hb := replacement_equations d U hu
  have hk := (kernelReplacement d U hu (smoothKernel d) (smoothKernel_agreement d)).1
  exact ⟨hb.position, hb.score, hb.backward, hb.conditional, hb.forward,
    hk.kernel_angle, hk.velocity_kernel⟩

theorem backwardKernel_canonical_equations (d : Data ι m) :
    AffineResidual.Mean.Equations d.G (curvesWithBackwardKernel d)
      (primitiveLp (primitiveData d) (seedMeasure d)) d.r d.sigma 0
      (initialPosition d) (initialScore d) (initialNoise d) :=
  backwardKernel_equations d _ (primitiveLp_spec _ _)

theorem backwardKernel_reference_eq (d : Data ι m) :
    (curvesWithBackwardKernel d).reference d.G 0 d.r =
      (curves d).reference d.G 0 d.r :=
  replacement_reference_eq d

theorem backwardKernel_position_eq (d : Data ι m) :
    (curvesWithBackwardKernel d).position = (curves d).position := rfl

theorem backwardKernel_score_eq (d : Data ι m) :
    (curvesWithBackwardKernel d).score = (curves d).score := rfl

theorem backwardKernel_velocity_eq (d : Data ι m) :
    (curvesWithBackwardKernel d).velocity = (curves d).velocity := rfl

theorem backwardKernel_conditional_eq (d : Data ι m) :
    (curvesWithBackwardKernel d).conditional = (curves d).conditional := rfl

theorem backwardKernel_forward_eq (d : Data ι m) :
    (curvesWithBackwardKernel d).forward = (curves d).forward := rfl

theorem backwardKernel_backward_eq (d : Data ι m) :
    (curvesWithBackwardKernel d).backward = smoothBackward d := rfl

theorem backwardKernel_kernel_eq (d : Data ι m) :
    (curvesWithBackwardKernel d).kernel = smoothKernel d := rfl

/-- The receiver primitive sees exactly the same backward curve as the
backward-only replacement, at every real time. -/
theorem backwardKernel_backwardMean_eq (d : Data ι m) (U : H d → ℝ → H d) :
    (curvesWithBackwardKernel d).backwardMean d.G U 0 d.r =
      (curvesWithBackward d).backwardMean d.G U 0 d.r := rfl

theorem backwardKernel_meanOutput_eq (d : Data ι m) (U : H d → ℝ → H d) :
    d.G.meanOutput d.sigma (initialScore d)
      (fun i => U ((curvesWithBackwardKernel d).reference d.G 0 d.r i)
        (d.G.radius d.r i)) =
    d.G.meanOutput d.sigma (initialScore d)
      (fun i => U ((curves d).reference d.G 0 d.r i) (d.G.radius d.r i)) := by
  rw [backwardKernel_reference_eq]

end AcceleratedLogConcave.Numerics.MeanResidualBridge
