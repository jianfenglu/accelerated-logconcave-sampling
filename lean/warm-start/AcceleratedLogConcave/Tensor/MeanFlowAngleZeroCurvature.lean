import AcceleratedLogConcave.Tensor.MeanFlowAngleDisplacementBudget
import AcceleratedLogConcave.Analysis.AngleZeroCurvature

/-! The zero-curvature branch reaches the literal
fixed-common-seed action and its canonical L2 lift without dividing by ell.
The action is constant in angle, not necessarily the zero vector. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
namespace AcceleratedLogConcave.Numerics.MeanFlowLp
open Conditional Tensor.ForwardFlow
variable {D m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)

theorem fderiv_angleEndpoint_eq_id_of_zero_curvature (d : Data (Fin D) m)
    (hell : d.ell = 0) (k : d.G.Kernel) (y : E) :
    fderiv ℝ (angleEndpoint d k) y = ContinuousLinearMap.id ℝ E := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  rw [angleEndpoint_eq_forwardProbabilityTransport]
  have h := norm_fderiv_forwardProbabilityTransport_sub_id_le d.hF d.hell d.hlo d.hup
    d.x d.hr d.G.backwardEnd_pos.le d.G.backwardEnd_lt_one d.hsmall
    ⟨(d.G.rho_mem k).1,(d.G.rho_mem k).2.le⟩ y
  simpa [hell] using h

/-- The same actual seed is used on both sides. No equality-in-law substitution. -/
theorem action_angle_constant_of_zero_curvature (d : Data (Fin D) m)
    (hell : d.ell = 0) (j : Fin m) (k : d.G.Kernel) (z t : ℝ) (w : Seed d) :
    action d j k z w = action d j k t w := by
  exact Analysis.AnglePhase.displacement_constant_of_derivative_identity
    (angleEndpoint d k) ((contDiff_angleEndpoint d k).differentiable (by simp))
    (fderiv_angleEndpoint_eq_id_of_zero_curvature d hell k)
    (rotation d j k z w) (rotation d j k t w)

theorem positive_action_angle_derivative_zero_of_zero_curvature (d : Data (Fin D) m)
    (hell : d.ell = 0) (j : Fin m) (k : d.G.Kernel) (n : ℕ) (z : ℝ) (w : Seed d) :
    iteratedDeriv (n+1) (fun t => action d j k t w) z = 0 := by
  exact Analysis.AnglePhase.positive_angle_derivative_zero_of_derivative_identity
    (angleEndpoint d k) ((contDiff_angleEndpoint d k).differentiable (by simp))
    (fderiv_angleEndpoint_eq_id_of_zero_curvature d hell k)
    (fun t => rotation d j k t w) n z

/-- Equality in the original canonical L2 space, not a new coupling. -/
theorem actionLp_constant_of_zero_curvature (d : Data (Fin D) m)
    (hell : d.ell = 0) (j : Fin m) (k : d.G.Kernel) (z t : ℝ) :
    actionLp d j k z = actionLp d j k t := by
  exact MemLp.toLp_congr (action_memLp d j k z) (action_memLp d j k t)
    (Filter.Eventually.of_forall (action_angle_constant_of_zero_curvature d hell j k z t))

theorem contDiff_actionLp_of_zero_curvature (d : Data (Fin D) m)
    (hell : d.ell = 0) (j : Fin m) (k : d.G.Kernel) :
    ContDiff ℝ ∞ (actionLp d j k) := by
  have he : actionLp d j k = fun _ => actionLp d j k 0 :=
    funext (fun t => actionLp_constant_of_zero_curvature d hell j k t 0)
  rw [he]
  exact contDiff_const

theorem positive_actionLp_derivative_zero_of_zero_curvature (d : Data (Fin D) m)
    (hell : d.ell = 0) (j : Fin m) (k : d.G.Kernel) (n : ℕ) (z : ℝ) :
    iteratedDeriv (n+1) (actionLp d j k) z = 0 := by
  have he : actionLp d j k = fun _ => actionLp d j k 0 :=
    funext (fun t => actionLp_constant_of_zero_curvature d hell j k t 0)
  rw [he,iteratedDeriv_const]
  simp
end AcceleratedLogConcave.Numerics.MeanFlowLp
