import AcceleratedLogConcave.Numerics.AngleSourceSmooth
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-! Exact all-order chain for the actual angle action.
The spatial endpoint coefficients are exposed, not assumed bounded and not
silently converted into a final Regularity budget. -/
noncomputable section
open Set
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace AcceleratedLogConcave.Numerics.MeanFlowLp
open Conditional AffineGraph AffineGraph.MeanGeometry
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

def angleEndpoint (d : Data ι m) (k : d.G.Kernel) : E → E :=
  TransportFlowLp.flow (transportData d) d.x
    ⟨d.G.rho k,(d.G.rho_mem k).1,(d.G.rho_mem k).2.le⟩ (backwardEnd d.G.R)

omit [DecidableEq ι] in
theorem contDiff_angleEndpoint (d : Data ι m) (k : d.G.Kernel) :
    ContDiff ℝ ∞ (angleEndpoint d k) :=
  contDiff_transport_endpoint d _ ⟨backwardEnd d.G.R,d.G.backwardEnd_pos.le,le_rfl⟩

/-- Literal Faà di Bruno expansion at each shared seed, valid at every finite order. -/
theorem iteratedDeriv_action_angle (d : Data ι m) (j : Fin m) (k : d.G.Kernel)
    (n : ℕ) (z : ℝ) (w : Seed d) :
    iteratedDeriv n (fun t => action d j k t w) z =
      (∑ c : OrderedFinpartition n,
        iteratedFDeriv ℝ c.length (angleEndpoint d k) (rotation d j k z w)
          (fun i => iteratedDeriv (c.partSize i) (fun t => rotation d j k t w) z)) -
      iteratedDeriv n (fun t => rotation d j k t w) z := by
  have hT : ContDiffAt ℝ n (angleEndpoint d k) (rotation d j k z w) :=
    ((contDiff_angleEndpoint d k).of_le (by simp)).contDiffAt
  have hW : ContDiffAt ℝ n (fun t => rotation d j k t w) z :=
    ((contDiff_rotation_angle d j k w).of_le (by simp)).contDiffAt
  change iteratedDeriv n ((angleEndpoint d k ∘ (fun t => rotation d j k t w)) -
    (fun t => rotation d j k t w)) z = _
  rw [iteratedDeriv_sub (hT.comp z hW) hW,
    iteratedDeriv_vcomp_eq_sum_orderedFinpartition hT hW le_rfl]

/-- Explicit spatial-coefficient dependency of the actual source angle jet.
This is a consumer identity/bound, not a derivative-norm-defined budget. -/
theorem norm_iteratedDeriv_action_angle_le (d : Data ι m) (j : Fin m) (k : d.G.Kernel)
    (n : ℕ) (z : ℝ) (w : Seed d) :
    ‖iteratedDeriv n (fun t => action d j k t w) z‖ ≤
      (∑ c : OrderedFinpartition n,
        ‖iteratedFDeriv ℝ c.length (angleEndpoint d k) (rotation d j k z w)‖ *
          ∏ i, ‖iteratedDeriv (c.partSize i) (fun t => rotation d j k t w) z‖) +
      ‖iteratedDeriv n (fun t => rotation d j k t w) z‖ := by
  rw [iteratedDeriv_action_angle]
  apply (norm_sub_le _ _).trans
  apply add_le_add_left
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro c _
  exact ContinuousMultilinearMap.le_opNorm _ _
end AcceleratedLogConcave.Numerics.MeanFlowLp
