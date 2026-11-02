import AcceleratedLogConcave.Numerics.AngleRotationJets
import AcceleratedLogConcave.Conditional.Transport.JointFlowExtension

/-! Pointwise angle smoothness from original C² Data. This is deliberately
not claimed as L² smoothness: its uniform derivative domination is separate. -/
noncomputable section
open Set Metric
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace AcceleratedLogConcave.Numerics.MeanFlowLp
open Conditional AffineGraph AffineGraph.MeanGeometry
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

theorem contDiff_rotation_angle (d : Data ι m) (j : Fin m) (k : d.G.Kernel)
    (w : Seed d) : ContDiff ℝ ∞ (fun z => rotation d j k z w) := by
  unfold rotation
  fun_prop

omit [DecidableEq ι] in
/-- Local smooth representatives of the actual transport give all-order
spatial regularity without higher derivatives of the original potential. -/
theorem contDiff_transport_endpoint (d : Data ι m) (s t : Icc (0:ℝ) (backwardEnd d.G.R)) :
    ContDiff ℝ ∞ (TransportFlowLp.flow (transportData d) d.x s t) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  obtain ⟨S,hS,heq⟩ := Transport.exists_smooth_convexProbabilityFlow_extension
    d.hF d.hell d.hlo d.hup d.x d.hr d.G.backwardEnd_pos.le d.G.backwardEnd_lt_one d.hsmall y
  have h : ContDiff ℝ ∞ (fun z : E => S (((s:ℝ),(t:ℝ)),z)) :=
    hS.comp (contDiff_const.prodMk contDiff_id)
  apply h.contDiffAt.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds y (by norm_num : (0:ℝ)<1)] with z hz
  rw [TransportFlowLp.flow_eq (transportData d) d.x s t.property]
  exact (heq s t z hz).symm

theorem contDiff_forward_angle (d : Data ι m) (j : Fin m) (k : d.G.Kernel)
    {t : ℝ} (ht : t ∈ Icc 0 (backwardEnd d.G.R)) (w : Seed d) :
    ContDiff ℝ ∞ (fun z => forward d j k z t w) :=
  (contDiff_transport_endpoint d
    ⟨d.G.rho k,(d.G.rho_mem k).1,(d.G.rho_mem k).2.le⟩ ⟨t,ht⟩).comp
      (contDiff_rotation_angle d j k w)

theorem contDiff_action_angle (d : Data ι m) (j : Fin m) (k : d.G.Kernel)
    (w : Seed d) : ContDiff ℝ ∞ (fun z => action d j k z w) :=
  (contDiff_forward_angle d j k ⟨d.G.backwardEnd_pos.le,le_rfl⟩ w).sub
    (contDiff_rotation_angle d j k w)
end AcceleratedLogConcave.Numerics.MeanFlowLp
