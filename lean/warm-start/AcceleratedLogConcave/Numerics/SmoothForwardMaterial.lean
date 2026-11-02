import AcceleratedLogConcave.Numerics.SmoothForward
import AcceleratedLogConcave.Numerics.SmoothConditionalCell
import AcceleratedLogConcave.Numerics.RotatedMarginalLaw

/-! Transfer the published material estimate to the actual fixed-angle forward
seed. Its rewound input has the exact Gaussian marginal; no independence is
asserted. Reference-time conjugacy and finite-coordinate transport are reused. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace AcceleratedLogConcave.Numerics.MeanResidualBridge
open MeanFlowLp AffineGraph ConditionalSmoothing Analysis.PositiveVarianceSlab
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι
variable (d : MeanFlowLp.Data ι m) (j : Fin m) (ρ : d.G.Kernel) (z : ℝ)

/-- On the source slab the marginal is at t itself, not the clamped time. -/
theorem smoothForward_preserving_source {t : ℝ} (ht : t ∈ Icc 0 (backwardEnd d.G.R)) :
    MeasurePreserving (forward d j ρ z t) (seedMeasure d)
      (Conditional.interpolationLaw d.F d.x d.r t) := by
  simpa only [SamplingFlowLp.sourceTime_eq d.G.backwardEnd_pos.le ht] using
    forward_preserving d j ρ z t

/-- The actual rewound forward input, at every fixed deterministic angle. -/
theorem smoothForward_zero_preserving :
    MeasurePreserving (forward d j ρ z 0) (seedMeasure d) (stdGaussian E) := by
  simpa only [Conditional.interpolationLaw_zero d.hF d.hlo d.x d.r] using
    smoothForward_preserving_source d j ρ z ⟨le_rfl,d.G.backwardEnd_pos.le⟩

/-- The reference-b jet uses the same actual zero-time input transported to b. -/
theorem forwardJet_eq_referencePositionJet (q : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (left (backwardEnd d.G.R)) (right (backwardEnd d.G.R))) (w : Seed d) :
    forwardJet d j ρ z q t w =
      (fixedData (transportData d) d.x).positionJet q t
        (referenceInput (transportData d) d.x (forward d j ρ z 0 w)) :=
  jet_snd_eq_referencePositionJet (transportData d) q d.x (forward d j ρ z 0 w) ht

/-- Exact moment transfer for the actual common seed, without a replacement law. -/
theorem integral_forwardJet_sq_eq_gaussian (q : ℕ) (t : ℝ) :
    (∫ w, ‖forwardJet d j ρ z q t w‖^2 ∂seedMeasure d) =
      ∫ y : E, ‖(jet (transportData d) q t (d.x,y)).2‖^2 ∂stdGaussian E := by
  have hp := smoothForward_zero_preserving d j ρ z
  have hc : Continuous (fun y : E => ‖(jet (transportData d) q t (d.x,y)).2‖^2) :=
    (((continuous_jet (transportData d) q).comp
      (continuous_const.prodMk (continuous_const.prodMk continuous_id))).snd).norm.pow 2
  change (∫ w, ‖(jet (transportData d) q t (d.x,forward d j ρ z 0 w)).2‖^2
    ∂seedMeasure d) = _
  rw [← hp.map_eq]
  exact (integral_map hp.measurable.aemeasurable hc.aestronglyMeasurable).symm

theorem norm_sq_forwardJetLp (q : ℕ) (t : ℝ) :
    ‖forwardJetLp d j ρ z q t‖^2 =
      ∫ w, ‖forwardJet d j ρ z q t w‖^2 ∂seedMeasure d :=
  Analysis.DominatedLp.norm_sq_toLp (forwardJet_memLp d j ρ z q t)

/-- State-jet order k+2 has amplitude ell*r^2 and material index k.
The general finite-coordinate supplier includes its explicit isometric transport. -/
theorem forwardJetLp_norm_le_material (k : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 (backwardEnd d.G.R)) :
    ‖forwardJetLp d j ρ z (k+2) t‖ ≤
      (d.ell*d.r^2)*materialOrderFactor (Fintype.card ι) k/(1-t^2)^(k+1) := by
  have hv : 0 < 1-t^2 := Conditional.conditionalVariance_pos
    (by linarith [ht.1]) (ht.2.trans_lt d.G.backwardEnd_lt_one)
  have hnonneg : 0 ≤ (d.ell*d.r^2)*materialOrderFactor (Fintype.card ι) k/(1-t^2)^(k+1) :=
    div_nonneg (mul_nonneg (mul_nonneg d.hell (sq_nonneg _))
      (materialOrderFactor_nonneg _ k)) (pow_nonneg hv.le _)
  have hsq : ‖forwardJetLp d j ρ z (k+2) t‖^2 ≤
      ((d.ell*d.r^2)*materialOrderFactor (Fintype.card ι) k/(1-t^2)^(k+1))^2 := by
    rw [norm_sq_forwardJetLp, integral_forwardJet_sq_eq_gaussian]
    exact integral_gaussian_jet_sq_le_material_fintype (transportData d) d.hsmall k d.x ht
  nlinarith [norm_nonneg (forwardJetLp d j ρ z (k+2) t)]

end AcceleratedLogConcave.Numerics.MeanResidualBridge
