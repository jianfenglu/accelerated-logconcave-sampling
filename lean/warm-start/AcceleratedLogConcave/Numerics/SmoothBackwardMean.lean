import AcceleratedLogConcave.Numerics.SmoothKernel
import AcceleratedLogConcave.Analysis.FiniteDerivativeLadder
import AcceleratedLogConcave.Numerics.MeanResidualBridge

/-! A smooth position-jet supplier on the enlarged positive-variance slab.
The original source curves are not changed. All moment and derivative
premises are derived from the original C² convexity assumptions. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
open Analysis.PositiveVarianceSlab
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
variable (d : PositiveVarianceFlowData (EuclideanSpace ℝ ι))

def positionMeasure : Measure E := interpolationLaw d.F d.x d.r d.b
instance positionMeasure_probability : IsProbabilityMeasure d.positionMeasure :=
  interpolationLaw_isProbabilityMeasure d.hF d.hlo d.x d.r d.b

def positionJet (k : ℕ) (t : ℝ) (y : E) : E := (d.jet k t y).fst

theorem continuous_positionJet (k : ℕ) :
    Continuous (Function.uncurry (d.positionJet k)) := (d.continuous_jet k).fst

theorem exists_positionJet_envelope (k : ℕ) :
    ∃ B : E → ℝ, MemLp B 2 d.positionMeasure ∧ ∀ t y, ‖d.positionJet k t y‖ ≤ B y := by
  let := interpolationLaw_isProbabilityMeasure d.hF d.hlo d.x d.r d.b
  obtain ⟨C, hC, N, hb⟩ := d.exists_jet_polynomial_bound k
  refine ⟨fun y => C * (1 + ‖y‖) ^ N, ?_, ?_⟩
  · exact (Analysis.PolynomialLp.memLp_two_one_add_norm_pow N
      (interpolationLaw_integrable_norm_pow d.hF d.hlo d.x d.r d.b (2 * N))).const_mul C
  · intro t y
    exact (norm_fst_le (d.jet k t y)).trans (hb t y)

theorem positionJet_memLp (k : ℕ) (t : ℝ) :
    MemLp (d.positionJet k t) 2 d.positionMeasure := by
  obtain ⟨B, hB, hb⟩ := d.exists_positionJet_envelope k
  exact hB.mono'
    ((d.continuous_positionJet k).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall (hb t))

def positionJetLp (k : ℕ) (t : ℝ) : Lp E 2 d.positionMeasure :=
  (d.positionJet_memLp k t).toLp (d.positionJet k t)

theorem hasDerivAt_positionJet (k : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (left d.b) (right d.b)) (y : E) :
    HasDerivAt (fun u => d.positionJet k u y) (d.positionJet (k + 1) t y) t :=
  (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)).hasFDerivAt.comp_hasDerivAt t
    (d.hasDerivAt_jet k ht y)

theorem hasDerivAt_positionJetLp (k : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (left d.b) (right d.b)) :
    HasDerivAt (d.positionJetLp k) (d.positionJetLp (k + 1) t) t := by
  obtain ⟨B, hB, hb⟩ := d.exists_positionJet_envelope (k + 1)
  exact Analysis.DominatedLp.hasDerivAt_toLp_of_dominated
    (d.positionJet k) (d.positionJet (k + 1)) (d.continuous_positionJet (k + 1))
    B hB hb (d.positionJet_memLp k) (d.positionJet_memLp (k + 1))
    (fun u hu y => d.hasDerivAt_positionJet k hu y) ht

theorem contDiffOn_positionJetLp (n k : ℕ) :
    ContDiffOn ℝ n (d.positionJetLp k) (Ioo (left d.b) (right d.b)) := by
  choose B hB hb using (fun q : ℕ => d.exists_positionJet_envelope (k + q))
  exact Analysis.DominatedLp.contDiffOn_toLp_of_finite_ladder n
    (fun q => d.positionJet (k + q))
    (fun q _ t => d.positionJet_memLp (k + q) t)
    (fun q _ => d.continuous_positionJet (k + q)) B (fun q _ => hB q)
    (fun q _ => hb q)
    (fun q _ t ht y => by simpa only [Nat.add_assoc] using d.hasDerivAt_positionJet (k + q) ht y)

theorem iteratedDeriv_positionJetLp (n k : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (left d.b) (right d.b)) :
    iteratedDeriv n (d.positionJetLp k) t = d.positionJetLp (k + n) t := by
  have h := Analysis.iteratedDeriv_eq_of_finite_ladder n
    (fun q => d.positionJetLp (k + q)) isOpen_Ioo
    (fun q _ u hu => by simpa only [Nat.add_assoc] using d.hasDerivAt_positionJetLp (k + q) hu) ht
  simpa only [Nat.add_zero] using h

theorem positionJet_zero_eq_state {t : ℝ}
    (ht : t ∈ Icc (left d.b) (right d.b)) (y : E) :
    d.positionJet 0 t y = (d.state t y).fst := by
  simp only [positionJet, jet, Analysis.ODEJet.stateJet, d.time_eq ht]

theorem positionJet_zero_eq_source {t : ℝ} (ht : t ∈ Icc 0 d.b) (y : E) :
    d.positionJet 0 t y =
      convexProbabilityFlow d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0
        (by norm_num) d.hb1 ⟨d.b, d.hb0, le_rfl⟩ y t := by
  rw [d.positionJet_zero_eq_state (d.source_subset_construction ht)]
  exact d.flow_eq_source ⟨d.b, d.hb0, le_rfl⟩ ⟨t, ht⟩ y

theorem positionJet_one_eq_mean {t : ℝ}
    (ht : t ∈ Ioo (left d.b) (right d.b)) (y : E) :
    d.positionJet 1 t y = -d.r • conditionalMean d.F d.x d.r t (d.positionJet 0 t y) := by
  have hs := (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)).hasFDerivAt.comp_hasDerivAt t
    (d.hasDerivAt_state ht y)
  have he : (fun u => d.positionJet 0 u y) =ᶠ[𝓝 t] (fun u => (d.state u y).fst) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    exact d.positionJet_zero_eq_state ⟨hu.1.le, hu.2.le⟩ y
  have hh := (d.hasDerivAt_positionJet 0 ht y).unique (hs.congr_of_eventuallyEq he)
  change d.positionJet 1 t y = -d.r • conditionalMean d.F d.x d.r t (d.state t y).fst at hh
  rw [d.positionJet_zero_eq_state ⟨ht.1.le, ht.2.le⟩]
  exact hh

end AcceleratedLogConcave.Conditional.PositiveVarianceFlowData

namespace AcceleratedLogConcave.Numerics.MeanResidualBridge
open MeanFlowLp AffineGraph AffineGraph.MeanGeometry Conditional Analysis.PositiveVarianceSlab
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

def backwardSmoothData (d : Data ι m) := KernelFlowLp.smoothData (kernelData d)

theorem position_center_preserving (d : Data ι m) (j : Fin m) :
    MeasurePreserving (position d (centerNode j)) (seedMeasure d)
      (backwardSmoothData d).positionMeasure :=
  (CenteringFlowLp.position_preserving (kernelData d)).comp
    (kernel_phase_preserving d (centerNode j))

def positionPullback (d : Data ι m) (j : Fin m) :
    Lp E 2 (backwardSmoothData d).positionMeasure →L[ℝ] H d :=
  (Lp.compMeasurePreservingₗᵢ (p := 2) ℝ (position d (centerNode j))
    (position_center_preserving d j)).toContinuousLinearMap

def pulledPositionJet (d : Data ι m) (j : Fin m) (k : ℕ) (t : ℝ) : H d :=
  positionPullback d j ((backwardSmoothData d).positionJetLp k t)

def smoothBackward (d : Data ι m) (j : Fin m) : ℝ → H d := pulledPositionJet d j 0

def smoothBackwardMean (d : Data ι m) (j : Fin m) (t : ℝ) : H d :=
  -d.r⁻¹ • pulledPositionJet d j 1 t

theorem norm_pulledPositionJet (d : Data ι m) (j : Fin m) (k : ℕ) (t : ℝ) :
    ‖pulledPositionJet d j k t‖ = ‖(backwardSmoothData d).positionJetLp k t‖ :=
  Lp.norm_compMeasurePreserving _ (position_center_preserving d j)

theorem hasDerivAt_pulledPositionJet (d : Data ι m) (j : Fin m) (k : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (left (backwardEnd d.G.R)) (right (backwardEnd d.G.R))) :
    HasDerivAt (pulledPositionJet d j k) (pulledPositionJet d j (k + 1) t) t :=
  (positionPullback d j).hasFDerivAt.comp_hasDerivAt t
    ((backwardSmoothData d).hasDerivAt_positionJetLp k ht)

theorem contDiffOn_pulledPositionJet (d : Data ι m) (j : Fin m) (n k : ℕ) :
    ContDiffOn ℝ n (pulledPositionJet d j k)
      (Ioo (left (backwardEnd d.G.R)) (right (backwardEnd d.G.R))) :=
  (positionPullback d j).contDiff.comp_contDiffOn
    ((backwardSmoothData d).contDiffOn_positionJetLp n k)

theorem contDiffAt_smoothBackwardMean (d : Data ι m) (j : Fin m) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 (backwardEnd d.G.R)) :
    ContDiffAt ℝ n (smoothBackwardMean d j) t :=
  ((contDiffOn_pulledPositionJet d j n 1).const_smul (-d.r⁻¹)).contDiffAt
    (isOpen_Ioo.mem_nhds (source_subset d.G.backwardEnd_pos.le d.G.backwardEnd_lt_one ht))

theorem iteratedDeriv_smoothBackwardMean (d : Data ι m) (j : Fin m) (n : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (left (backwardEnd d.G.R)) (right (backwardEnd d.G.R))) :
    iteratedDeriv n (smoothBackwardMean d j) t = -d.r⁻¹ • pulledPositionJet d j (n + 1) t := by
  exact Analysis.iteratedDeriv_eq_of_finite_ladder n
    (fun q t => -d.r⁻¹ • pulledPositionJet d j (q + 1) t) isOpen_Ioo
    (fun q _ u hu => by
      change HasDerivAt (-d.r⁻¹ • pulledPositionJet d j (q + 1))
        (-d.r⁻¹ • pulledPositionJet d j ((q + 1) + 1) u) u
      exact (hasDerivAt_pulledPositionJet d j (q + 1) hu).const_smul (-d.r⁻¹)) ht

theorem norm_iteratedDeriv_smoothBackwardMean (d : Data ι m) (j : Fin m) (n : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (left (backwardEnd d.G.R)) (right (backwardEnd d.G.R))) :
    ‖iteratedDeriv n (smoothBackwardMean d j) t‖ =
      d.r⁻¹ * ‖(backwardSmoothData d).positionJetLp (n + 1) t‖ := by
  rw [iteratedDeriv_smoothBackwardMean d j n ht, norm_smul, Real.norm_eq_abs,
    abs_neg, abs_of_pos (inv_pos.mpr d.hr), norm_pulledPositionJet]

theorem smoothBackward_eq (d : Data ι m) (j : Fin m) {t : ℝ}
    (ht : t ∈ Icc 0 (backwardEnd d.G.R)) :
    smoothBackward d j t = backwardLp d j t := by
  change (((backwardSmoothData d).positionJet_memLp 0 t).comp_measurePreserving
    (position_center_preserving d j)).toLp _ = (backward_memLp d j t).toLp _
  apply MemLp.toLp_congr
  filter_upwards [] with z
  dsimp only [Function.comp_apply]
  rw [(backwardSmoothData d).positionJet_zero_eq_source ht]
  exact (TransportFlowLp.flow_eq (transportData d) d.x _ ht _).symm

theorem smoothBackwardMean_eq (d : Data ι m) (j : Fin m) {t : ℝ}
    (ht : t ∈ Icc 0 (backwardEnd d.G.R)) :
    smoothBackwardMean d j t = backwardMeanLp d j t := by
  let hm := ((backwardSmoothData d).positionJet_memLp 1 t).comp_measurePreserving
    (position_center_preserving d j)
  change -d.r⁻¹ • hm.toLp _ = (backwardMean_memLp d j t).toLp _
  rw [← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  filter_upwards [] with z
  dsimp only [Function.comp_apply, Pi.smul_apply]
  have hi := source_subset d.G.backwardEnd_pos.le d.G.backwardEnd_lt_one ht
  rw [(backwardSmoothData d).positionJet_one_eq_mean hi,
    (backwardSmoothData d).positionJet_zero_eq_source ht]
  change -d.r⁻¹ • (-d.r • Conditional.conditionalMean d.F d.x d.r t _) = _
  rw [smul_smul, neg_mul_neg, inv_mul_cancel₀ (ne_of_gt d.hr), one_smul]
  rw [AffineFlowIdentities.conditionalMean_eq_primitiveMean d.hF d.hell d.hlo d.hup
    d.x d.hr (by linarith [ht.1]) (ht.2.trans_lt d.G.backwardEnd_lt_one)]
  simp only [backwardMean, SamplingFlowLp.sourceTime_eq d.G.backwardEnd_pos.le ht,
    MeanFlowLp.backward, TransportFlowLp.flow_eq (transportData d) d.x _ ht]
  rfl

theorem contDiffAt_smoothBackward (d : Data ι m) (j : Fin m) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 (backwardEnd d.G.R)) :
    ContDiffAt ℝ n (smoothBackward d j) t :=
  (contDiffOn_pulledPositionJet d j n 0).contDiffAt
    (isOpen_Ioo.mem_nhds (source_subset d.G.backwardEnd_pos.le d.G.backwardEnd_lt_one ht))

theorem raw_smoothBackward_eq (d : Data ι m) (j : Fin m) {t : ℝ}
    (ht : t ∈ Icc 0 (backwardEnd d.G.R)) (z : Seed d) :
    (backwardSmoothData d).positionJet 0 t (position d (centerNode j) z) =
      MeanFlowLp.backward d j t z := by
  rw [(backwardSmoothData d).positionJet_zero_eq_source ht]
  exact (TransportFlowLp.flow_eq (transportData d) d.x _ ht _).symm

/-- Literal pointwise equality implies equality of the pushforward laws. -/
theorem raw_smoothBackward_law_eq (d : Data ι m) (j : Fin m) {t : ℝ}
    (ht : t ∈ Icc 0 (backwardEnd d.G.R)) :
    (seedMeasure d).map (fun z =>
      (backwardSmoothData d).positionJet 0 t (position d (centerNode j) z)) =
      (seedMeasure d).map (MeanFlowLp.backward d j t) := by
  congr 1
  funext z
  exact raw_smoothBackward_eq d j ht z

end AcceleratedLogConcave.Numerics.MeanResidualBridge
