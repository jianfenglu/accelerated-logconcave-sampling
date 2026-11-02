import AcceleratedLogConcave.Numerics.SmoothConditionalMarginals
import AcceleratedLogConcave.Numerics.SmoothBackwardMean

/-! Reference-time conjugacy for the actual conditional path. The input at
time b is the same Gaussian input transported from zero, at the same center.
The reference posterior law is used only after this explicit transport. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace AcceleratedLogConcave.Numerics.ConditionalSmoothing
open Conditional Analysis.PositiveVarianceSlab OAI.LogConcaveSampling.GlobalODE
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι
variable (d : SamplingCenterLp.Data ι)

/-- Transport from probability time zero to the reference time b. -/
def referenceInput (x z : E) : E := SamplingCenterLp.path d x d.b z

omit [DecidableEq ι] in
theorem jointPath_snd_eq_referenceState (x z : E) {t : ℝ}
    (ht : t ∈ Icc (left d.b) (right d.b)) :
    (jointPath d t (x,z)).2 =
      ((fixedData d x).state t (referenceInput d x z)).fst := by
  have hb : d.b ∈ Icc 0 d.b := ⟨d.hb, le_rfl⟩
  have he := jointPath_snd_eq_source d x z hb
  rw [jointPath_eq_fixed, time_eq d ((fixedData d x).source_subset_construction hb)] at he
  rw [jointPath_eq_fixed, time_eq d ht]
  change flow (fixedData d x).lipschitz_clippedVelocity
    (fixedData d x).continuous_clippedVelocity (start d) z t =
      flow (fixedData d x).lipschitz_clippedVelocity
        (fixedData d x).continuous_clippedVelocity (fixedData d x).reference
        (SamplingCenterLp.path d x d.b z) t
  rw [← he]
  exact (flow_cocycle (fixedData d x).lipschitz_clippedVelocity
    (fixedData d x).continuous_clippedVelocity (start d)
    (fixedData d x).reference ⟨t,ht⟩ z).symm

omit [DecidableEq ι] in
/-- Equality of the actual time jets, proved from their derivative ladders on
the open construction interval, not by changing the initial input law. -/
theorem jet_snd_eq_referencePositionJet (k : ℕ) (x z : E) {t : ℝ}
    (ht : t ∈ Ioo (left d.b) (right d.b)) :
    (jet d k t (x,z)).2 =
      (fixedData d x).positionJet k t (referenceInput d x z) := by
  have hleft := Analysis.iteratedDeriv_eq_of_finite_ladder k
    (fun q u => (jet d q u (x,z)).2) isOpen_Ioo
    (fun q _ u hu => (hasDerivAt_jet d q hu (x,z)).snd) ht
  have hright := Analysis.iteratedDeriv_eq_of_finite_ladder k
    (fun q u => (fixedData d x).positionJet q u (referenceInput d x z)) isOpen_Ioo
    (fun q _ u hu => (fixedData d x).hasDerivAt_positionJet q hu _) ht
  have he : (fun u => (jet d 0 u (x,z)).2) =ᶠ[𝓝 t]
      (fun u => (fixedData d x).positionJet 0 u (referenceInput d x z)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    rw [jet_zero, (fixedData d x).positionJet_zero_eq_state ⟨hu.1.le,hu.2.le⟩]
    exact jointPath_snd_eq_referenceState d x z ⟨hu.1.le,hu.2.le⟩
  rw [← hleft, ← hright]
  exact (he.iteratedDeriv k).eq_of_nhds

theorem referenceInput_measurePreserving (x : E) :
    MeasurePreserving (referenceInput d x) (stdGaussian E) (fixedData d x).positionMeasure :=
  path_measurePreserving d x ⟨d.hb, le_rfl⟩

/-- Exact Gaussian-to-reference-posterior moment identity at every interior
construction time, hence also at both source endpoints. -/
theorem integral_jet_sq_eq_referencePositionJet (k : ℕ) (x : E) {t : ℝ}
    (ht : t ∈ Ioo (left d.b) (right d.b)) :
    (∫ z : E, ‖(jet d k t (x,z)).2‖^2 ∂stdGaussian E) =
      ∫ y : E, ‖(fixedData d x).positionJet k t y‖^2
        ∂(fixedData d x).positionMeasure := by
  simp_rw [jet_snd_eq_referencePositionJet d k x _ ht]
  have hp := referenceInput_measurePreserving d x
  have hc : Continuous (fun y : E => ‖(fixedData d x).positionJet k t y‖^2) :=
    (((fixedData d x).continuous_positionJet k).comp
      (continuous_const.prodMk continuous_id)).norm.pow 2
  rw [← hp.map_eq]
  exact (integral_map hp.measurable.aemeasurable hc.aestronglyMeasurable).symm

end AcceleratedLogConcave.Numerics.ConditionalSmoothing
