import AcceleratedLogConcave.Conditional.Flow.ExtendedJets
import AcceleratedLogConcave.Conditional.Flow.Restriction
import AcceleratedLogConcave.Conditional.Stein.Transport

/-! Exact agreement with the original source transport, including endpoints.
The two time-clipped vector fields are compared only on the common slab,
where uniqueness identifies every trajectory for every initial input. -/
noncomputable section
open Set Function
open scoped ContDiff Topology NNReal
namespace AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
open Analysis.PositiveVarianceSlab Analysis.ODEJet
open OAI.LogConcaveSampling.GlobalODE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (d : PositiveVarianceFlowData E)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem source_subset_construction : Icc 0 d.b ⊆ Icc (left d.b) (right d.b) :=
  fun _ ht => ⟨(source_subset d.hb0 d.hb1 ht).1.le, (source_subset d.hb0 d.hb1 ht).2.le⟩

theorem flow_eq_source (s t : Icc 0 d.b) (y : E) :
    flow d.lipschitz_clippedVelocity d.continuous_clippedVelocity
      ⟨s, d.source_subset_construction s.2⟩ y t =
      convexProbabilityFlow d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0
        (by norm_num) d.hb1 s y t := by
  exact (meanProbabilityFlow_eq_on_subinterval d.hb0 d.interval_le
    d.source_subset_construction d.r (conditionalMean d.F d.x d.r)
    (continuousOn_conditionalMean d.hF d.hlo d.hhi d.x d.r (by norm_num) d.hb1)
    d.continuous_mean
    (fun u hu => lipschitzWith_conditionalMean d.hF d.hell d.hlo d.hhi d.x d.hr
      (by linarith [hu.1]) (hu.2.trans_lt d.hb1)) d.lipschitz_mean s t y).symm

theorem state_snd_eq_source {t : ℝ} (ht : t ∈ Icc 0 d.b) (y : E) :
    (d.state t y).snd = transportedJacobian d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 t y := by
  have ht' := d.source_subset_construction ht
  have hf : (fun z => flow d.lipschitz_clippedVelocity d.continuous_clippedVelocity
      (projIcc (left d.b) (right d.b) d.interval_le t) z d.reference) =
      (forwardProbabilityTransport d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 t : E → E) := by
    funext z
    change flow d.lipschitz_clippedVelocity d.continuous_clippedVelocity
      (projIcc (left d.b) (right d.b) d.interval_le t) z d.b =
      convexProbabilityFlow d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0
        (by norm_num) d.hb1 (projIcc 0 d.b d.hb0 t) z d.b
    rw [projIcc_of_mem d.interval_le ht', projIcc_of_mem d.hb0 ht]
    exact d.flow_eq_source ⟨t, ht⟩ ⟨d.b, d.hb0, le_rfl⟩ z
  have hb : flow d.lipschitz_clippedVelocity d.continuous_clippedVelocity d.reference y
      (projIcc (left d.b) (right d.b) d.interval_le t) =
      backwardProbabilityTransport d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 t y := by
    rw [backwardProbabilityTransport_eq_flow, projIcc_of_mem d.interval_le ht',
      projIcc_of_mem d.hb0 ht]
    exact d.flow_eq_source ⟨d.b, d.hb0, le_rfl⟩ ⟨t, ht⟩ y
  change fderiv ℝ (fun z => flow d.lipschitz_clippedVelocity d.continuous_clippedVelocity
      (projIcc (left d.b) (right d.b) d.interval_le t) z d.reference)
      (flow d.lipschitz_clippedVelocity d.continuous_clippedVelocity d.reference y
        (projIcc (left d.b) (right d.b) d.interval_le t)) = _
  rw [hf, hb]
  rfl

theorem jet_zero_snd_eq_source {t : ℝ} (ht : t ∈ Icc 0 d.b) (y : E) :
    (d.jet 0 t y).snd = transportedJacobian d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 t y := by
  rw [jet, stateJet, d.time_eq (d.source_subset_construction ht)]
  exact d.state_snd_eq_source ht y

@[simp] theorem jet_zero_snd_reference (y : E) :
    (d.jet 0 d.b y).snd = ContinuousLinearMap.id ℝ E := by
  rw [d.jet_zero_snd_eq_source ⟨d.hb0, le_rfl⟩, transportedJacobian_terminal]

end AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
