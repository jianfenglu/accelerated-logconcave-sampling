import AcceleratedLogConcave.Conditional.Flow.CoupledPolynomial
import AcceleratedLogConcave.Conditional.Flow.Construction
import AcceleratedLogConcave.Conditional.JetBasics
import AcceleratedLogConcave.Conditional.Stein.ReferenceState

/-! The actual enlarged-slab flow and its actual inverse-flow derivative.
The reference time b is interior to the construction slab. Clipping is only
at the outer construction endpoints; the requested source neighborhood lies
strictly inside them. No coupled-flow existence premise is introduced. -/
noncomputable section
open Set Function
open scoped ContDiff Topology NNReal
namespace AcceleratedLogConcave.Conditional
open Analysis.PositiveVarianceSlab Analysis.CoupledVelocityPolynomial
open OAI.LogConcaveSampling.GlobalODE

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure PositiveVarianceFlowData where
  F : E → ℝ
  hF : ContDiff ℝ 2 F
  ell : ℝ
  hell : 0 ≤ ell
  hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w
  hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ ell * ‖w‖ ^ 2
  x : E
  r : ℝ
  hr : 0 < r
  b : ℝ
  hb0 : 0 ≤ b
  hb1 : b < 1

namespace PositiveVarianceFlowData
variable {E} (d : PositiveVarianceFlowData E)

theorem interval_le : left d.b ≤ right d.b := by
  dsimp [left, right]
  linarith

def reference : Icc (left d.b) (right d.b) :=
  ⟨d.b, (source_subset d.hb0 d.hb1 ⟨d.hb0, le_rfl⟩).1.le,
    (source_subset d.hb0 d.hb1 ⟨d.hb0, le_rfl⟩).2.le⟩

def time (t : ℝ) : ℝ := projIcc (left d.b) (right d.b) d.interval_le t

theorem time_mem (t : ℝ) : d.time t ∈ Icc (left d.b) (right d.b) :=
  (projIcc (left d.b) (right d.b) d.interval_le t).2

theorem time_eq {t : ℝ} (ht : t ∈ Icc (left d.b) (right d.b)) : d.time t = t := by
  simp only [time, projIcc_of_mem d.interval_le ht]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem continuous_mean :
    ContinuousOn (uncurry (conditionalMean d.F d.x d.r))
      (Icc (left d.b) (right d.b) ×ˢ (univ : Set E)) :=
  (contDiffOn_conditionalMean d.hF d.hlo d.hhi d.x d.r).continuousOn.mono
    (fun _ hp => construction_subset d.hb0 d.hb1 hp.1)

theorem lipschitz_mean (t : ℝ) (ht : t ∈ Icc (left d.b) (right d.b)) :
    LipschitzWith ⟨d.r * d.ell, mul_nonneg d.hr.le d.hell⟩
      (conditionalMean d.F d.x d.r t) :=
  lipschitzWith_conditionalMean d.hF d.hell d.hlo d.hhi d.x d.hr
    (construction_subset d.hb0 d.hb1 ht).1 (construction_subset d.hb0 d.hb1 ht).2

def clippedVelocity : ℝ → E → E :=
  clippedProbabilityVelocity d.interval_le d.r (conditionalMean d.F d.x d.r)

theorem continuous_clippedVelocity : Continuous (uncurry d.clippedVelocity) :=
  clippedProbabilityVelocity_continuous d.interval_le d.r d.continuous_mean

theorem lipschitz_clippedVelocity (t : ℝ) (_ht : t ∈ Icc (left d.b) (right d.b)) :
    LipschitzWith (‖d.r‖₊ * ⟨d.r * d.ell, mul_nonneg d.hr.le d.hell⟩)
      (d.clippedVelocity t) :=
  clippedProbabilityVelocity_lipschitz d.interval_le d.r d.lipschitz_mean t

def clippedDerivative (t : ℝ) (y : E) : E →L[ℝ] E :=
  (-d.r * d.time t) • firstScaledJet d.F d.x d.r (d.time t) y

theorem continuous_clippedDerivative : Continuous (uncurry d.clippedDerivative) := by
  have ht : Continuous d.time := continuous_subtype_val.comp continuous_projIcc
  have hu := (contDiffOn_firstScaledJet_natural d.hF d.hlo d.hhi d.x d.r).continuousOn
  have hc : Continuous (fun p : ℝ × E => firstScaledJet d.F d.x d.r (d.time p.1) p.2) :=
    hu.comp_continuous ((ht.comp continuous_fst).prodMk continuous_snd)
      (fun p => construction_subset d.hb0 d.hb1 (d.time_mem p.1))
  exact (continuous_const.mul (ht.comp continuous_fst)).smul hc

theorem hasFDerivAt_clippedVelocity (t : ℝ) (y : E) :
    HasFDerivAt (d.clippedVelocity t) (d.clippedDerivative t y) y := by
  have hp := construction_subset d.hb0 d.hb1 (d.time_mem t)
  have hd := ((contDiff_one_conditionalMean d.hF d.hlo d.hhi d.x d.r hp.1 hp.2).differentiable_one y).hasFDerivAt.const_smul (-d.r)
  rw [fderiv_conditionalMean_eq_smul_firstScaledJet d.hF d.hlo d.hhi d.x d.r hp.1 hp.2,
    smul_smul] at hd
  exact hd

def state (t : ℝ) (y : E) : CoupledState E :=
  flowReferenceState d.interval_le d.continuous_clippedVelocity
    d.lipschitz_clippedVelocity d.reference t y

/-- Ordinary differentiation is used at every interior probability time,
including zero and the fixed reference b. -/
theorem hasDerivAt_state {t : ℝ} (ht : t ∈ Ioo (left d.b) (right d.b)) (y : E) :
    HasDerivAt (fun u => d.state u y)
      (conditionalCoupledVelocity d.F d.x d.r (t, d.state t y)) t := by
  have hh := hasDerivAt_flowReferenceState d.interval_le d.continuous_clippedVelocity
    d.lipschitz_clippedVelocity d.continuous_clippedDerivative d.hasFDerivAt_clippedVelocity
    d.reference ht y
  have ht' : t ∈ Icc (left d.b) (right d.b) := ⟨ht.1.le, ht.2.le⟩
  change HasDerivAt (fun u => d.state u y)
    (referenceStateVelocity d.clippedVelocity d.clippedDerivative (t, d.state t y)) t at hh
  have he : referenceStateVelocity d.clippedVelocity d.clippedDerivative (t, d.state t y) =
      conditionalCoupledVelocity d.F d.x d.r (t, d.state t y) := by
    dsimp [referenceStateVelocity, conditionalCoupledVelocity, velocity,
      clippedVelocity, clippedProbabilityVelocity, meanVelocity, clippedDerivative]
    rw [d.time_eq ht', projIcc_of_mem d.interval_le ht']
    simp only [ContinuousLinearMap.comp_smul, ← neg_smul, neg_mul, neg_neg]
  rw [he] at hh
  exact hh

theorem state_joint_continuous :
    Continuous (fun p : E × Icc (left d.b) (right d.b) => d.state p.2 p.1) :=
  flowReferenceState_joint_continuous d.interval_le d.continuous_clippedVelocity
    d.lipschitz_clippedVelocity d.continuous_clippedDerivative d.hasFDerivAt_clippedVelocity
    d.reference

theorem exists_state_linear_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (left d.b) (right d.b), ∀ y : E,
      ‖d.state t y‖ ≤ C * (1 + ‖y‖) :=
  exists_flowReferenceState_linear_bound d.interval_le d.continuous_clippedVelocity
    d.lipschitz_clippedVelocity d.reference

end PositiveVarianceFlowData
end AcceleratedLogConcave.Conditional
