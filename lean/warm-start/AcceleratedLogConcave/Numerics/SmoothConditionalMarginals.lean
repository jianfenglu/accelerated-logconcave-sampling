import AcceleratedLogConcave.Numerics.SmoothConditionalSeedDisintegration

/-! Exact fixed-center posterior marginals for the zero-initialized actual
conditional path, and transfer of its state-jet moments to those marginals.
No quantitative estimate is assumed or asserted. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace AcceleratedLogConcave.Numerics.ConditionalSmoothing
open Conditional Analysis.PositiveVarianceSlab Analysis.CoupledVelocityPolynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι
variable (d : SamplingCenterLp.Data ι)

theorem path_measurePreserving (x : E) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    MeasurePreserving (SamplingCenterLp.path d x t) (stdGaussian E)
      (interpolationLaw d.F x d.r t) := by
  have ht1 := ht.2.trans_lt d.hb1
  have hsub : Icc 0 t ⊆ Icc 0 d.b := fun _ hu => ⟨hu.1,hu.2.trans ht.2⟩
  have he : SamplingCenterLp.path d x t = fun y =>
      convexProbabilityFlow d.hF d.hell d.hlo d.hup x d.hr ht.1
        (by norm_num) ht1 ⟨0,le_rfl,ht.1⟩ y t := by
    funext y
    unfold SamplingCenterLp.path
    rw [SamplingFlowLp.sourcePath_eq d.hF d.hell d.hlo d.hup x d.hr d.hb d.hb1 ht]
    exact (meanProbabilityFlow_eq_on_subinterval ht.1 d.hb hsub d.r
      (Conditional.conditionalMean d.F x d.r)
      (continuousOn_conditionalMean d.hF d.hlo d.hup x d.r (by norm_num) ht1)
      (continuousOn_conditionalMean d.hF d.hlo d.hup x d.r (by norm_num) d.hb1)
      (fun u hu => lipschitzWith_conditionalMean d.hF d.hell d.hlo d.hup x d.hr
        (by linarith [hu.1]) (hu.2.trans_lt ht1))
      (fun u hu => lipschitzWith_conditionalMean d.hF d.hell d.hlo d.hup x d.hr
        (by linarith [hu.1]) (hu.2.trans_lt d.hb1))
      ⟨0,le_rfl,ht.1⟩ ⟨t,ht.1,le_rfl⟩ y).symm
  rw [he]
  have hp := convexProbabilityFlow_measurePreserving_le d.hF d.hell d.hlo d.hup
    x d.hr ht.1 (by norm_num) ht1
  rw [interpolationLaw_zero d.hF d.hlo] at hp
  exact hp

/-- The universal time-jet field at a fixed center and current position. -/
def fixedCenterJetField (k : ℕ) (t : ℝ) (x y : E) : E :=
  (Analysis.ODEJet.stateJet (openDomain (E × E)) (openVelocity d) k (t,(x,y))).2

omit [DecidableEq ι] in
theorem jet_eq_fixedCenterJetField (k : ℕ) (x z : E) {t : ℝ}
    (ht : t ∈ Icc 0 d.b) :
    (jet d k t (x,z)).2 = fixedCenterJetField d k t x (SamplingCenterLp.path d x t z) := by
  have ht' := source_subset d.hb d.hb1 ht
  unfold jet fixedCenterJetField
  rw [time_eq d ⟨ht'.1.le,ht'.2.le⟩]
  have he : jointPath d t (x,z) = (x,SamplingCenterLp.path d x t z) :=
    Prod.ext (jointPath_fst d t (x,z)) (jointPath_snd_eq_source d x z ht)
  rw [he]

omit [DecidableEq ι] in
theorem continuous_fixedCenterJetField (k : ℕ) (x : E) {t : ℝ}
    (ht : t ∈ Ioo (-1) 1) : Continuous (fixedCenterJetField d k t x) := by
  have h := (Analysis.ODEJet.contDiffOn_stateJet (isOpen_openDomain (E × E)).uniqueDiffOn
    (contDiffOn_openVelocity d) k).continuousOn.comp_continuous
      (show Continuous (fun y : E => (t,(x,y))) by fun_prop)
      (fun _ => ht)
  exact h.snd

/-- Exact Gaussian-to-local-posterior moment transfer at every source time,
including zero and the terminal endpoint. -/
theorem integral_jet_sq_eq_interpolation (k : ℕ) (x : E) {t : ℝ}
    (ht : t ∈ Icc 0 d.b) :
    (∫ z : E, ‖(jet d k t (x,z)).2‖^2 ∂stdGaussian E) =
      ∫ y : E, ‖fixedCenterJetField d k t x y‖^2 ∂interpolationLaw d.F x d.r t := by
  have hp := path_measurePreserving d x ht
  have hc := (continuous_fixedCenterJetField d k x
    (show t ∈ Ioo (-1) 1 from ⟨by linarith [ht.1],ht.2.trans_lt d.hb1⟩)).norm.pow 2
  simp_rw [jet_eq_fixedCenterJetField d k x _ ht]
  rw [← hp.map_eq]
  exact (integral_map hp.measurable.aemeasurable
    (show AEStronglyMeasurable (fun y => ‖fixedCenterJetField d k t x y‖^2)
      ((stdGaussian E).map (SamplingCenterLp.path d x t)) from hc.aestronglyMeasurable)).symm

end AcceleratedLogConcave.Numerics.ConditionalSmoothing

namespace AcceleratedLogConcave.Numerics.MeanResidualBridge
open MeanFlowLp AffineGraph ConditionalSmoothing
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

/-- The literal receiver's norm, expressed on the correct local posterior law
at its actual random center. This identity adds no numerical bound premise. -/
theorem norm_sq_iteratedDeriv_conditionalMean_eq_phase_interpolation
    (d : MeanFlowLp.Data ι m) (j : Fin m) (ρ : d.G.Kernel)
    (U : H d → ℝ → H d) (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U)
    (k : ℕ) {t : ℝ} (ht : t ∈ Icc 0 conditionalEnd) :
    ‖iteratedDeriv k ((curvesWithConditional d).conditionalMean d.G U 0 d.r j ρ) t‖^2 =
      (d.r*Real.sqrt (d.G.variance ρ))⁻¹^2 *
        ∫ p, ∫ y : E,
          ‖fixedCenterJetField (conditionalData d ρ) (k+1) t
            (conditionalPhaseCenter d j ρ p) y‖^2
              ∂Conditional.interpolationLaw d.F (conditionalPhaseCenter d j ρ p)
                (d.r*Real.sqrt (d.G.variance ρ)) t
              ∂KernelFlowLp.seedMeasure (kernelData d) := by
  rw [norm_sq_iteratedDeriv_conditionalMean_eq_phase_gaussian d j ρ U hu k ht]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with p
  exact integral_jet_sq_eq_interpolation (conditionalData d ρ) (k+1)
    (conditionalPhaseCenter d j ρ p) ht

end AcceleratedLogConcave.Numerics.MeanResidualBridge
