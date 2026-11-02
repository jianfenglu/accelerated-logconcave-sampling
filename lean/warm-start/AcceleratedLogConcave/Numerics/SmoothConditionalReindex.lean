import AcceleratedLogConcave.Numerics.SmoothConditionalCoordinates

/-! Explicit coordinate transport of the frozen-center conditional ODE and
its time jets. Gaussian inputs are transported by the same linear isometry. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Numerics.ConditionalSmoothing
open Conditional Analysis.PositiveVarianceSlab OAI.LogConcaveSampling.GlobalODE
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
local notation "E" => EuclideanSpace ℝ ι
local notation "V" => EuclideanSpace ℝ κ

def reindexData (d : SamplingCenterLp.Data ι) (e : E ≃ₗᵢ[ℝ] V) : SamplingCenterLp.Data κ where
  F := fun z => d.F (e.symm z)
  hF := d.hF.comp e.symm.toContinuousLinearEquiv.contDiff
  ell := d.ell
  hell := d.hell
  hlo := by
    intro z v
    rw [hessian_comp_isometry e.symm d.hF]
    exact d.hlo _ _
  hup := by
    intro z v
    rw [hessian_comp_isometry e.symm d.hF]
    simpa only [e.symm.norm_map] using d.hup (e.symm z) (e.symm v)
  r := d.r
  hr := d.hr
  b := d.b
  hb := d.hb
  hb1 := d.hb1

theorem clippedVelocity_reindex (d : SamplingCenterLp.Data ι) (e : E ≃ₗᵢ[ℝ] V)
    (x z : E) (t : ℝ) :
    (fixedData (reindexData d e) (e x)).clippedVelocity t (e z) =
      e ((fixedData d x).clippedVelocity t z) := by
  change (-d.r) • Conditional.conditionalMean (fun y => d.F (e.symm y)) (e x) d.r _ (e z) =
    e ((-d.r) • Conditional.conditionalMean d.F x d.r _ z)
  rw [conditionalMean_map_isometry e d.hF, map_smul]
  rfl

theorem jointPath_snd_reindex (d : SamplingCenterLp.Data ι) (e : E ≃ₗᵢ[ℝ] V)
    (x z : E) (t : ℝ) :
    e ((jointPath d t (x,z)).2) = (jointPath (reindexData d e) t (e x,e z)).2 := by
  let fd := fixedData d x
  let gd := fixedData (reindexData d e) (e x)
  let X : ℝ → V := fun u => e (flow fd.lipschitz_clippedVelocity
    fd.continuous_clippedVelocity (start d) z u)
  have hX : Continuous X := e.continuous.comp (flow_continuous _ _ _ _)
  have hdX (u : ℝ) (hu : u ∈ Icc (left d.b) (right d.b)) :
      HasDerivWithinAt X (gd.clippedVelocity u (X u)) (Icc (left d.b) (right d.b)) u := by
    have hh := e.toContinuousLinearEquiv.hasFDerivAt.comp_hasDerivWithinAt u
      (flow_deriv fd.lipschitz_clippedVelocity fd.continuous_clippedVelocity (start d) z u hu)
    dsimp only [X, gd]
    rw [clippedVelocity_reindex]
    exact hh
  have hh := trajectory_dist gd.lipschitz_clippedVelocity hX.continuousOn hdX
    (flow_continuous gd.lipschitz_clippedVelocity gd.continuous_clippedVelocity
      (start (reindexData d e)) (e z)).continuousOn
    (flow_deriv gd.lipschitz_clippedVelocity gd.continuous_clippedVelocity
      (start (reindexData d e)) (e z))
    (start (reindexData d e)) ⟨time d t,time_mem d t⟩
  have hinit : X (start (reindexData d e)) = e z := by
    change e (flow fd.lipschitz_clippedVelocity fd.continuous_clippedVelocity (start d) z (start d)) = _
    rw [flow_initial]
  rw [hinit, flow_initial, dist_self, zero_mul, dist_le_zero] at hh
  rw [jointPath_eq_fixed, jointPath_eq_fixed]
  exact hh

theorem jet_snd_reindex (d : SamplingCenterLp.Data ι) (e : E ≃ₗᵢ[ℝ] V)
    (k : ℕ) (x z : E) {t : ℝ} (ht : t ∈ Ioo (left d.b) (right d.b)) :
    e ((jet d k t (x,z)).2) = (jet (reindexData d e) k t (e x,e z)).2 := by
  have hleft := Analysis.iteratedDeriv_eq_of_finite_ladder k
    (fun q u => e ((jet d q u (x,z)).2)) isOpen_Ioo
    (fun q _ u hu => e.toContinuousLinearEquiv.hasFDerivAt.comp_hasDerivAt u
      (hasDerivAt_jet d q hu (x,z)).snd) ht
  have hright := Analysis.iteratedDeriv_eq_of_finite_ladder k
    (fun q u => (jet (reindexData d e) q u (e x,e z)).2) isOpen_Ioo
    (fun q _ u hu => (hasDerivAt_jet (reindexData d e) q hu (e x,e z)).snd) ht
  have he : (fun u => e ((jet d 0 u (x,z)).2)) =
      (fun u => (jet (reindexData d e) 0 u (e x,e z)).2) := by
    funext u
    exact jointPath_snd_reindex d e x z u
  rw [← hleft, ← hright, he]

theorem integral_gaussian_jet_sq_reindex (d : SamplingCenterLp.Data ι) (e : E ≃ₗᵢ[ℝ] V)
    (k : ℕ) (x : E) {t : ℝ} (ht : t ∈ Ioo (left d.b) (right d.b)) :
    (∫ z : E, ‖(jet d k t (x,z)).2‖^2 ∂stdGaussian E) =
      ∫ z : V, ‖(jet (reindexData d e) k t (e x,z)).2‖^2 ∂stdGaussian V := by
  have hc : Continuous (fun z : V => ‖(jet (reindexData d e) k t (e x,z)).2‖^2) :=
    (((continuous_jet (reindexData d e) k).comp
      (continuous_const.prodMk (continuous_const.prodMk continuous_id))).snd.norm).pow 2
  rw [← stdGaussian_map e, integral_map e.continuous.measurable.aemeasurable hc.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [← jet_snd_reindex d e k x z ht, e.norm_map]

end AcceleratedLogConcave.Numerics.ConditionalSmoothing
