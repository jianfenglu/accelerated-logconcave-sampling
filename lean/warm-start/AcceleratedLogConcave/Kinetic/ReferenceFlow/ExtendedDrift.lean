import AcceleratedLogConcave.Kinetic.ReferenceFlow.Drift
import AcceleratedLogConcave.Kinetic.ReferenceFlow.MovingFrameCore

/-! Retaining an actual dormant coordinate in a complete flow. This identifies
the constructed full-space ODE with the product of the coupled flow and identity. -/
noncomputable section
open Set Function
open scoped NNReal
open OAI.LogConcaveSampling.GlobalODE
namespace AcceleratedLogConcave.Kinetic
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def extendDrift (v : ℝ → X → X) (t : ℝ) (z : X × Y) : X × Y := (v t z.1,0)

omit [NormedSpace ℝ X] [NormedSpace ℝ Y] in
theorem extendDrift_continuous {v : ℝ → X → X} (hv : Continuous (uncurry v)) :
    Continuous (uncurry (extendDrift (Y := Y) v)) :=
  (hv.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk continuous_const

omit [NormedSpace ℝ X] [NormedSpace ℝ Y] in
theorem extendDrift_lipschitz {v : X → X} {K : ℝ≥0} (hv : LipschitzWith K v) :
    LipschitzWith K (fun z : X × Y => (v z.1,(0:Y))) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
  exact (hv.dist_le_mul z.1 w.1).trans
    (mul_le_mul_of_nonneg_left (le_max_left _ _) K.coe_nonneg)

def extendDriftDerivative (D : ℝ → X → X →L[ℝ] X) (t : ℝ) (z : X × Y) :
    (X × Y) →L[ℝ] (X × Y) :=
  ((D t z.1).comp (ContinuousLinearMap.fst ℝ X Y)).prod 0

theorem extendDriftDerivative_continuous {D : ℝ → X → X →L[ℝ] X}
    (hD : Continuous (uncurry D)) :
    Continuous (uncurry (extendDriftDerivative (Y := Y) D)) := by
  exact (ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp
    (((hD.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).clm_comp
      continuous_const).prodMk continuous_const)

theorem extendDrift_hasFDerivAt {v : ℝ → X → X} {D : ℝ → X → X →L[ℝ] X}
    (hd : ∀ t x, HasFDerivAt (v t) (D t x) x) (t : ℝ) (z : X × Y) :
    HasFDerivAt (extendDrift v t) (extendDriftDerivative D t z) z :=
  ((hd t z.1).comp z (ContinuousLinearMap.fst ℝ X Y).hasFDerivAt).prodMk
    (hasFDerivAt_const (0:Y) z)

variable [CompleteSpace X] [CompleteSpace Y] {a b : ℝ}
  {v : ℝ → X → X} (hv : Continuous (uncurry v))
  {K : ℝ≥0} (hL : ∀ t ∈ Icc a b, LipschitzWith K (v t))

/-- The full flow fixes the dormant coordinate exactly. -/
theorem flow_extendDrift (s t : Icc a b) (z : X × Y) :
    flow (fun u hu => extendDrift_lipschitz (Y := Y) (hL u hu))
      (extendDrift_continuous hv) s z t = (flow hL hv s z.1 t,z.2) := by
  have hd (u : ℝ) (hu : u ∈ Icc a b) :
      HasDerivWithinAt (fun q => (flow hL hv s z.1 q,z.2))
        (extendDrift v u (flow hL hv s z.1 u,z.2)) (Icc a b) u :=
    (flow_deriv hL hv s z.1 u hu).prodMk (hasDerivWithinAt_const u (Icc a b) z.2)
  have hh := trajectory_dist (fun u hu => extendDrift_lipschitz (Y := Y) (hL u hu))
    (flow_continuous (fun u hu => extendDrift_lipschitz (Y := Y) (hL u hu))
      (extendDrift_continuous hv) s z).continuousOn
    (flow_deriv (fun u hu => extendDrift_lipschitz (Y := Y) (hL u hu))
      (extendDrift_continuous hv) s z)
    ((flow_continuous hL hv s z.1).prodMk continuous_const).continuousOn hd s t
  have hi := flow_initial (fun u hu => extendDrift_lipschitz (Y := Y) (hL u hu))
    (extendDrift_continuous (Y := Y) hv) s z
  rw [hi] at hh
  simpa only [flow_initial, Prod.mk.eta, dist_self, zero_mul, dist_le_zero] using hh

end AcceleratedLogConcave.Kinetic
