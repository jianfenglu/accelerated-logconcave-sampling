import AcceleratedLogConcave.Kinetic.ReferenceFlow.ExtendedDrift

/-! Exact coordinate changes of actual complete ODE flows. -/
noncomputable section
open Set Function
open scoped NNReal
open OAI.LogConcaveSampling.GlobalODE
namespace AcceleratedLogConcave.Kinetic
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def conjugateDrift (A : X ≃L[ℝ] Y) (v : ℝ → X → X) (t : ℝ) (y : Y) : Y :=
  A (v t (A.symm y))

theorem conjugateDrift_continuous (A : X ≃L[ℝ] Y) {v : ℝ → X → X}
    (hv : Continuous (uncurry v)) : Continuous (uncurry (conjugateDrift A v)) :=
  A.continuous.comp (hv.comp (continuous_fst.prodMk (A.symm.continuous.comp continuous_snd)))

def conjugateLipschitzConstant (A : X ≃L[ℝ] Y) (K : ℝ≥0) : ℝ≥0 :=
  ‖A.toContinuousLinearMap‖₊ * (K * ‖A.symm.toContinuousLinearMap‖₊)

theorem conjugateDrift_lipschitz (A : X ≃L[ℝ] Y) {v : X → X} {K : ℝ≥0}
    (hv : LipschitzWith K v) :
    LipschitzWith (conjugateLipschitzConstant A K) (fun y => A (v (A.symm y))) :=
  A.toContinuousLinearMap.lipschitzWith.comp (hv.comp A.symm.toContinuousLinearMap.lipschitzWith)

def conjugateDriftDerivative (A : X ≃L[ℝ] Y) (D : ℝ → X → X →L[ℝ] X)
    (t : ℝ) (y : Y) : Y →L[ℝ] Y :=
  A.toContinuousLinearMap.comp ((D t (A.symm y)).comp A.symm.toContinuousLinearMap)

theorem conjugateDriftDerivative_continuous (A : X ≃L[ℝ] Y)
    {D : ℝ → X → X →L[ℝ] X} (hD : Continuous (uncurry D)) :
    Continuous (uncurry (conjugateDriftDerivative A D)) :=
  continuous_const.clm_comp ((hD.comp
    (continuous_fst.prodMk (A.symm.continuous.comp continuous_snd))).clm_comp continuous_const)

theorem conjugateDrift_hasFDerivAt (A : X ≃L[ℝ] Y)
    {v : ℝ → X → X} {D : ℝ → X → X →L[ℝ] X}
    (hd : ∀ t x, HasFDerivAt (v t) (D t x) x) (t : ℝ) (y : Y) :
    HasFDerivAt (conjugateDrift A v t) (conjugateDriftDerivative A D t y) y :=
  A.hasFDerivAt.comp y ((hd t (A.symm y)).comp y A.symm.hasFDerivAt)

variable [CompleteSpace X] [CompleteSpace Y] {a b : ℝ}
  (A : X ≃L[ℝ] Y) {v : ℝ → X → X} (hv : Continuous (uncurry v))
  {K : ℝ≥0} (hL : ∀ t ∈ Icc a b, LipschitzWith K (v t))

/-- The coordinate-transformed ODE is exactly the conjugate flow. -/
theorem flow_conjugateDrift (s t : Icc a b) (y : Y) :
    flow (fun u hu => conjugateDrift_lipschitz A (hL u hu))
      (conjugateDrift_continuous A hv) s y t = A (flow hL hv s (A.symm y) t) := by
  have hd (u : ℝ) (hu : u ∈ Icc a b) :
      HasDerivWithinAt (fun q => A (flow hL hv s (A.symm y) q))
        (conjugateDrift A v u (A (flow hL hv s (A.symm y) u))) (Icc a b) u := by
    simp only [conjugateDrift, A.symm_apply_apply]
    exact A.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt u
      (flow_deriv hL hv s (A.symm y) u hu)
  have hh := trajectory_dist (fun u hu => conjugateDrift_lipschitz A (hL u hu))
    (flow_continuous (fun u hu => conjugateDrift_lipschitz A (hL u hu))
      (conjugateDrift_continuous A hv) s y).continuousOn
    (flow_deriv (fun u hu => conjugateDrift_lipschitz A (hL u hu))
      (conjugateDrift_continuous A hv) s y)
    (A.continuous.comp (flow_continuous hL hv s (A.symm y))).continuousOn hd s t
  have hi := flow_initial (fun u hu => conjugateDrift_lipschitz A (hL u hu))
    (conjugateDrift_continuous A hv) s y
  rw [hi] at hh
  simpa only [Function.comp_apply, flow_initial, A.apply_symm_apply, dist_self, zero_mul, dist_le_zero] using hh

end AcceleratedLogConcave.Kinetic
