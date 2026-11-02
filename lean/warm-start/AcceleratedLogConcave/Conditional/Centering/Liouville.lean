import AcceleratedLogConcave.Conditional.Centering.Jacobi
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Weighted Liouville conservation along a trajectory. The divergence equation
is needed only on that trajectory, so a cutoff field need not preserve the
measure away from the region where the cutoff equals one. -/
noncomputable section
open Set MeasureTheory
namespace AcceleratedLogConcave.Conditional.Centering
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The weighted Jacobian has zero derivative when the weighted divergence
vanishes along the trajectory. -/
theorem hasDerivAt_density_det_zero {X : ℝ → E} {J : ℝ → E →L[ℝ] E}
    {p : E → ℝ} {v : E} {A : E →L[ℝ] E} {dp : E →L[ℝ] ℝ} {t : ℝ}
    (hX : HasDerivAt X v t) (hJ : HasDerivAt J (A.comp (J t)) t)
    (hp : HasFDerivAt p dp (X t))
    (hdiv : dp v + p (X t) * LinearMap.trace ℝ E A.toLinearMap = 0) :
    HasDerivAt (fun s => p (X s) * (J s).det) 0 t := by
  have h := (hp.comp_hasDerivAt t hX).mul (hasDerivAt_det_of_left_ode hJ)
  convert h using 1
  · rfl
  · change 0 = dp v * (J t).det + p (X t) *
      (LinearMap.trace ℝ E A.toLinearMap * (J t).det)
    linear_combination -(J t).det * hdiv

/-- Conservation includes both closed endpoints; differentiability is required
only in the interior. -/
theorem density_det_eq_of_weighted_divergence {X : ℝ → E}
    {J : ℝ → E →L[ℝ] E} {p : E → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn (fun s => p (X s) * (J s).det) (Icc a b))
    (h : ∀ t ∈ Ioo a b, ∃ (v : E) (A : E →L[ℝ] E) (dp : E →L[ℝ] ℝ),
      HasDerivAt X v t ∧ HasDerivAt J (A.comp (J t)) t ∧
      HasFDerivAt p dp (X t) ∧
      dp v + p (X t) * LinearMap.trace ℝ E A.toLinearMap = 0) :
    p (X b) * (J b).det = p (X a) * (J a).det := by
  have hd (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (fun s => p (X s) * (J s).det) 0 t := by
    obtain ⟨v, A, dp, hX, hJ, hp, hdiv⟩ := h t ht
    exact hasDerivAt_density_det_zero hX hJ hp hdiv
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hc hd
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume a b)
  simpa using (sub_eq_zero.mp (by simpa using hi.symm))
end AcceleratedLogConcave.Conditional.Centering
