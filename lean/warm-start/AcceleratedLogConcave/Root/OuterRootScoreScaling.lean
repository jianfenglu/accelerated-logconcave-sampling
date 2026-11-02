import AcceleratedLogConcave.Root.OuterRootOriginalData

/-! SOURCE-ONLY. Exact score units for the normalized outer root. Scaling is
proved on the literal Gaussian posterior before taking its primitive mean. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Root.OuterRootScoreScaling
open OuterRootOriginalData
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Both primitive posteriors have exactly the same density on the same z. -/
theorem primitiveLaw_scaled (V : E → ℝ) (h r : ℝ) (x : E) :
    Gibbs.primitiveLaw (potential V h) x r =
      Gibbs.primitiveLaw V (Real.sqrt h • x) (Real.sqrt h*r) := by
  unfold Gibbs.primitiveLaw
  congr 1
  funext z
  simp only [potential, smul_add, smul_smul]

/-- The uncentered primitive reply scales by sqrt(h), not h or rF. -/
theorem primitiveMean_scaled {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (h r : ℝ) (x : E) :
    Gibbs.primitiveMean (potential V h) x r =
      Real.sqrt h • Gibbs.primitiveMean V (Real.sqrt h • x) (Real.sqrt h*r) := by
  have hg (z : E) : gradient (potential V h) z =
      Real.sqrt h • gradient V (Real.sqrt h • z) := by
    change gradient (fun z : E => V (Real.sqrt h • z)) z = _
    simpa only [potential, zero_add] using Gibbs.primitive_gradient_affine_comp
      (hV.differentiable (by norm_num)) (0 : E) (Real.sqrt h) z
  unfold Gibbs.primitiveMean
  rw [primitiveLaw_scaled]
  simp_rw [hg, smul_add, smul_smul]
  rw [integral_smul]

/-- Consequently the scaled root reply is the actual physical heat score at
variance h*r². No score-identification premise is accepted. -/
theorem primitiveMean_eq_physical_heatScore {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    {h r : ℝ} (hh : 0 < h) (hr : 0 < r)
    (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ V) z v v)
    (hup : ∀ z v, fderiv ℝ (fderiv ℝ V) z v v ≤ ‖v‖^2) (x : E) :
    Gibbs.primitiveMean (potential V h) x r =
      Real.sqrt h • gradient (Gibbs.heatPotential V (h*r^2)) (Real.sqrt h • x) := by
  rw [primitiveMean_scaled hV,
    Gibbs.primitive_mean_eq_heat_score hV hlo
      (show ∀ z v, fderiv ℝ (fderiv ℝ V) z v v ≤ (1:ℝ)*‖v‖^2 by simpa using hup)
      (mul_pos (Real.sqrt_pos.mpr hh) hr)]
  rw [mul_pow, Real.sq_sqrt hh.le]

end AcceleratedLogConcave.Root.OuterRootScoreScaling
