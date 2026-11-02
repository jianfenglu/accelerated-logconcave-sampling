import AcceleratedLogConcave.Tensor.ActualCoefficientSplitBounds

noncomputable section
open scoped ContDiff RealInnerProductSpace
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability

private theorem variance_sqrt_power_bound {v : ℝ} (hv : 0 < v) (m : ℕ) :
    (v^(m+1))⁻¹ * (Real.sqrt (2*v))^(m+2) ≤
      (2:ℝ)^(m+2) * ((Real.sqrt v)^m)⁻¹ := by
  have hR : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hs : Real.sqrt (2*v) ≤ 2*Real.sqrt v := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_right (by norm_num : Real.sqrt 2 ≤ (2:ℝ)) hR.le
  have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.sqrt_nonneg _) hs (m+2))
    (inv_nonneg.mpr (pow_pos hv (m+1)).le)
  apply hh.trans_eq
  have hp : v^(m+1) = (Real.sqrt v)^m * (Real.sqrt v)^(m+2) := by
    calc
      v^(m+1) = ((Real.sqrt v)^2)^(m+1) := by rw [Real.sq_sqrt hv.le]
      _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; omega
  rw [hp,mul_pow]
  field_simp [hR.ne']

/-- Explicit source coefficient budget with c0=2 for every spatial derivative
of the literal J_(n+1) field, with R=sqrt(1-rho²). -/
theorem normalizedJetDerivativeCoefficient_budget {D : ℕ}
    (d : Conditional.PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (n j : ℕ) {t : ℝ} (ht : -1 < t ∧ t < 1) (y : EuclideanSpace ℝ (Fin D))
    (S : Finset ((Fin j ⊕ Fin (n+1)) ⊕ Unit)) (hS : NontrivialSplit S) :
    splitNorm D S (normalizedJetDerivativeCoefficient d.F d.x d.ell d.r t n j y) ≤
      (2:ℝ)^(n+2+j) * ((n+2+j).factorial : ℝ) *
        ((Real.sqrt (Conditional.conditionalVariance t))^(n+j))⁻¹ := by
  have hv := Conditional.conditionalVariance_pos ht.1 ht.2
  have ht1 : |t| ≤ 1 := (abs_lt.mpr ht).le
  have hf : (1:ℝ) ≤ ((n+1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (n+1)
  have hfac : 0 ≤ (((n+1).factorial : ℝ)⁻¹) := inv_nonneg.mpr (by positivity)
  have hi : (((n+1).factorial : ℝ)⁻¹) ≤ 1 := (inv_le_one₀ (by positivity)).mpr hf
  have hsmall : |t|^j * (((n+1).factorial : ℝ)⁻¹) ≤ 1 :=
    (mul_le_mul_of_nonneg_right (pow_le_one₀ (abs_nonneg t) ht1) hfac).trans (by simpa using hi)
  have h0 := normalizedJetDerivativeCoefficient_splitNorm_le d n j ht y S hS
  have hp := variance_sqrt_power_bound hv (n+j)
  have hfact : (((n+j+1).factorial : ℝ)) ≤ ((n+2+j).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : n+j+1 ≤ n+2+j)
  have he : j+(n+1) = n+j+1 := by omega
  have ha : n+2+j = n+j+2 := by omega
  rw [he] at h0
  rw [ha] at hfact ⊢
  calc
    _ ≤ (|t|^j * ((n+1).factorial : ℝ)⁻¹) *
        ((Conditional.conditionalVariance t ^ (n+j+1))⁻¹ *
          (((n+j+1).factorial : ℝ) * (Real.sqrt (2*Conditional.conditionalVariance t))^(n+j+2))) := by
      convert h0 using 1; ring
    _ ≤ 1 * ((Conditional.conditionalVariance t ^ (n+j+1))⁻¹ *
          (((n+j+1).factorial : ℝ) * (Real.sqrt (2*Conditional.conditionalVariance t))^(n+j+2))) :=
      mul_le_mul_of_nonneg_right hsmall (by positivity)
    _ = ((n+j+1).factorial : ℝ) *
        ((Conditional.conditionalVariance t ^ (n+j+1))⁻¹ *
          (Real.sqrt (2*Conditional.conditionalVariance t))^(n+j+2)) := by ring
    _ ≤ ((n+j+1).factorial : ℝ) *
        ((2:ℝ)^(n+j+2) * ((Real.sqrt (Conditional.conditionalVariance t))^(n+j))⁻¹) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ ((n+j+2).factorial : ℝ) *
        ((2:ℝ)^(n+j+2) * ((Real.sqrt (Conditional.conditionalVariance t))^(n+j))⁻¹) :=
      mul_le_mul_of_nonneg_right hfact (by positivity)
    _ = _ := by ring

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
