import AcceleratedLogConcave.Tensor.MaterialExpressionLp

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff ENNReal
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open Conditional Analysis Analysis.PositiveVarianceSlab MeasureTheory Set
variable {D : ℕ} (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))

/-- Literal rank-one finite expression expansion, with no dimension factor. -/
def materialVectorTermsTensor (ts : List (MaterialTerm 1)) (t : ℝ)
    (y : EuclideanSpace ℝ (Fin D)) : FinCoeff 1 D :=
  (ts.map (fun u => (u.coefficient*t^u.degree) •
    Expr.evaluate (coefficientEnvironment d.F d.x d.ell d.r t)
      (interpolationPotential d.F d.x d.r t) u.expression y)).sum

theorem materialVectorTermsTensor_apply (ts : List (MaterialTerm 1)) (t : ℝ)
    (y : EuclideanSpace ℝ (Fin D)) (a : Fin 1 → Fin D) :
    materialVectorTermsTensor d ts t y a = materialTermsValue d ts a (t,y) := by
  induction ts with
  | nil => rfl
  | cons u ts ih =>
    change (u.coefficient*t^u.degree)*materialExpressionValue d u.expression a (t,y) +
      materialVectorTermsTensor d ts t y a = _
    rw [ih]
    rfl

theorem actualVectorTerms_memLp (ts : List (MaterialTerm 1)) {t : ℝ}
    (ht : t ∈ Icc (left d.b) (right d.b)) :
    MemLp (materialVectorTermsTensor d ts t) 2 (interpolationLaw d.F d.x d.r t) := by
  induction ts with
  | nil => exact MemLp.zero
  | cons u ts ih =>
    exact ((actualExpression_memLp d u.expression ht).const_smul (u.coefficient*t^u.degree)).add ih

def actualVectorTermsLp (ts : List (MaterialTerm 1)) {t : ℝ}
    (ht : t ∈ Icc (left d.b) (right d.b)) :
    Lp (FinCoeff 1 D) 2 (interpolationLaw d.F d.x d.r t) :=
  (actualVectorTerms_memLp d ts ht).toLp _

theorem actualVectorTermsLp_cons (u : MaterialTerm 1) (ts : List (MaterialTerm 1)) {t : ℝ}
    (ht : t ∈ Icc (left d.b) (right d.b)) :
    actualVectorTermsLp d (u::ts) ht =
      (u.coefficient*t^u.degree) • actualExpressionLp d u.expression ht + actualVectorTermsLp d ts ht := rfl

theorem actualVectorTermsLp_norm_le (ts : List (MaterialTerm 1)) {t M : ℝ}
    (ht : t ∈ Icc (left d.b) (right d.b)) (htabs : |t|≤1)
    (hM : ∀ u ∈ ts, ‖actualExpressionLp d u.expression ht‖ ≤ M) :
    ‖actualVectorTermsLp d ts ht‖ ≤ materialMass ts*M := by
  induction ts with
  | nil =>
    have hz : actualVectorTermsLp d [] ht = 0 := rfl
    rw [hz]
    simp [materialMass]
  | cons u ts ih =>
    have hu := hM u (by simp)
    have hs := ih (fun v hv => hM v (by simp [hv]))
    have hc : ‖u.coefficient*t^u.degree‖ ≤ |u.coefficient| := by
      rw [Real.norm_eq_abs,abs_mul,abs_pow]
      have hp : |t|^u.degree ≤ 1 := pow_le_one₀ (abs_nonneg t) htabs
      nlinarith [abs_nonneg u.coefficient]
    rw [actualVectorTermsLp_cons]
    calc
      _ ≤ ‖(u.coefficient*t^u.degree) • actualExpressionLp d u.expression ht‖ +
          ‖actualVectorTermsLp d ts ht‖ := norm_add_le _ _
      _ ≤ |u.coefficient| * M+materialMass ts*M := by
        rw [norm_smul]
        exact add_le_add (mul_le_mul hc hu (norm_nonneg _) (abs_nonneg _)) hs
      _ = materialMass (u::ts)*M := by simp [materialMass]; ring

/-- Only the pending whole-expression RMS estimate is a premise; all
measurability and L2 integrability come from original flow data. -/
theorem actualVectorTerms_integral_norm_sq_le (ts : List (MaterialTerm 1)) {t M : ℝ}
    (ht : t ∈ Icc (left d.b) (right d.b)) (htabs : |t|≤1) (hM0 : 0≤M)
    (hM : ∀ u ∈ ts,
      (∫ y, ‖Expr.evaluate (coefficientEnvironment d.F d.x d.ell d.r t)
        (interpolationPotential d.F d.x d.r t) u.expression y‖^2
        ∂interpolationLaw d.F d.x d.r t) ≤ M^2) :
    (∫ y, ‖materialVectorTermsTensor d ts t y‖^2 ∂interpolationLaw d.F d.x d.r t) ≤
      (materialMass ts*M)^2 := by
  have hnorm : ∀ u ∈ ts, ‖actualExpressionLp d u.expression ht‖ ≤ M := by
    intro u hu
    have hh := hM u hu
    rw [←DominatedLp.norm_sq_toLp (actualExpression_memLp d u.expression ht)] at hh
    change ‖actualExpressionLp d u.expression ht‖^2 ≤ M^2 at hh
    nlinarith [norm_nonneg (actualExpressionLp d u.expression ht)]
  have hh := actualVectorTermsLp_norm_le d ts ht htabs hnorm
  rw [←DominatedLp.norm_sq_toLp (actualVectorTerms_memLp d ts ht)]
  change ‖actualVectorTermsLp d ts ht‖^2 ≤ _
  nlinarith [norm_nonneg (actualVectorTermsLp d ts ht),mul_nonneg (materialMass_nonneg ts) hM0]

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
