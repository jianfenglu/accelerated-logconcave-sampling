import AcceleratedLogConcave.Tensor.MaterialWordsSum
import AcceleratedLogConcave.Analysis.DominatedLp
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff ENNReal
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open Conditional Analysis Analysis.PositiveVarianceSlab MeasureTheory Set
variable {D : ℕ} (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))

theorem actualExpression_memLp {r : ℕ} (e : Expr signature r) {t : ℝ}
    (ht : t ∈ Icc (left d.b) (right d.b)) :
    MemLp (Expr.evaluate (coefficientEnvironment d.F d.x d.ell d.r t)
      (interpolationPotential d.F d.x d.r t) e) 2 (interpolationLaw d.F d.x d.r t) := by
  apply MemLp.of_eval_piLp
  intro a
  have ht' := construction_subset d.hb0 d.hb1 ht
  have hc := CoordinateReduction.contDiff_section _ _
    (coefficient_contDiff d.hF d.hlo d.hhi d.hb0 d.hb1 d.x d.r ht)
    (contDiff_interpolationPotential d.hF d.hlo d.hhi d.x d.r ht'.1 ht'.2) e a
  apply (memLp_two_iff_integrable_sq hc.continuous.aestronglyMeasurable).2
  exact integral_section_pow d.hF d.hlo d.hhi d.hb0 d.hb1 d.x d.r ht e a [] 2

def actualExpressionLp {r : ℕ} (e : Expr signature r) {t : ℝ}
    (ht : t ∈ Icc (left d.b) (right d.b)) :
    Lp (FinCoeff r D) 2 (interpolationLaw d.F d.x d.r t) :=
  (actualExpression_memLp d e ht).toLp _

theorem actualTerms_memLp (ts : List (MaterialTerm 2)) {t : ℝ}
    (ht : t ∈ Icc (left d.b) (right d.b)) :
    MemLp (materialTermsTensor d ts t) 2 (interpolationLaw d.F d.x d.r t) := by
  induction ts with
  | nil => exact MemLp.zero
  | cons u ts ih =>
    exact ((actualExpression_memLp d u.expression ht).const_smul (u.coefficient*t^u.degree)).add ih

def actualTermsLp (ts : List (MaterialTerm 2)) {t : ℝ}
    (ht : t ∈ Icc (left d.b) (right d.b)) :
    Lp (FinCoeff 2 D) 2 (interpolationLaw d.F d.x d.r t) :=
  (actualTerms_memLp d ts ht).toLp _

theorem actualTermsLp_cons (u : MaterialTerm 2) (ts : List (MaterialTerm 2)) {t : ℝ}
    (ht : t ∈ Icc (left d.b) (right d.b)) :
    actualTermsLp d (u::ts) ht =
      (u.coefficient*t^u.degree) • actualExpressionLp d u.expression ht + actualTermsLp d ts ht := rfl

theorem actualTermsLp_norm_le (ts : List (MaterialTerm 2)) {t M : ℝ}
    (ht : t ∈ Icc (left d.b) (right d.b)) (htabs : |t|≤1)
    (hM : ∀ u ∈ ts, ‖actualExpressionLp d u.expression ht‖ ≤ M) :
    ‖actualTermsLp d ts ht‖ ≤ materialMass ts*M := by
  induction ts with
  | nil =>
    have hz : actualTermsLp d [] ht = 0 := rfl
    rw [hz]
    simp [materialMass]
  | cons u ts ih =>
    have hu := hM u (by simp)
    have hs := ih (fun v hv => hM v (by simp [hv]))
    have hc : ‖u.coefficient*t^u.degree‖ ≤ |u.coefficient| := by
      rw [Real.norm_eq_abs,abs_mul,abs_pow]
      have hp : |t|^u.degree ≤ 1 := pow_le_one₀ (abs_nonneg t) htabs
      nlinarith [abs_nonneg u.coefficient]
    rw [actualTermsLp_cons]
    calc
      _ ≤ ‖(u.coefficient*t^u.degree) • actualExpressionLp d u.expression ht‖ +
          ‖actualTermsLp d ts ht‖ := norm_add_le _ _
      _ ≤ |u.coefficient| * M+materialMass ts*M := by
        rw [norm_smul]
        exact add_le_add (mul_le_mul hc hu (norm_nonneg _) (abs_nonneg _)) hs
      _ = materialMass (u::ts)*M := by simp [materialMass]; ring

/-- Only the pending whole-expression RMS estimate is a premise; all
measurability and L2 integrability come from original flow data. -/
theorem actualTerms_integral_norm_sq_le (ts : List (MaterialTerm 2)) {t M : ℝ}
    (ht : t ∈ Icc (left d.b) (right d.b)) (htabs : |t|≤1) (hM0 : 0≤M)
    (hM : ∀ u ∈ ts,
      (∫ y, ‖Expr.evaluate (coefficientEnvironment d.F d.x d.ell d.r t)
        (interpolationPotential d.F d.x d.r t) u.expression y‖^2
        ∂interpolationLaw d.F d.x d.r t) ≤ M^2) :
    (∫ y, ‖materialTermsTensor d ts t y‖^2 ∂interpolationLaw d.F d.x d.r t) ≤
      (materialMass ts*M)^2 := by
  have hnorm : ∀ u ∈ ts, ‖actualExpressionLp d u.expression ht‖ ≤ M := by
    intro u hu
    have hh := hM u hu
    rw [←DominatedLp.norm_sq_toLp (actualExpression_memLp d u.expression ht)] at hh
    change ‖actualExpressionLp d u.expression ht‖^2 ≤ M^2 at hh
    nlinarith [norm_nonneg (actualExpressionLp d u.expression ht)]
  have hh := actualTermsLp_norm_le d ts ht htabs hnorm
  rw [←DominatedLp.norm_sq_toLp (actualTerms_memLp d ts ht)]
  change ‖actualTermsLp d ts ht‖^2 ≤ _
  nlinarith [norm_nonneg (actualTermsLp d ts ht),mul_nonneg (materialMass_nonneg ts) hM0]

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
