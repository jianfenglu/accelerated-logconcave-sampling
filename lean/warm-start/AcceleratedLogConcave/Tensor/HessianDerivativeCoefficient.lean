import AcceleratedLogConcave.Tensor.HessianCoefficientBudget

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff RealInnerProductSpace
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open Conditional

/-- Literal spatial derivative tensor of the S coefficient, with the same
slot ordering as the differentiated J1 tensor. -/
def hessianDerivativeCoefficient {D : ℕ} (F : EuclideanSpace ℝ (Fin D) → ℝ)
    (x : EuclideanSpace ℝ (Fin D)) (ell r t : ℝ) (j : ℕ)
    (y : EuclideanSpace ℝ (Fin D)) : Coeff ((Fin j ⊕ Fin 1) ⊕ Unit) D :=
  WithLp.toLp 2 (fun a => JetCalculus.jet
    (fun i : Fin j => coordinateDirection D (a (Sum.inl (Sum.inl i)))) (List.finRange j)
    (fun z => coefficientEnvironment F x ell r t (Sum.inr ()) z
      (Fin.cons (a (Sum.inr ())) (fun i => a (Sum.inl (Sum.inr i))))) y)

variable {D : ℕ} (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))

theorem hessianDerivativeCoefficient_eq (j : ℕ) {t : ℝ} (ht : -1 < t ∧ t < 1)
    (y : EuclideanSpace ℝ (Fin D)) :
    hessianDerivativeCoefficient d.F d.x d.ell d.r t j y =
      (if j = 0 then WithLp.toLp 2 (fun a => inner ℝ
        (coordinateDirection D (a (Sum.inr ())))
        (coordinateDirection D (a (Sum.inl (Sum.inr 0))))) else 0) +
      (d.r^2*d.ell*t^2) • normalizedJetDerivativeCoefficient d.F d.x d.ell d.r t 0 j y := by
  ext a
  let b : Fin 2 → Fin D := Fin.cons (a (Sum.inr ())) (fun i => a (Sum.inl (Sum.inr i)))
  have he : (fun z => coefficientEnvironment d.F d.x d.ell d.r t (Sum.inr ()) z b) =
      fun z => inner ℝ (coordinateDirection D (b 0)) (coordinateDirection D (b 1)) +
        (d.r^2*d.ell*t^2) * coefficientEnvironment d.F d.x d.ell d.r t (Sum.inl 0) z b := by
    funext z
    exact congrArg (fun A : Coeff (Fin 2) D => A b)
      (coefficientEnvironment_hessian_eq_identity_add_J1 d ht z)
  have hJ := contDiff_scaledJet_spatial 1 d.hF d.hlo d.hhi d.x d.r ht.1 ht.2
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun z => coefficientEnvironment d.F d.x d.ell d.r t (Sum.inl 0) z b) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun z => (d.ell*d.r*((0+1).factorial : ℝ))⁻¹ *
      inner ℝ (coordinateDirection D (b 0)) (scaledJet 1 d.F d.x d.r t z (fun i => coordinateDirection D (b i.succ))))
    exact contDiff_const.mul (contDiff_const.inner ℝ
      ((ScaledJetPolynomial.tensorEvaluation 1 (fun i => coordinateDirection D (b i.succ))).contDiff.comp hJ))
  change JetCalculus.jet _ _ (fun z => coefficientEnvironment d.F d.x d.ell d.r t (Sum.inr ()) z b) y = _
  rw [he,JetCalculus.jet_add contDiff_const (contDiff_const.mul hc),JetCalculus.jet_const_mul hc]
  simp only [JetCalculus.jet_const]
  by_cases hj : j = 0 <;> simp [hj,normalizedJetDerivativeCoefficient,b]

/-- Source size-two, weight-zero budget for the literal Hessian coefficient,
using only the original curvature-smallness regime. The same c0=2 works for
all normalized J coefficients and for S. -/
theorem hessianDerivativeCoefficient_budget (hsmall : d.r^2*d.ell ≤ 1/2)
    (j : ℕ) {t : ℝ} (ht : -1 < t ∧ t < 1) (y : EuclideanSpace ℝ (Fin D))
    (S : Finset ((Fin j ⊕ Fin 1) ⊕ Unit)) (hS : NontrivialSplit S) :
    splitNorm D S (hessianDerivativeCoefficient d.F d.x d.ell d.r t j y) ≤
      (2:ℝ)^(2+j) * ((2+j).factorial : ℝ) *
        ((Real.sqrt (conditionalVariance t))^j)⁻¹ := by
  have ht1 : |t| ≤ 1 := (abs_lt.mpr ht).le
  have ht2 : t^2 ≤ 1 := (sq_le_one_iff_abs_le_one t).mpr ht1
  have hc0 : 0 ≤ d.r^2*d.ell*t^2 := mul_nonneg (mul_nonneg (sq_nonneg _) d.hell) (sq_nonneg _)
  have hc : d.r^2*d.ell*t^2 ≤ 1/2 :=
    (mul_le_mul_of_nonneg_left ht2 (mul_nonneg (sq_nonneg _) d.hell)).trans (by simpa using hsmall)
  have hJ := normalizedJetDerivativeCoefficient_budget d 0 j ht y S hS
  simp only [Nat.zero_add] at hJ
  rw [hessianDerivativeCoefficient_eq d j ht y]
  split_ifs with hj
  · subst j
    have hI := pairIdentity_splitNorm_le
      (Slot := (Fin 0 ⊕ Fin 1) ⊕ Unit) (by simp)
      (Sum.inr ()) (Sum.inl (Sum.inr 0)) (by simp) S hS (D := D)
    have hA := splitNorm_add_le D S
      (WithLp.toLp 2 (fun a => inner ℝ (coordinateDirection D (a (Sum.inr ())))
        (coordinateDirection D (a (Sum.inl (Sum.inr 0))))))
      ((d.r^2*d.ell*t^2) • normalizedJetDerivativeCoefficient d.F d.x d.ell d.r t 0 0 y)
    rw [splitNorm_smul,abs_of_nonneg hc0] at hA
    norm_num at hJ ⊢
    nlinarith
  · rw [zero_add,splitNorm_smul,abs_of_nonneg hc0]
    have hp : 0 ≤ (2:ℝ)^(2+j) * ((2+j).factorial : ℝ) *
        ((Real.sqrt (conditionalVariance t))^j)⁻¹ := by positivity
    exact (mul_le_mul_of_nonneg_left hJ hc0).trans
      ((mul_le_mul_of_nonneg_right (by linarith : d.r^2*d.ell*t^2 ≤ 1) hp).trans_eq (one_mul _))

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
