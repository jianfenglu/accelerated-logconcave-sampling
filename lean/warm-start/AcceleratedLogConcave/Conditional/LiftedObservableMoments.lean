import AcceleratedLogConcave.Conditional.LiftedObservablePoincare

/-! Actual exponential moments of the nonlinear normalized observable lift.
Gaussian posterior tails dominate its Lipschitz affine growth. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace ENNReal NNReal
namespace AcceleratedLogConcave.Conditional
namespace LiftedObservable
section General
variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

lemma integrable_exp_sub_of_quadratic_bound {V g : E → ℝ}
    (hV : Measurable V) (hg : Measurable g) {a c A B : ℝ} (b : E) (hc : 0 < c)
    (hlower : ∀ z, a+inner ℝ b z+c*‖z‖^2 ≤ V z)
    (hbound : ∀ z, g z ≤ A+B*‖z‖) :
    Integrable (fun z => Real.exp (-(V z-g z))) := by
  apply Gibbs.integrable_exp_neg_of_quadratic_lower_bound (hV.sub hg) b
    (show 0 < c/2 by positivity) (a := a-A-B^2/(2*c))
  intro z
  have hy : B*‖z‖ ≤ c/2*‖z‖^2+B^2/(2*c) := by
    have hsq : 0 ≤ (c*‖z‖-B)^2/(2*c) := by positivity
    have he : (c*‖z‖-B)^2/(2*c) = c/2*‖z‖^2-B*‖z‖+B^2/(2*c) := by
      field_simp [ne_of_gt hc]
      ring
    rw [he] at hsq
    linarith
  change a-A-B^2/(2*c)+inner ℝ b z+c/2*‖z‖^2 ≤ V z-g z
  nlinarith [hlower z, hbound z]

/-- Every real exponential-linear observable of any Lipschitz image is
integrable under the actual Gaussian posterior; not just near zero. -/
theorem posterior_integrable_exp_inner_lipschitz {F : E → ℝ}
    (hF : ContDiff ℝ 2 F) {m t : ℝ} (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ z w, m*‖w‖^2 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (y : E) (T : E → W) {K : ℝ≥0} (hT : LipschitzWith K T) (θ : W) :
    Integrable (fun z => Real.exp (inner ℝ θ (T z))) (Gibbs.heatPosterior F t y) := by
  let b : E := (toDual ℝ E).symm (fderiv ℝ F 0)
  have hbase (z : E) : F 0 + inner ℝ b z + m/2*‖z‖^2 ≤ F z := by
    simpa only [b, toDual_symm_apply] using Gibbs.quadratic_lower_bound_of_hessian_lower hF hlo z
  have hnorm (z : E) : ‖T z‖ ≤ ‖T 0‖+(K:ℝ)*‖z‖ := by
    have hh := norm_add_le (T z-T 0) (T 0)
    rw [sub_add_cancel] at hh
    have hl := hT.norm_sub_le z 0
    simp only [sub_zero] at hl
    linarith
  have hbound (z : E) : inner ℝ θ (T z) ≤
      ‖θ‖*‖T 0‖ + (‖θ‖*(K:ℝ))*‖z‖ := by
    calc
      _ ≤ ‖θ‖*‖T z‖ := real_inner_le_norm _ _
      _ ≤ ‖θ‖*(‖T 0‖+(K:ℝ)*‖z‖) := mul_le_mul_of_nonneg_left (hnorm z) (norm_nonneg θ)
      _ = _ := by ring
  have hshift : Integrable (fun z => Real.exp
      (-((F z+‖z-y‖^2/(2*t))-inner ℝ θ (T z)))) :=
    integrable_exp_sub_of_quadratic_bound (hF.continuous.measurable.add (by fun_prop))
      (continuous_const.inner hT.continuous).measurable (b-t⁻¹•y)
      (by positivity : 0 < m/2+1/(2*t))
      (Gibbs.posterior_quadratic_lower_bound b y hbase) hbound
  have hI := Gibbs.integrable_posterior_of_hessian_lower hF hm ht y hlo
  apply Integrable.smul_measure _ (ENNReal.inv_ne_top.mpr (Gibbs.lintegral_exp_neg_pos hI).ne')
  apply (integrable_withDensity_iff_integrable_smul'
    (show Measurable (fun z : E => ENNReal.ofReal (Real.exp (-(F z+‖z-y‖^2/(2*t))))) by
      have hFm := hF.continuous.measurable
      fun_prop) (by simp)).mpr
  convert hshift using 1
  funext z
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, ← Real.exp_add]
  congr 1
  ring
end General
end LiftedObservable

variable {D : ℕ}

theorem conditionalLift_integrable_exp_inner {F : EuclideanSpace ℝ (Fin D) → ℝ}
    (hF : ContDiff ℝ 2 F) {ell r t : ℝ} (hell : 0 < ell) (hr : 0 < r)
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ ell*‖w‖^2)
    (x y : EuclideanSpace ℝ (Fin D)) (htlo : -1 < t) (hthi : t < 1)
    (θ : EuclideanSpace ℝ (Fin D ⊕ Fin D)) :
    Integrable (fun u => Real.exp (inner ℝ θ u))
      ((conditionalLaw F x r t y).map (normalizedObservableLift F x r ell)) := by
  have hLip := lipschitz_normalizedObservableLift hF hell hr hlo hhi x
  apply (integrable_map_measure (by fun_prop) hLip.continuous.measurable.aemeasurable).mpr
  apply LiftedObservable.posterior_integrable_exp_inner_lipschitz
    (contDiff_primitivePotential hF x r) (le_refl 0) (conditionalVariance_pos htlo hthi)
    _ (t•y) _ hLip θ
  simpa only [zero_mul] using primitivePotential_hessian_nonneg hF hlo x r

theorem conditionalLift_hasLocalMGF {F : EuclideanSpace ℝ (Fin D) → ℝ}
    (hF : ContDiff ℝ 2 F) {ell r t : ℝ} (hell : 0 < ell) (hr : 0 < r)
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ ell*‖w‖^2)
    (x y : EuclideanSpace ℝ (Fin D)) (htlo : -1 < t) (hthi : t < 1) :
    HasLocalMGF ((conditionalLaw F x r t y).map (normalizedObservableLift F x r ell)) :=
  Filter.Eventually.of_forall (conditionalLift_integrable_exp_inner hF hell hr hlo hhi x y htlo hthi)

theorem conditionalLift_isProbabilityMeasure {F : EuclideanSpace ℝ (Fin D) → ℝ}
    (hF : ContDiff ℝ 2 F) (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (x y : EuclideanSpace ℝ (Fin D)) (r ell : ℝ) {t : ℝ}
    (htlo : -1 < t) (hthi : t < 1) :
    IsProbabilityMeasure ((conditionalLaw F x r t y).map (normalizedObservableLift F x r ell)) := by
  let := conditionalLaw_isProbabilityMeasure hF hlo x r htlo hthi y
  exact (Measure.isProbabilityMeasure_map_iff
    (contDiff_normalizedObservableLift hF x r ell).continuous.measurable.aemeasurable).mpr inferInstance

theorem conditionalLift_hasMoments {F : EuclideanSpace ℝ (Fin D) → ℝ}
    (hF : ContDiff ℝ 2 F) {ell r t : ℝ} (hell : 0 < ell) (hr : 0 < r)
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ ell*‖w‖^2)
    (x y : EuclideanSpace ℝ (Fin D)) (htlo : -1 < t) (hthi : t < 1) :
    Appell.HasMoments ((conditionalLaw F x r t y).map (normalizedObservableLift F x r ell)) := by
  let := conditionalLift_isProbabilityMeasure hF hlo x y r ell htlo hthi
  exact (conditionalLift_hasLocalMGF hF hell hr hlo hhi x y htlo hthi).hasMoments
    (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin D ⊕ Fin D)))

/-- Sharp factorial cumulant split bound for the actual lifted image law.
Restriction to the gradient-observable Uq slots is a separate theorem. -/
theorem conditionalLift_cumulantTensor_splitNorm_le {Slot : Type}
    [Fintype Slot] [DecidableEq Slot] {N : ℕ}
    {F : EuclideanSpace ℝ (Fin D) → ℝ} (hF : ContDiff ℝ 2 F)
    {ell r t : ℝ} (hell : 0 < ell) (hr : 0 < r)
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ ell*‖w‖^2)
    (x y : EuclideanSpace ℝ (Fin D)) (htlo : -1 < t) (hthi : t < 1)
    (b : OrthonormalBasis (Fin N) ℝ (EuclideanSpace ℝ (Fin D ⊕ Fin D)))
    (S : Finset Slot) (hS : Tensor.NontrivialSplit S) :
    Tensor.splitNorm N S (cumulantTensor
      ((conditionalLaw F x r t y).map (normalizedObservableLift F x r ell)) b) ≤
      ((Fintype.card Slot-1).factorial:ℝ) * (Real.sqrt (2*conditionalVariance t))^Fintype.card Slot := by
  let := conditionalLift_isProbabilityMeasure hF hlo x y r ell htlo hthi
  exact cumulantTensor_splitNorm_le
    (conditionalLift_hasLocalMGF hF hell hr hlo hhi x y htlo hthi)
    (mul_nonneg (by norm_num) (conditionalVariance_pos htlo hthi).le)
    (conditionalLift_polynomialPoincare hF hell hr hlo hhi x y htlo hthi) b S hS

end AcceleratedLogConcave.Conditional
