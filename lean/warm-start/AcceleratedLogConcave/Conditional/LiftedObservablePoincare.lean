import AcceleratedLogConcave.Conditional.Cumulants
import AcceleratedLogConcave.Conditional.PolynomialMoments
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-! Original-data Poincare for the normalized gradient-observable lift.
The image lives in a Euclidean sum, not the max-norm product. -/
noncomputable section
open MeasureTheory ProbabilityTheory WithLp InnerProductSpace Function
open scoped ContDiff RealInnerProductSpace NNReal
namespace AcceleratedLogConcave.Conditional
namespace LiftedObservable
open Appell
section Growth
variable {E W G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup W]
  [NormedAddCommGroup G]

lemma growth_comp {f : W → G} {T : E → W} (hf : HasGrowth f) (hT : HasGrowth T) :
    HasGrowth (f ∘ T) := by
  obtain ⟨C,hC,n,hf⟩ := hf
  obtain ⟨A,hA,k,hk⟩ := (HasGrowth.const C).mul
    ((HasGrowth.const (1:ℝ)).add (hT.norm.pow n))
  refine ⟨A,hA,k,fun x => (hf (T x)).trans ?_⟩
  exact (le_abs_self _).trans (hk x)

end Growth
section Transfer
variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W] [BorelSpace W]

/-- The original Gibbs C1 inequality pulls back through a C1 Lipschitz map.
Polynomial tests are not incorrectly assumed polynomial after pullback. -/
theorem polynomialPoincare_map_of_gibbs (μ : Measure E) [IsProbabilityMeasure μ]
    (V : E → ℝ) (hV : ContDiff ℝ 2 V)
    (hI : Integrable (fun x => Real.exp (-V x)))
    (hμ : μ = volume.tilted (fun x => -V x)) (hMom : HasMoments μ)
    (m L : ℝ) (hm : 0 < m)
    (hlower : ∀ x a, m*‖a‖^2 ≤ fderiv ℝ (fderiv ℝ V) x a a)
    (hupper : ∀ x a, fderiv ℝ (fderiv ℝ V) x a a ≤ L*‖a‖^2)
    (T : E → W) (hT : ContDiff ℝ 1 T) {K : ℝ≥0} (hLip : LipschitzWith K T) :
    HasPolynomialPoincare (μ.map T) ((K:ℝ)^2 * m⁻¹) := by
  intro p hp
  have hpc : ContDiff ℝ 1 p := hp.contDiff.of_le (by simp)
  have hc : ContDiff ℝ 1 (p ∘ T) := hpc.comp hT
  have hTg : HasGrowth T := HasGrowth.lipschitz hLip
  have hpg : HasGrowth (p ∘ T) := growth_comp hp.hasGrowth hTg
  have hdg : HasGrowth (fun x => ‖fderiv ℝ p (T x)‖) :=
    (growth_comp hp.fderiv_hasGrowth hTg).norm
  have hb (x : E) : ‖gradient (p ∘ T) x‖ ≤ (K:ℝ)*‖fderiv ℝ p (T x)‖ := by
    rw [show ‖gradient (p ∘ T) x‖ = ‖fderiv ℝ (p ∘ T) x‖ from
      (toDual ℝ E).symm.norm_map _,
      fderiv_comp x (hpc.differentiable (by simp) (T x)) (hT.differentiable (by simp) x)]
    exact ((fderiv ℝ p (T x)).opNorm_comp_le _).trans
      (by simpa only [mul_comm] using (mul_le_mul_of_nonneg_left
        (norm_fderiv_le_of_lipschitz ℝ hLip) (norm_nonneg (fderiv ℝ p (T x)))))
  have hgm : AEStronglyMeasurable (gradient (p ∘ T)) μ :=
    ((toDual ℝ E).symm.continuous.comp (hc.continuous_fderiv (by simp))).aestronglyMeasurable
  have hq : MemLp (gradient (p ∘ T)) 2 μ := by
    apply (((HasGrowth.const (K:ℝ)).mul hdg).memLp
      ((continuous_const.mul ((hpc.continuous_fderiv (by simp)).comp hT.continuous).norm)).aestronglyMeasurable hMom).of_le hgm
    filter_upwards [] with x
    exact (hb x).trans (le_abs_self _)
  have h := Gibbs.c1_variance_poincare μ V hV hI hμ m L hm hlower hupper
    (p ∘ T) hc (hpg.memLp hc.continuous.aestronglyMeasurable hMom) hq
  have hdI : Integrable (fun x => ‖fderiv ℝ p (T x)‖^2) μ :=
    (hdg.pow 2).integrable
      ((((hpc.continuous_fderiv (by simp)).comp hT.continuous).norm.pow 2).aestronglyMeasurable) hMom
  have he := integral_mono ((memLp_two_iff_integrable_sq_norm hq.aestronglyMeasurable).mp hq)
    (hdI.const_mul ((K:ℝ)^2)) (fun x => by
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (hb x) 2)
  rw [integral_const_mul] at he
  rw [variance_map hp.contDiff.continuous.measurable.aemeasurable hT.continuous.measurable.aemeasurable,
    variance_eq_integral hc.continuous.measurable.aemeasurable,
    integral_map (f := fun x : W => ‖fderiv ℝ p x‖^2) hT.continuous.measurable.aemeasurable
      ((hp.contDiff.continuous_fderiv (by simp)).norm.pow 2).aestronglyMeasurable]
  have hh := (le_inv_mul_iff₀ hm).mpr (h.trans he)
  simpa only [mul_assoc, mul_left_comm] using hh

end Transfer
end LiftedObservable

variable {D : ℕ}

/-- Original Hessian upper bound `ell`; normalization is by `r*ell`. -/
def normalizedObservableLift (F : (EuclideanSpace ℝ (Fin D)) → ℝ) (x : (EuclideanSpace ℝ (Fin D))) (r ell : ℝ) (z : (EuclideanSpace ℝ (Fin D))) : (EuclideanSpace ℝ (Fin D ⊕ Fin D)) :=
  toLp 2 (Sum.elim (fun i => z i)
    (fun i => (r*ell)⁻¹ * primitiveObservable F x r z i))

@[simp] theorem normalizedObservableLift_inl (F : (EuclideanSpace ℝ (Fin D)) → ℝ) (x : (EuclideanSpace ℝ (Fin D))) (r ell : ℝ)
    (z : (EuclideanSpace ℝ (Fin D))) (i : Fin D) : normalizedObservableLift F x r ell z (Sum.inl i) = z i := rfl

@[simp] theorem normalizedObservableLift_inr (F : (EuclideanSpace ℝ (Fin D)) → ℝ) (x : (EuclideanSpace ℝ (Fin D))) (r ell : ℝ)
    (z : (EuclideanSpace ℝ (Fin D))) (i : Fin D) : normalizedObservableLift F x r ell z (Sum.inr i) =
      (r*ell)⁻¹ * primitiveObservable F x r z i := rfl

private def euclideanSumPair (z w : EuclideanSpace ℝ (Fin D)) :
    EuclideanSpace ℝ (Fin D ⊕ Fin D) := toLp 2 (Sum.elim z w)

private theorem norm_sq_euclideanSumPair (z w : EuclideanSpace ℝ (Fin D)) :
    ‖euclideanSumPair z w‖^2 = ‖z‖^2+‖w‖^2 := by
  simp [euclideanSumPair, EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type]

private theorem lift_sub_eq (F : EuclideanSpace ℝ (Fin D) → ℝ)
    (x : EuclideanSpace ℝ (Fin D)) (r ell : ℝ) (z w : EuclideanSpace ℝ (Fin D)) :
    normalizedObservableLift F x r ell z - normalizedObservableLift F x r ell w =
      euclideanSumPair (z-w) ((r*ell)⁻¹ • (primitiveObservable F x r z - primitiveObservable F x r w)) := by
  ext i
  cases i <;> simp [normalizedObservableLift, euclideanSumPair, mul_sub]

theorem contDiff_normalizedObservableLift {F : EuclideanSpace ℝ (Fin D) → ℝ}
    (hF : ContDiff ℝ 2 F) (x : EuclideanSpace ℝ (Fin D)) (r ell : ℝ) :
    ContDiff ℝ 1 (normalizedObservableLift F x r ell) := by
  have hg : ContDiff ℝ 1 (gradient F) :=
    (toDual ℝ (EuclideanSpace ℝ (Fin D))).symm.contDiff.comp (hF.fderiv_right (by norm_num))
  have ha : ContDiff ℝ 1 (fun z : EuclideanSpace ℝ (Fin D) => x+r•z) := by fun_prop
  have hf : ContDiff ℝ 1 (primitiveObservable F x r) := hg.comp ha
  apply (contDiff_piLp 2).mpr
  intro i
  cases i with
  | inl i => exact (contDiff_piLp 2).mp contDiff_id i
  | inr i => exact contDiff_const.mul ((contDiff_piLp 2).mp hf i)

theorem lipschitz_normalizedObservableLift {F : EuclideanSpace ℝ (Fin D) → ℝ}
    (hF : ContDiff ℝ 2 F) {ell r : ℝ} (hell : 0 < ell) (hr : 0 < r)
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ ell*‖w‖^2)
    (x : EuclideanSpace ℝ (Fin D)) :
    LipschitzWith ⟨Real.sqrt 2, Real.sqrt_nonneg 2⟩ (normalizedObservableLift F x r ell) := by
  have hg := Gibbs.gradient_lipschitz_of_hessian_bounds hF hell.le hlo hhi
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [dist_eq_norm, dist_eq_norm]
  have hobs : ‖(r*ell)⁻¹ • (primitiveObservable F x r z - primitiveObservable F x r w)‖ ≤ ‖z-w‖ := by
    have hh := hg.norm_sub_le (x+r•z) (x+r•w)
    have he : (x+r•z)-(x+r•w) = r•(z-w) := by module
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hr] at hh
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (mul_pos hr hell)]
    calc
      _ ≤ (r*ell)⁻¹ * (ell*(r*‖z-w‖)) :=
        mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (mul_pos hr hell).le)
      _ = ‖z-w‖ := by field_simp
  have hsq : ‖normalizedObservableLift F x r ell z - normalizedObservableLift F x r ell w‖^2 ≤ 2*‖z-w‖^2 := by
    rw [lift_sub_eq, norm_sq_euclideanSumPair]
    nlinarith [sq_le_sq₀ (norm_nonneg _) (norm_nonneg (z-w)) |>.mpr hobs]
  have hsqrt := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hn := norm_nonneg (normalizedObservableLift F x r ell z - normalizedObservableLift F x r ell w)
  have hp := mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg (z-w))
  change ‖normalizedObservableLift F x r ell z - normalizedObservableLift F x r ell w‖ ≤ Real.sqrt 2 * ‖z-w‖
  nlinarith

/-- Actual conditional lifted law has polynomial Poincare constant 2υ.
All C1, integrability, posterior curvature and normalization premises are
proved from the original C²/curvature data. -/
theorem conditionalLift_polynomialPoincare {F : EuclideanSpace ℝ (Fin D) → ℝ}
    (hF : ContDiff ℝ 2 F) {ell r t : ℝ} (hell : 0 < ell) (hr : 0 < r)
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ ell*‖w‖^2)
    (x y : EuclideanSpace ℝ (Fin D)) (htlo : -1 < t) (hthi : t < 1) :
    HasPolynomialPoincare
      ((conditionalLaw F x r t y).map (normalizedObservableLift F x r ell))
      (2*conditionalVariance t) := by
  have hv := conditionalVariance_pos htlo hthi
  have hB := contDiff_primitivePotential hF x r
  have hBl : ∀ z w, (0:ℝ)*‖w‖^2 ≤
      fderiv ℝ (fderiv ℝ (primitivePotential F x r)) z w w := by
    simpa only [zero_mul] using primitivePotential_hessian_nonneg hF hlo x r
  let := conditionalLaw_isProbabilityMeasure hF hlo x r htlo hthi y
  have h := LiftedObservable.polynomialPoincare_map_of_gibbs (conditionalLaw F x r t y)
    (fun z => primitivePotential F x r z + ‖z-t•y‖^2/(2*conditionalVariance t))
    (Gibbs.contDiff_posterior_potential hB (conditionalVariance t) (t•y))
    (Gibbs.integrable_posterior_of_hessian_lower hB (le_refl 0) hv (t•y) hBl)
    (Gibbs.heatPosterior_eq_tilted hB (le_refl 0) hv hBl (t•y))
    (fun n => Gibbs.integrable_norm_pow_heatPosterior hB (le_refl 0) hv hBl (t•y) n)
    (0+(conditionalVariance t)⁻¹) (r^2*ell+(conditionalVariance t)⁻¹) (by positivity)
    (Gibbs.posterior_hessian_lower hB hBl (conditionalVariance t) (t•y))
    (Gibbs.posterior_hessian_upper hB (primitivePotential_hessian_upper hF hhi x r)
      (conditionalVariance t) (t•y))
    (normalizedObservableLift F x r ell) (contDiff_normalizedObservableLift hF x r ell)
    (lipschitz_normalizedObservableLift hF hell hr hlo hhi x)
  change HasPolynomialPoincare _ ((Real.sqrt 2)^2 * (0+(conditionalVariance t)⁻¹)⁻¹) at h
  simpa only [zero_add, inv_inv, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] using h

end AcceleratedLogConcave.Conditional
