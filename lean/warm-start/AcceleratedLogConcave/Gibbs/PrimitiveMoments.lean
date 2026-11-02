import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import AcceleratedLogConcave.Gibbs.HeatHessian
import Mathlib.Probability.Moments.Variance

/-!
# Primitive posterior laws, moments, mean regularity, and Gaussian score error

The primitive law of `sources/warm-start.tex`, lines 1101–1135, is the actual
normalized density proportional to `exp (-‖z‖²/2 - F (x + r • z))`.
The unregularized base density need not be normalizable. Coordinate integration
by parts proves its second-moment bound. An affine density change of variables
identifies its score mean with the heat score and yields mean Lipschitzness.
The standard-Gaussian test-score residual has finite L² norm and satisfies the
source's constant-three bound (in fact constant two). These analytic estimates
do not require the separate synchronous Wasserstein estimate or small curvature.
-/

noncomputable section

namespace AcceleratedLogConcave.Gibbs

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal ContDiff

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem primitive_contDiff_affine_comp {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (x : E) (r : ℝ) : ContDiff ℝ 2 (fun z ↦ F (x + r • z)) :=
  hF.comp (contDiff_const.add (contDiff_const.smul contDiff_id))

theorem primitive_fderiv_affine_comp
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : E → G} (hF : Differentiable ℝ F) (x : E) (r : ℝ) (z : E) :
    fderiv ℝ (fun z ↦ F (x + r • z)) z = r • fderiv ℝ F (x + r • z) := by
  have h := (hF (x + r • z)).hasFDerivAt.comp z
    (((hasFDerivAt_id z).const_smul r).const_add x)
  change HasFDerivAt (fun z ↦ F (x + r • z)) _ z at h
  rw [h.fderiv]
  ext v
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul]

theorem primitive_fderiv_affine_comp_apply {F : E → ℝ} (hF : Differentiable ℝ F)
    (x : E) (r : ℝ) (z v : E) :
    fderiv ℝ (fun z ↦ F (x + r • z)) z v = r * fderiv ℝ F (x + r • z) v := by
  simp only [primitive_fderiv_affine_comp hF, smul_apply, smul_eq_mul]

theorem primitive_fderiv_fderiv_affine_comp_apply {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (x : E) (r : ℝ) (z v w : E) :
    fderiv ℝ (fderiv ℝ (fun z ↦ F (x + r • z))) z v w =
      r ^ 2 * fderiv ℝ (fderiv ℝ F) (x + r • z) v w := by
  have hd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hd' : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).differentiable (by norm_num)
  have heq : fderiv ℝ (fun z ↦ F (x + r • z)) =
      fun z ↦ r • fderiv ℝ F (x + r • z) :=
    funext (primitive_fderiv_affine_comp hd x r)
  have hc := (((hd'.comp ((differentiable_const x).add
    (differentiable_id.const_smul r))) z).hasFDerivAt).const_smul r
  change HasFDerivAt (fun z ↦ r • fderiv ℝ F (x + r • z)) _ z at hc
  rw [heq, hc.fderiv]
  change (r • fderiv ℝ (fun z ↦ fderiv ℝ F (x + r • z)) z) v w = _
  rw [primitive_fderiv_affine_comp hd']
  simp only [smul_apply, smul_eq_mul]
  ring

theorem primitive_affine_hessian_nonneg {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ y v, 0 ≤ fderiv ℝ (fderiv ℝ F) y v v) (x : E) (r : ℝ) :
    ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ (fun z ↦ F (x + r • z))) z v v := by
  intro z v
  rw [primitive_fderiv_fderiv_affine_comp_apply hF]
  exact mul_nonneg (sq_nonneg r) (hlo _ _)

theorem primitive_affine_hessian_upper {F : E → ℝ} {L : ℝ} (hF : ContDiff ℝ 2 F)
    (hup : ∀ y v, fderiv ℝ (fderiv ℝ F) y v v ≤ L * ‖v‖ ^ 2) (x : E) (r : ℝ) :
    ∀ z v, fderiv ℝ (fderiv ℝ (fun z ↦ F (x + r • z))) z v v ≤
      (r ^ 2 * L) * ‖v‖ ^ 2 := by
  intro z v
  rw [primitive_fderiv_fderiv_affine_comp_apply hF, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hup _ _) (sq_nonneg r)

variable [FiniteDimensional ℝ E]

theorem primitive_gradient_affine_comp {F : E → ℝ} (hF : Differentiable ℝ F)
    (x : E) (r : ℝ) (z : E) :
    gradient (fun z ↦ F (x + r • z)) z = r • gradient F (x + r • z) := by
  apply ext_inner_left ℝ
  intro v
  simp only [inner_gradient_right, real_inner_smul_right,
    primitive_fderiv_affine_comp_apply hF, map_mul, starRingEnd_apply, star_trivial]

theorem gradient_lipschitz_of_hessian_bounds {F : E → ℝ} {L : ℝ} (hF : ContDiff ℝ 2 F)
    (hL : 0 ≤ L)
    (hlo : ∀ x v, 0 ≤ fderiv ℝ (fderiv ℝ F) x v v)
    (hup : ∀ x v, fderiv ℝ (fderiv ℝ F) x v v ≤ L * ‖v‖ ^ 2) :
    LipschitzWith ⟨L, hL⟩ (gradient F) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm]
  change ‖gradient F x - gradient F y‖ ≤ L * ‖x - y‖
  obtain ⟨_, heq, _, _, hn⟩ :=
    AutoSamplingTheory.TechnicalLemmas.Analysis.HessianSecantOperator.hessian_secant_operator
      (α := 0) (β := L) hF (by simpa using hlo) hup x y
  rw [heq]
  apply (ContinuousLinearMap.le_opNorm _ _).trans
  simpa [abs_of_nonneg hL, max_eq_right hL] using
    mul_le_mul_of_nonneg_right hn (norm_nonneg (x - y))

theorem gradient_monotone_of_hessian_bounds {F : E → ℝ} {L : ℝ}
    (hF : ContDiff ℝ 2 F)
    (hlo : ∀ x v, 0 ≤ fderiv ℝ (fderiv ℝ F) x v v)
    (hup : ∀ x v, fderiv ℝ (fderiv ℝ F) x v v ≤ L * ‖v‖ ^ 2) (x y : E) :
    0 ≤ inner ℝ (gradient F x - gradient F y) (x - y) := by
  obtain ⟨_, heq, _, hb, _⟩ :=
    AutoSamplingTheory.TechnicalLemmas.Analysis.HessianSecantOperator.hessian_secant_operator
      (α := 0) (β := L) hF (by simpa using hlo) hup x y
  rw [heq]
  simpa only [zero_mul] using (hb (x - y)).1

theorem primitive_inner_scaled_gradient_sub_nonneg {F : E → ℝ} {L : ℝ}
    (hF : ContDiff ℝ 2 F)
    (hlo : ∀ x v, 0 ≤ fderiv ℝ (fderiv ℝ F) x v v)
    (hup : ∀ x v, fderiv ℝ (fderiv ℝ F) x v v ≤ L * ‖v‖ ^ 2)
    (x z : E) (r : ℝ) :
    0 ≤ inner ℝ z (r • (gradient F (x + r • z) - gradient F x)) := by
  have h := gradient_monotone_of_hessian_bounds hF hlo hup (x + r • z) x
  simpa only [add_sub_cancel_left, real_inner_smul_right, real_inner_smul_left,
    real_inner_comm] using h

end Calculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The normalized primitive posterior on its Gaussian coordinate. -/
def primitiveLaw (F : E → ℝ) (x : E) (r : ℝ) : Measure E :=
  heatPosterior (fun z ↦ F (x + r • z)) 1 0

/-- The actual posterior expectation of the base gradient. -/
def primitiveMean (F : E → ℝ) (x : E) (r : ℝ) : E :=
  ∫ z, gradient F (x + r • z) ∂primitiveLaw F x r

/-- The source's primitive scale, independent of the radius. -/
def primitiveScale (F : E → ℝ) (x : E) : ℝ :=
  Real.sqrt (Module.finrank ℝ E) + ‖gradient F x‖

omit [MeasurableSpace E] [BorelSpace E] in
theorem primitiveScale_nonneg (F : E → ℝ) (x : E) : 0 ≤ primitiveScale F x := by
  exact add_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] in
/-- On a probability law the first norm moment is bounded by the second-moment RMS. -/
theorem integral_norm_le_sqrt_integral_norm_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → E} (hf : MemLp f 2 μ) :
    (∫ z, ‖f z‖ ∂μ) ≤ Real.sqrt (∫ z, ‖f z‖ ^ 2 ∂μ) := by
  have hv := variance_nonneg (fun z => ‖f z‖) μ
  rw [variance_eq_sub hf.norm] at hv
  have h2 : 0 ≤ ∫ z, ‖f z‖ ^ 2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have h1 : 0 ≤ ∫ z, ‖f z‖ ∂μ := integral_nonneg (fun _ => norm_nonneg _)
  have hs := Real.sq_sqrt h2
  have hp := Real.sqrt_nonneg (∫ z, ‖f z‖ ^ 2 ∂μ)
  change 0 ≤ (∫ z, ‖f z‖ ^ 2 ∂μ) - (∫ z, ‖f z‖ ∂μ) ^ 2 at hv
  nlinarith


/-- Convexity alone normalizes the primitive law, for every real radius. -/
theorem primitiveLaw_isProbabilityMeasure {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ y v, 0 ≤ fderiv ℝ (fderiv ℝ F) y v v) (x : E) (r : ℝ) :
    IsProbabilityMeasure (primitiveLaw F x r) := by
  apply heatPosterior_isProbabilityMeasure (primitive_contDiff_affine_comp hF x r)
    (m := 0) (le_refl 0) (by norm_num : (0 : ℝ) < 1)
  simpa only [zero_mul] using primitive_affine_hessian_nonneg hF hlo x r

/-- Every primitive position moment is finite, including at radius zero. -/
theorem primitive_integrable_norm_pow {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ y v, 0 ≤ fderiv ℝ (fderiv ℝ F) y v v) (x : E) (r : ℝ) (n : ℕ) :
    Integrable (fun z ↦ ‖z‖ ^ n) (primitiveLaw F x r) := by
  apply integrable_norm_pow_heatPosterior (primitive_contDiff_affine_comp hF x r)
    (m := 0) (le_refl 0) (by norm_num : (0 : ℝ) < 1)
  simpa only [zero_mul] using primitive_affine_hessian_nonneg hF hlo x r

theorem primitive_memLp_two_id {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ y v, 0 ≤ fderiv ℝ (fderiv ℝ F) y v v) (x : E) (r : ℝ) :
    MemLp id 2 (primitiveLaw F x r) := by
  apply memLp_two_id_heatPosterior (primitive_contDiff_affine_comp hF x r)
    (m := 0) (le_refl 0) (by norm_num : (0 : ℝ) < 1)
  simpa only [zero_mul] using primitive_affine_hessian_nonneg hF hlo x r

/-- Continuous observables of affine growth have a genuine second primitive moment. -/
theorem primitive_memLp_two_of_affine_bound
    {G : Type*} [NormedAddCommGroup G] {g : E → G}
    {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ y v, 0 ≤ fderiv ℝ (fderiv ℝ F) y v v) (x : E) (r : ℝ)
    (hg : Continuous g) (A B : ℝ) (hb : ∀ z, ‖g z‖ ≤ A + B * ‖z‖) :
    MemLp g 2 (primitiveLaw F x r) := by
  apply memLp_two_heatPosterior_of_affine_bound (primitive_contDiff_affine_comp hF x r)
    (m := 0) (le_refl 0) (by norm_num : (0 : ℝ) < 1) _ 0 hg A B hb
  simpa only [zero_mul] using primitive_affine_hessian_nonneg hF hlo x r

/-- The base gradient observable is square integrable under the actual primitive law. -/
theorem primitive_memLp_two_score {F : E → ℝ} {L : ℝ} (hF : ContDiff ℝ 2 F)
    (hL : 0 ≤ L)
    (hlo : ∀ y v, 0 ≤ fderiv ℝ (fderiv ℝ F) y v v)
    (hup : ∀ y v, fderiv ℝ (fderiv ℝ F) y v v ≤ L * ‖v‖ ^ 2)
    (x : E) (r : ℝ) :
    MemLp (fun z ↦ gradient F (x + r • z)) 2 (primitiveLaw F x r) := by
  have hl := gradient_lipschitz_of_hessian_bounds hF hL hlo hup
  apply primitive_memLp_two_of_affine_bound hF hlo x r
    (hl.continuous.comp (by fun_prop)) ‖gradient F x‖ (L * |r|)
  intro z
  change ‖gradient F (x + r • z)‖ ≤ ‖gradient F x‖ + (L * |r|) * ‖z‖
  have hd : ‖gradient F (x + r • z) - gradient F x‖ ≤ (L * |r|) * ‖z‖ := by
    simpa only [dist_eq_norm, NNReal.coe_mk, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, mul_assoc] using! hl.dist_le_mul (x + r • z) x
  calc
    _ = ‖(gradient F (x + r • z) - gradient F x) + gradient F x‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖gradient F (x + r • z) - gradient F x‖ + ‖gradient F x‖ := norm_add_le _ _
    _ ≤ (L * |r|) * ‖z‖ + ‖gradient F x‖ := add_le_add hd (le_refl _)
    _ = _ := by ring

theorem primitive_integrable_score {F : E → ℝ} {L : ℝ} (hF : ContDiff ℝ 2 F)
    (hL : 0 ≤ L)
    (hlo : ∀ y v, 0 ≤ fderiv ℝ (fderiv ℝ F) y v v)
    (hup : ∀ y v, fderiv ℝ (fderiv ℝ F) y v v ≤ L * ‖v‖ ^ 2)
    (x : E) (r : ℝ) :
    Integrable (fun z ↦ gradient F (x + r • z)) (primitiveLaw F x r) := by
  let := primitiveLaw_isProbabilityMeasure hF hlo x r
  exact (primitive_memLp_two_score hF hL hlo hup x r).integrable (by norm_num)

/-- Linear-coordinate integration by parts under the actual unit posterior. -/
theorem integral_unit_posterior_coordinate_score
    {F : E → ℝ} {L : ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ x v, 0 ≤ (fderiv ℝ (fderiv ℝ F) x v) v)
    (hup : ∀ x v, (fderiv ℝ (fderiv ℝ F) x v) v ≤ L * ‖v‖ ^ 2)
    (v : E) :
    (∫ z, (fderiv ℝ F z v + ⟪z, v⟫) * ⟪z, v⟫ ∂heatPosterior F 1 0) =
      ‖v‖ ^ 2 := by
  have hl : ∀ x v, 0 * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v := by
    simpa using hlo
  let := heatPosterior_isProbabilityMeasure hF (le_refl 0) (by norm_num : (0:ℝ)<1) hl 0
  have hR := heatPosterior_eq_tilted hF (le_refl 0) (by norm_num : (0:ℝ)<1) hl 0
  have hv := memLp_two_directionalScore_heatPosterior hF (le_refl 0)
    (by norm_num : (0:ℝ)<1) hl hup 0 v
  have hp := memLp_two_position_heatPosterior hF (le_refl 0)
    (by norm_num : (0:ℝ)<1) hl 0 v
  have hposteq (z : E) :
      fderiv ℝ (fun a ↦ F a + ‖a - 0‖ ^ 2 / (2 * 1)) z v =
        fderiv ℝ F z v + ⟪z, v⟫ := by
    simpa only [inv_one, inner_zero_left, sub_zero, one_mul] using
      fderiv_posterior_potential_apply (hF.differentiable (by norm_num)) 1 0 z v
  have hpost : MemLp
      (fun z ↦ fderiv ℝ (fun a ↦ F a + ‖a - 0‖ ^ 2 / (2 * 1)) z v)
      2 (heatPosterior F 1 0) := by
    simpa only [hposteq, Pi.add_apply] using! hv.add hp
  have hd (z : E) : fderiv ℝ (fun a ↦ ⟪a, v⟫) z v = ‖v‖ ^ 2 := by
    change fderiv ℝ (fun a ↦ ⟪id a, v⟫) z v = _
    rw [fderiv_inner_apply ℝ differentiableAt_id (differentiableAt_const v)]
    simp
  have hderiv : Integrable (fun z ↦ fderiv ℝ (fun a ↦ ⟪a, v⟫) z v)
      (heatPosterior F 1 0) := by
    simpa only [hd] using (integrable_const (‖v‖ ^ 2) :
      Integrable (fun _ : E ↦ ‖v‖ ^ 2) (heatPosterior F 1 0))
  have hi := integral_tilted_fderiv (f := fun z ↦ ⟪z, v⟫) v
    ((contDiff_posterior_potential hF 1 0).differentiable (by norm_num))
    (by simpa only [id_eq] using (differentiable_id.inner ℝ (differentiable_const v)))
    (integrable_posterior_of_hessian_lower hF (le_refl 0)
      (by norm_num : (0:ℝ)<1) 0 hl)
    (by rw [← hR]; exact hpost.integrable_mul hp)
    (by rwa [← hR])
    (by rw [← hR]; exact hp.integrable (by norm_num))
  rw [← hR] at hi
  simpa only [hd, integral_const, probReal_univ, smul_eq_mul, one_mul, hposteq]
    using hi.symm

/-- Summing genuine coordinate IBP identities gives the dimension, including dimension zero. -/
theorem integral_unit_posterior_trace
    {F : E → ℝ} {L : ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ x v, 0 ≤ (fderiv ℝ (fderiv ℝ F) x v) v)
    (hup : ∀ x v, (fderiv ℝ (fderiv ℝ F) x v) v ≤ L * ‖v‖ ^ 2) :
    (∫ z, (‖z‖ ^ 2 + fderiv ℝ F z z) ∂heatPosterior F 1 0) =
      Module.finrank ℝ E := by
  let b := stdOrthonormalBasis ℝ E
  have hl : ∀ x v, 0 * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v := by
    simpa using hlo
  have hi (i : Fin (Module.finrank ℝ E)) :
      Integrable (fun z ↦ (fderiv ℝ F z (b i) + ⟪z, b i⟫) * ⟪z, b i⟫)
        (heatPosterior F 1 0) := by
    have hs := memLp_two_directionalScore_heatPosterior hF (le_refl 0)
      (by norm_num : (0:ℝ)<1) hl hup 0 (b i)
    have hp := memLp_two_position_heatPosterior hF (le_refl 0)
      (by norm_num : (0:ℝ)<1) hl 0 (b i)
    exact (hs.add hp).integrable_mul hp
  have heq (z : E) :
      (∑ i, (fderiv ℝ F z (b i) + ⟪z, b i⟫) * ⟪z, b i⟫) =
      ‖z‖ ^ 2 + fderiv ℝ F z z := by
    simp_rw [← inner_gradient_left, add_mul]
    rw [Finset.sum_add_distrib]
    have hs (a : E) : (∑ i, ⟪a, b i⟫ * ⟪z, b i⟫) = ⟪a, z⟫ := by
      calc
        _ = ∑ i, ⟪a, b i⟫ * ⟪b i, z⟫ := by
          apply Finset.sum_congr rfl
          intro i _
          rw [real_inner_comm z (b i)]
        _ = _ := b.sum_inner_mul_inner a z
    rw [hs, hs, real_inner_self_eq_norm_sq]
    ring
  simp_rw [← heq]
  rw [integral_finsetSum _ (fun i _ ↦ hi i)]
  simp_rw [integral_unit_posterior_coordinate_score hF hlo hup]
  simp [b.orthonormal.norm_eq_one]

/-- A convex unit-variance posterior has a quantitative, uncentered second moment. -/
theorem unit_posterior_second_moment_le
    {F : E → ℝ} {L : ℝ} (hF : ContDiff ℝ 2 F) (hL : 0 ≤ L)
    (hlo : ∀ x v, 0 ≤ (fderiv ℝ (fderiv ℝ F) x v) v)
    (hup : ∀ x v, (fderiv ℝ (fderiv ℝ F) x v) v ≤ L * ‖v‖ ^ 2) :
    Real.sqrt (∫ z, ‖z‖ ^ 2 ∂heatPosterior F 1 0) ≤
      Real.sqrt (Module.finrank ℝ E) + ‖gradient F 0‖ := by
  have hl : ∀ x v, 0 * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v := by
    simpa using hlo
  let := heatPosterior_isProbabilityMeasure hF (le_refl 0) (by norm_num : (0:ℝ)<1) hl 0
  have hz := memLp_two_id_heatPosterior hF (le_refl 0) (by norm_num : (0:ℝ)<1) hl 0
  have hg := memLp_two_gradient_heatPosterior hF (le_refl 0)
    (by norm_num : (0:ℝ)<1) hl hup 0
  have hn : Integrable (fun z : E ↦ ‖z‖) (heatPosterior F 1 0) :=
    hz.norm.integrable (by norm_num)
  have h2 := integrable_norm_pow_heatPosterior hF (le_refl 0)
    (by norm_num : (0:ℝ)<1) hl 0 2
  have hdiag : Integrable (fun z ↦ fderiv ℝ F z z) (heatPosterior F 1 0) := by
    refine (hg.norm.integrable_mul hz.norm).mono' ?_ ?_
    · have hc := (gradient_lipschitz_of_hessian_bounds hF hL hlo hup).continuous
      simpa only [inner_gradient_left, id_eq] using
        (hc.inner (𝕜 := ℝ) continuous_id).aestronglyMeasurable
    · filter_upwards [] with z
      rw [← inner_gradient_left]
      exact norm_inner_le_norm _ _
  have htrace : Integrable (fun z ↦ ‖z‖ ^ 2 + fderiv ℝ F z z)
      (heatPosterior F 1 0) := h2.add hdiag
  have hpoint (z : E) :
      ‖z‖ ^ 2 ≤ (‖z‖ ^ 2 + fderiv ℝ F z z) + ‖gradient F 0‖ * ‖z‖ := by
    have hm := gradient_monotone_of_hessian_bounds hF hlo hup z 0
    simp only [sub_zero, inner_sub_left, inner_gradient_left] at hm
    have hninner := neg_le_of_abs_le (abs_real_inner_le_norm (gradient F 0) z)
    rw [inner_gradient_left] at hninner
    linarith
  have hi := integral_mono h2 (htrace.add (hn.const_mul ‖gradient F 0‖)) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_add htrace (hn.const_mul ‖gradient F 0‖), integral_const_mul,
    integral_unit_posterior_trace hF hlo hup] at hi
  have hmean := integral_norm_le_sqrt_integral_norm_sq hz
  have hmean' := mul_le_mul_of_nonneg_left hmean (norm_nonneg (gradient F 0))
  have hs := Real.sq_sqrt (integral_nonneg (fun z : E ↦ sq_nonneg ‖z‖)
    (μ := heatPosterior F 1 0))
  have hd := Real.sq_sqrt (Nat.cast_nonneg (Module.finrank ℝ E) :
    (0 : ℝ) ≤ Module.finrank ℝ E)
  have hp := Real.sqrt_nonneg (∫ z, ‖z‖ ^ 2 ∂heatPosterior F 1 0)
  have hdp := Real.sqrt_nonneg (Module.finrank ℝ E : ℝ)
  have hgp := norm_nonneg (gradient F 0)
  nlinarith

/-- The source primitive RMS bound, proved by trace IBP and convexity without a mode. -/
theorem primitive_second_moment_le {F : E → ℝ} {L r : ℝ}
    (hF : ContDiff ℝ 2 F) (hL : 0 ≤ L)
    (hlo : ∀ y v, 0 ≤ fderiv ℝ (fderiv ℝ F) y v v)
    (hup : ∀ y v, fderiv ℝ (fderiv ℝ F) y v v ≤ L * ‖v‖ ^ 2)
    (hr : 0 < r) (x : E) :
    Real.sqrt (∫ z, ‖z‖ ^ 2 ∂primitiveLaw F x r) ≤
      Real.sqrt (Module.finrank ℝ E) + r * ‖gradient F x‖ := by
  have h := unit_posterior_second_moment_le (primitive_contDiff_affine_comp hF x r)
    (mul_nonneg (sq_nonneg r) hL) (primitive_affine_hessian_nonneg hF hlo x r)
    (primitive_affine_hessian_upper hF hup x r)
  simpa only [primitiveLaw, primitive_gradient_affine_comp (hF.differentiable (by norm_num)),
    smul_zero, add_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hr] using h


end AcceleratedLogConcave.Gibbs


noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace AcceleratedLogConcave.Gibbs

/-- Pushforward of a pulled-back density. -/
theorem map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {T : α → β} (hT : Measurable T)
    {w : β → ℝ≥0∞} (hw : Measurable w) :
    Measure.map T (μ.withDensity (fun z ↦ w (T z))) =
      (Measure.map T μ).withDensity w := by
  ext s hs
  rw [Measure.map_apply hT hs, withDensity_apply _ (hT hs),
    withDensity_apply _ hs, setLIntegral_map hs hw hT]

/-- A finite nonzero change-of-volume factor cancels in the normalized density.
This statement also respects the zero-measure convention at an infinite partition. -/
theorem map_normalized_withDensity_comp
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) {T : α → β} (hT : Measurable T)
    {w : β → ℝ≥0∞} (hw : Measurable w) {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hcTop : c ≠ ∞) (hmap : Measure.map T μ = c • ν) :
    Measure.map T ((∫⁻ z, w (T z) ∂μ)⁻¹ • μ.withDensity (fun z ↦ w (T z))) =
      (∫⁻ a, w a ∂ν)⁻¹ • ν.withDensity w := by
  have hZ : (∫⁻ z, w (T z) ∂μ) = c * ∫⁻ a, w a ∂ν := by
    rw [← lintegral_map hw hT, hmap, lintegral_smul_measure, smul_eq_mul]
  rw [Measure.map_smul _ hT.aemeasurable, map_withDensity_comp μ hT hw, hmap,
    withDensity_smul_measure, hZ, smul_smul]
  congr 1
  rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hcTop)]
  calc
    c⁻¹ * (∫⁻ a, w a ∂ν)⁻¹ * c =
        (∫⁻ a, w a ∂ν)⁻¹ * (c⁻¹ * c) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hc0 hcTop, mul_one]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Translation followed by a nonzero scalar dilation has the usual inverse
Jacobian on volume, including dimension zero. -/
theorem map_volume_primitive_affine (x : E) {r : ℝ} (hr : r ≠ 0) :
    Measure.map (fun z : E ↦ x + r • z) volume =
      ENNReal.ofReal (abs (r ^ Module.finrank ℝ E)⁻¹) • (volume : Measure E) := by
  have hc : (fun z : E ↦ x + r • z) = (fun z : E ↦ x + z) ∘ (fun z : E ↦ r • z) := rfl
  rw [hc, ← Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_addHaar_smul volume hr, Measure.map_smul _ (by fun_prop),
    Measure.IsAddLeftInvariant.map_add_left_eq_self]

/-- The affine image of the actual normalized primitive law is the Gaussian
posterior at physical variance `r²`. The inverse Jacobian cancels against the
same factor in the partition. -/
theorem primitiveLaw_map_affine {F : E → ℝ} (hF : Measurable F)
    {r : ℝ} (hr : r ≠ 0) (x : E) :
    Measure.map (fun z : E ↦ x + r • z) (primitiveLaw F x r) =
      heatPosterior F (r ^ 2) x := by
  let T : E → E := fun z ↦ x + r • z
  let w : E → ℝ≥0∞ := fun a ↦
    ENNReal.ofReal (Real.exp (-(F a + ‖a - x‖ ^ 2 / (2 * r ^ 2))))
  have hT : Measurable T := by fun_prop
  have hw : Measurable w := by fun_prop
  have hc : 0 < abs (r ^ Module.finrank ℝ E)⁻¹ :=
    abs_pos.mpr (inv_ne_zero (pow_ne_zero _ hr))
  have hnorm (z : E) : ‖x + r • z - x‖ ^ 2 / (2 * r ^ 2) =
      ‖z - 0‖ ^ 2 / (2 * 1) := by
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs, sub_zero, mul_one]
    field_simp
  have hcomp (z : E) : w (T z) =
      ENNReal.ofReal (Real.exp (-(F (x + r • z) + ‖z - 0‖ ^ 2 / (2 * 1)))) := by
    dsimp [w, T]
    rw [hnorm]
  have h := map_normalized_withDensity_comp (volume : Measure E) volume hT hw
    (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top
    (map_volume_primitive_affine x hr)
  simpa only [hcomp, primitiveLaw, heatPosterior, w, T] using h

end AcceleratedLogConcave.Gibbs


noncomputable section

namespace AcceleratedLogConcave.Gibbs

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The primitive mean is the actual heat score at variance `r²`. -/
theorem primitive_mean_eq_heat_score
    {F : E → ℝ} {L r : ℝ}
    (hF : ContDiff ℝ 2 F)
    (hlo : ∀ y v, 0 ≤ fderiv ℝ (fderiv ℝ F) y v v)
    (hup : ∀ y v, fderiv ℝ (fderiv ℝ F) y v v ≤ L * ‖v‖ ^ 2)
    (hr : 0 < r) (x : E) :
    primitiveMean F x r = gradient (heatPotential F (r ^ 2)) x := by
  have hgrad : Continuous (gradient F) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp
      (hF.continuous_fderiv (by norm_num))
  have hmap := integral_map_of_stronglyMeasurable
    (μ := primitiveLaw F x r)
    (show Measurable (fun z : E ↦ x + r • z) from
      (continuous_const.add (continuous_const.smul continuous_id)).measurable)
    hgrad.stronglyMeasurable
  rw [primitiveLaw_map_affine hF.continuous.measurable hr.ne' x] at hmap
  change (∫ z, gradient F (x + r • z) ∂primitiveLaw F x r) = _
  rw [← hmap]
  exact (heat_score_dictionary hF (m := 0) le_rfl (sq_pos_of_pos hr)
    (by simpa using hlo) hup x).1.symm

/-- The actual primitive mean inherits the original upper curvature bound. -/
theorem primitive_mean_lipschitz
    {F : E → ℝ} {L r : ℝ}
    (hF : ContDiff ℝ 2 F) (hL : 0 ≤ L)
    (hlo : ∀ y v, 0 ≤ fderiv ℝ (fderiv ℝ F) y v v)
    (hup : ∀ y v, fderiv ℝ (fderiv ℝ F) y v v ≤ L * ‖v‖ ^ 2)
    (hr : 0 < r) :
    LipschitzWith ⟨L, hL⟩ (fun x ↦ primitiveMean F x r) := by
  have hconv : ∀ y v, (0 : ℝ) * ‖v‖ ^ 2 ≤
      fderiv ℝ (fderiv ℝ F) y v v := by simpa using hlo
  have hcurv := heat_hessian_curvature hF (m := 0) le_rfl
    (sq_pos_of_pos hr) hconv hup
  have hheat := contDiff_two_heatPotential hF (m := 0) le_rfl
    (sq_pos_of_pos hr) hconv
  have hLip := gradient_lipschitz_of_hessian_bounds hheat hL
    (fun y v ↦ by simpa using (hcurv y v).1)
    (fun y v ↦ (hcurv y v).2)
  have heq : (fun x ↦ primitiveMean F x r) = gradient (heatPotential F (r ^ 2)) :=
    funext (primitive_mean_eq_heat_score hF hlo hup hr)
  rw [heq]
  exact hLip

end AcceleratedLogConcave.Gibbs


noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace ENNReal

namespace AcceleratedLogConcave.Gibbs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A standard Gaussian has the dimension as its exact squared norm moment. -/
theorem integral_norm_sq_stdGaussian :
    (∫ z : E, ‖z‖ ^ 2 ∂stdGaussian E) = (Module.finrank ℝ E : ℝ) := by
  let b := stdOrthonormalBasis ℝ E
  have hcoord (v : E) : ∫ z, (inner ℝ v z) ^ 2 ∂stdGaussian E = ‖v‖ ^ 2 := by
    have h := covarianceBilin_apply (IsGaussian.memLp_two_id (μ := stdGaussian E)) v v
    rw [covarianceBilin_stdGaussian] at h
    change inner ℝ v v = _ at h
    simpa only [integral_id_stdGaussian, id_eq, sub_zero, ← pow_two,
      real_inner_self_eq_norm_sq] using h.symm
  simp_rw [← b.sum_sq_inner_right]
  have hi (i : Fin (Module.finrank ℝ E)) :
      Integrable (fun z => inner ℝ (b i) z ^ 2) (stdGaussian E) := by
    simpa only [id_eq] using
      ((IsGaussian.memLp_two_id (μ := stdGaussian E)).const_inner (b i)).integrable_sq
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp only [hcoord, b.norm_eq_one, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- A Gaussian affine growth bound controls the exact second moment. -/
theorem integral_norm_sq_stdGaussian_le_of_affine_bound
    {f : E → E} (hf : Continuous f) (a b : ℝ)
    (hbound : ∀ z, ‖f z‖ ≤ a * ‖z‖ + b) :
    (∫ z, ‖f z‖ ^ 2 ∂stdGaussian E) ≤
      2 * a ^ 2 * (Module.finrank ℝ E : ℝ) + 2 * b ^ 2 := by
  have hpt (z : E) : ‖f z‖ ^ 2 ≤ 2 * a ^ 2 * ‖z‖ ^ 2 + 2 * b ^ 2 := by
    have hsq := (sq_le_sq₀ (norm_nonneg (f z))
      ((norm_nonneg (f z)).trans (hbound z))).mpr (hbound z)
    nlinarith [sq_nonneg (a * ‖z‖ - b)]
  have hz : Integrable (fun z : E => ‖z‖ ^ 2) (stdGaussian E) :=
    (memLp_two_iff_integrable_sq_norm
      (IsGaussian.memLp_two_id (μ := stdGaussian E)).aestronglyMeasurable).mp
        (IsGaussian.memLp_two_id (μ := stdGaussian E))
  have hu : Integrable (fun z : E => 2 * a ^ 2 * ‖z‖ ^ 2 + 2 * b ^ 2)
      (stdGaussian E) := (hz.const_mul (2 * a ^ 2)).add (integrable_const _)
  have hi : Integrable (fun z => ‖f z‖ ^ 2) (stdGaussian E) := by
    apply hu.mono' ((hf.norm.pow 2).aestronglyMeasurable)
    filter_upwards [] with z
    change |‖f z‖ ^ 2| ≤ _
    rw [abs_of_nonneg (sq_nonneg ‖f z‖)]
    exact hpt z
  have h := integral_mono hi hu hpt
  rw [integral_add (hz.const_mul _) (integrable_const _), integral_const_mul,
    integral_norm_sq_stdGaussian, integral_const, probReal_univ, one_smul] at h
  exact h

/-- A continuous affine-growth Gaussian observable belongs to the actual L² space. -/
theorem memLp_two_stdGaussian_of_affine_bound {f : E → E} (hf : Continuous f)
    (a b : ℝ) (hbound : ∀ z, ‖f z‖ ≤ a * ‖z‖ + b) :
    MemLp f 2 (stdGaussian E) := by
  have h : MemLp (fun z : E => a * ‖z‖ + b) 2 (stdGaussian E) := by
    simpa only [Pi.add_apply, id_eq] using!
      ((IsGaussian.memLp_two_id (μ := stdGaussian E)).norm.const_mul a).add (memLp_const b)
  exact h.mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall hbound)

/-- A concrete Gaussian RMS bound from a pointwise linear growth bound. -/
theorem gaussian_rms_le_two_of_affine_bound {f : E → E} (hf : Continuous f)
    {a D : ℝ} (ha : 0 ≤ a) (hD : Real.sqrt (Module.finrank ℝ E) ≤ D)
    (hbound : ∀ z, ‖f z‖ ≤ a * ‖z‖ + a * D) :
    Real.sqrt (∫ z, ‖f z‖ ^ 2 ∂stdGaussian E) ≤ 2 * a * D := by
  have hDn : 0 ≤ D := (Real.sqrt_nonneg _).trans hD
  have hDs : (Module.finrank ℝ E : ℝ) ≤ D ^ 2 := (Real.sqrt_le_iff.mp hD).2
  have hi := integral_norm_sq_stdGaussian_le_of_affine_bound hf a (a * D) hbound
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hm := mul_le_mul_of_nonneg_left hDs (by positivity : 0 ≤ 2 * a ^ 2)
    nlinarith

omit [BorelSpace E] in
/-- A posterior mean bias is controlled by a pointwise Lipschitz displacement
and the actual posterior second moment. -/
theorem norm_integral_sub_le_lipschitz_rms {μ : Measure E} [IsProbabilityMeasure μ]
    {g : E → E} (hg : Integrable g μ) (hz : MemLp (fun z : E => z) 2 μ)
    (c : E) {a : ℝ} (ha : 0 ≤ a) (hbound : ∀ z, ‖g z - c‖ ≤ a * ‖z‖) :
    ‖(∫ z, g z ∂μ) - c‖ ≤ a * Real.sqrt (∫ z, ‖z‖ ^ 2 ∂μ) := by
  have heq : (∫ z, g z ∂μ) - c = ∫ z, g z - c ∂μ := by
    rw [integral_sub hg (integrable_const c), integral_const, probReal_univ, one_smul]
  rw [heq]
  calc
    _ ≤ ∫ z, a * ‖z‖ ∂μ := norm_integral_le_of_norm_le
      (((hz.integrable (by norm_num)).norm).const_mul a) (Filter.Eventually.of_forall hbound)
    _ = a * ∫ z, ‖z‖ ∂μ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_norm_le_sqrt_integral_norm_sq hz) ha

omit [MeasurableSpace E] [BorelSpace E] in
/-- The exact displacement bound for the base score along a primitive coordinate. -/
theorem norm_primitive_score_sub_gradient_le {F : E → ℝ} {L r : ℝ}
    (hF : ContDiff ℝ 2 F) (hL : 0 ≤ L)
    (hlo : ∀ y v, 0 ≤ fderiv ℝ (fderiv ℝ F) y v v)
    (hup : ∀ y v, fderiv ℝ (fderiv ℝ F) y v v ≤ L * ‖v‖ ^ 2)
    (hr : 0 ≤ r) (x z : E) :
    ‖gradient F (x + r • z) - gradient F x‖ ≤ (L * r) * ‖z‖ := by
  have hl := gradient_lipschitz_of_hessian_bounds hF hL hlo hup
  have h := hl.dist_le_mul (x + r • z) x
  convert h using 1 <;> simp [dist_eq_norm, norm_smul, abs_of_nonneg hr, mul_assoc]
  exact Or.inl (NNReal.coe_mk L hL).symm

/-- The primitive mean bias is bounded using the actual primitive second moment. -/
theorem norm_primitiveMean_sub_gradient_le_rms {F : E → ℝ} {L r : ℝ}
    (hF : ContDiff ℝ 2 F) (hL : 0 ≤ L)
    (hlo : ∀ y v, 0 ≤ fderiv ℝ (fderiv ℝ F) y v v)
    (hup : ∀ y v, fderiv ℝ (fderiv ℝ F) y v v ≤ L * ‖v‖ ^ 2)
    (hr : 0 ≤ r) (x : E) :
    ‖primitiveMean F x r - gradient F x‖ ≤
      (L * r) * Real.sqrt (∫ z, ‖z‖ ^ 2 ∂primitiveLaw F x r) := by
  let := primitiveLaw_isProbabilityMeasure hF hlo x r
  exact norm_integral_sub_le_lipschitz_rms (primitive_integrable_score hF hL hlo hup x r)
    (MemLp.ae_eq (Filter.Eventually.of_forall (fun z => rfl))
      (primitive_memLp_two_id hF hlo x r))
    (gradient F x) (mul_nonneg hL hr) (norm_primitive_score_sub_gradient_le hF hL hlo hup hr x)

/-- The actual Gaussian-input score residual has a finite second moment. -/
theorem primitive_gaussian_score_error_memLp_two {F : E → ℝ} {L : ℝ}
    (hF : ContDiff ℝ 2 F) (hL : 0 ≤ L)
    (hlo : ∀ y v, 0 ≤ fderiv ℝ (fderiv ℝ F) y v v)
    (hup : ∀ y v, fderiv ℝ (fderiv ℝ F) y v v ≤ L * ‖v‖ ^ 2)
    (x : E) (r : ℝ) :
    MemLp (fun z => gradient F (x + r • z) - primitiveMean F x r) 2 (stdGaussian E) := by
  have hl := gradient_lipschitz_of_hessian_bounds hF hL hlo hup
  apply memLp_two_stdGaussian_of_affine_bound
    ((hl.continuous.comp (by fun_prop)).sub continuous_const)
    (L * |r|) ‖gradient F x - primitiveMean F x r‖
  intro z
  apply (norm_sub_le_norm_sub_add_norm_sub _ (gradient F x) _).trans
  apply add_le_add _ le_rfl
  have h := hl.dist_le_mul (x + r • z) x
  convert h using 1 <;> simp [dist_eq_norm, norm_smul, mul_assoc]
  exact Or.inl (NNReal.coe_mk L hL).symm

/-- Bias of the primitive mean at every center, with no base normalizability premise. -/
theorem norm_primitiveMean_sub_gradient_le {F : E → ℝ} {L r : ℝ}
    (hF : ContDiff ℝ 2 F) (hL : 0 ≤ L)
    (hlo : ∀ y v, 0 ≤ fderiv ℝ (fderiv ℝ F) y v v)
    (hup : ∀ y v, fderiv ℝ (fderiv ℝ F) y v v ≤ L * ‖v‖ ^ 2)
    (hr : 0 < r) (hrone : r ≤ 1) (x : E) :
    ‖primitiveMean F x r - gradient F x‖ ≤ (L * r) * primitiveScale F x := by
  calc
    _ ≤ (L * r) * Real.sqrt (∫ z, ‖z‖ ^ 2 ∂primitiveLaw F x r) :=
      norm_primitiveMean_sub_gradient_le_rms hF hL hlo hup hr.le x
    _ ≤ (L * r) * (Real.sqrt (Module.finrank ℝ E) + r * ‖gradient F x‖) :=
      mul_le_mul_of_nonneg_left (primitive_second_moment_le hF hL hlo hup hr x)
        (mul_nonneg hL hr.le)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (by dsimp [primitiveScale]; nlinarith [norm_nonneg (gradient F x)]) (mul_nonneg hL hr.le)

/-- A stronger coefficient-two Gaussian score residual bound; it implies the
coefficient-three bound stated in the manuscript. -/
theorem primitive_gaussian_score_rms_error_le_two {F : E → ℝ} {L r : ℝ}
    (hF : ContDiff ℝ 2 F) (hL : 0 ≤ L)
    (hlo : ∀ y v, 0 ≤ fderiv ℝ (fderiv ℝ F) y v v)
    (hup : ∀ y v, fderiv ℝ (fderiv ℝ F) y v v ≤ L * ‖v‖ ^ 2)
    (hr : 0 < r) (hrone : r ≤ 1) (x : E) :
    Real.sqrt (∫ z, ‖gradient F (x + r • z) - primitiveMean F x r‖ ^ 2
      ∂stdGaussian E) ≤ 2 * (L * r) * primitiveScale F x := by
  have hl := gradient_lipschitz_of_hessian_bounds hF hL hlo hup
  apply gaussian_rms_le_two_of_affine_bound
    ((hl.continuous.comp (by fun_prop)).sub continuous_const) (mul_nonneg hL hr.le)
    (by dsimp [primitiveScale]; exact le_add_of_nonneg_right (norm_nonneg _))
  intro z
  calc
    _ ≤ ‖gradient F (x + r • z) - gradient F x‖ +
        ‖gradient F x - primitiveMean F x r‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (L * r) * ‖z‖ + (L * r) * primitiveScale F x := by
      apply add_le_add (norm_primitive_score_sub_gradient_le hF hL hlo hup hr.le x z)
      rw [norm_sub_rev]
      exact norm_primitiveMean_sub_gradient_le hF hL hlo hup hr hrone x

/-- The source's Gaussian RMS score residual estimate, with coefficient three. -/
theorem primitive_gaussian_score_rms_error_le {F : E → ℝ} {L r : ℝ}
    (hF : ContDiff ℝ 2 F) (hL : 0 ≤ L)
    (hlo : ∀ y v, 0 ≤ fderiv ℝ (fderiv ℝ F) y v v)
    (hup : ∀ y v, fderiv ℝ (fderiv ℝ F) y v v ≤ L * ‖v‖ ^ 2)
    (hr : 0 < r) (hrone : r ≤ 1) (x : E) :
    Real.sqrt (∫ z, ‖gradient F (x + r • z) - primitiveMean F x r‖ ^ 2
      ∂stdGaussian E) ≤ 3 * (L * r) * primitiveScale F x := by
  apply (primitive_gaussian_score_rms_error_le_two hF hL hlo hup hr hrone x).trans
  have h := mul_nonneg (mul_nonneg hL hr.le) (primitiveScale_nonneg F x)
  nlinarith

end AcceleratedLogConcave.Gibbs
