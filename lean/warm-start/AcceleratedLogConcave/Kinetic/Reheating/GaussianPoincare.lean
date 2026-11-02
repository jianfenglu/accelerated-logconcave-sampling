import AcceleratedLogConcave.Gibbs.Poincare
import AcceleratedLogConcave.Channels.GaussianForward
import Mathlib.Analysis.Calculus.FDeriv.Norm

/-! Actual Gaussian Poincare for classical tests, from W02. The two Gaussian
Fourier adapters generalize the proofs in Channels/GaussianForward.lean from
Euclidean coordinates to an arbitrary finite-dimensional real Hilbert space. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace Complex
open scoped RealInnerProductSpace ContDiff
namespace AcceleratedLogConcave.Kinetic.Reheating
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma integrable_gaussian_weight_general (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : E ↦ Real.exp (-b * ‖x‖ ^ 2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (show 0 < (b : ℂ).re from hb) 0 (0 : E)).norm
  simpa [Complex.norm_exp, ← Complex.ofReal_pow] using h

lemma charFun_gaussian_tilt_general (b : ℝ) (hb : 0 < b) (w : E) :
    charFun (volume.tilted (fun x : E ↦ -b * ‖x‖ ^ 2)) w =
      Complex.exp (-((‖w‖ ^ 2 : ℝ) : ℂ) / (4 * (b : ℂ))) := by
  let Z : ℝ := ∫ x : E, Real.exp (-b * ‖x‖ ^ 2)
  have hZ : Z ≠ 0 := (integral_exp_pos (integrable_gaussian_weight_general (E := E) b hb)).ne'
  have hZc : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ
  have hc : (Z : ℂ) = (Real.pi / (b : ℂ)) ^
      (Module.finrank ℝ (E) / 2 : ℂ) := by
    dsimp only [Z]
    rw [← integral_complex_ofReal]
    convert GaussianFourier.integral_cexp_neg_mul_sq_norm
      (show 0 < (b : ℂ).re from hb) (V := E) using 1
    congr 1
    ext x
    simp
  rw [charFun_apply, integral_tilted]
  change (∫ x : E,
    (Real.exp (-b * ‖x‖ ^ 2) / Z) • Complex.exp ((inner ℝ x w : ℝ) * Complex.I)) = _
  calc
    _ = (Z : ℂ)⁻¹ * ∫ x : E,
        Complex.exp (-(b : ℂ) * ‖x‖ ^ 2 + Complex.I * (inner ℝ w x : ℝ)) := by
      rw [← integral_const_mul]
      congr 1
      ext x
      rw [Complex.exp_add, real_inner_comm w x]
      simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_exp,
        Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow]
      ring_nf
    _ = _ := by
      rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add
        (show 0 < (b : ℂ).re from hb), ← hc, ← mul_assoc, inv_mul_cancel₀ hZc, one_mul]
      simp [Complex.I_sq]


/-- The standard Gaussian is the actual normalized quadratic Gibbs law. -/
theorem stdGaussian_eq_quadratic_tilted :
    stdGaussian E = volume.tilted (fun x : E => -(‖x‖^2/2)) := by
  have he : (fun x : E => -(‖x‖^2/2)) = (fun x => -(1/2 : ℝ)*‖x‖^2) := by
    funext x
    ring
  rw [he]
  apply Measure.ext_of_charFun
  ext w
  rw [charFun_stdGaussian, charFun_gaussian_tilt_general (1/2) (by norm_num)]
  congr 1
  push_cast
  ring

/-- The literal quadratic potential, in the same convention as W02. -/
def gaussianPotential (x : E) : ℝ := ‖x‖^2/2

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem gaussianPotential_smooth : ContDiff ℝ ∞ (gaussianPotential (E := E)) :=
  (contDiff_norm_sq ℝ).div_const 2

theorem gaussianPotential_integrable : Integrable (fun x : E => Real.exp (-gaussianPotential x)) := by
  convert integrable_gaussian_weight_general (E := E) (1/2) (by norm_num) using 1
  funext x
  congr 1
  simp only [gaussianPotential]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem gaussianPotential_fderiv (x : E) : fderiv ℝ gaussianPotential x = innerSL ℝ x := by
  have h := ((hasFDerivAt_id (𝕜 := ℝ) x).norm_sq).mul_const (2 : ℝ)⁻¹
  have he : HasFDerivAt gaussianPotential (innerSL ℝ x) x := by
    convert h using 1
    · funext y
      simp [gaussianPotential, div_eq_mul_inv]
    · ext v
      simp
  exact he.fderiv

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem gaussianPotential_hessian (x a : E) :
    fderiv ℝ (fderiv ℝ gaussianPotential) x a a = ‖a‖^2 := by
  have he : fderiv ℝ (gaussianPotential (E := E)) = innerSL ℝ := funext gaussianPotential_fderiv
  rw [he, (innerSL ℝ).fderiv]
  exact real_inner_self_eq_norm_sq a

/-- Sharp Gaussian Poincare for genuine C1 functions with L2 value and gradient. -/
theorem gaussian_c1_poincare (f : E → ℝ) (hf : ContDiff ℝ 1 f)
    (hp : MemLp f 2 (stdGaussian E)) (hq : MemLp (gradient f) 2 (stdGaussian E)) :
    (∫ x, (f x - ∫ y, f y ∂stdGaussian E)^2 ∂stdGaussian E) ≤
      ∫ x, ‖gradient f x‖^2 ∂stdGaussian E := by
  have h := Gibbs.c1_variance_poincare (stdGaussian E) gaussianPotential
    (gaussianPotential_smooth.of_le (by norm_num)) gaussianPotential_integrable
    stdGaussian_eq_quadratic_tilted 1 1 zero_lt_one
    (fun x a => by rw [gaussianPotential_hessian]; simp)
    (fun x a => by rw [gaussianPotential_hessian]; simp) f hf hp hq
  simpa only [one_mul] using h

end AcceleratedLogConcave.Kinetic.Reheating
