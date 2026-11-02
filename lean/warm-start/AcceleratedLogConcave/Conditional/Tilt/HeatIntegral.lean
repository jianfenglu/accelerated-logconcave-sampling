import AcceleratedLogConcave.Conditional.Tilt.GaussianIntegral

/-!
# All-order regularity of normalized Gaussian posterior expectations

Square completion converts the actual posterior to natural Gaussian parameters.
The common scalar factor cancels only after positivity is established.
-/

noncomputable section
namespace AcceleratedLogConcave.Conditional.Tilt

open MeasureTheory Set
open scoped RealInnerProductSpace ContDiff

universe u v
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Gaussian natural parameters of a positive variance and an arbitrary center. -/
def posteriorParameters (p : ℝ × E) : ℝ × E := ((2 * p.1)⁻¹, p.1⁻¹ • p.2)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem posterior_density_eq_natural (B : E → ℝ) (t : ℝ) (c z : E) (ht : t ≠ 0) :
    Real.exp (-(B z + ‖z - c‖ ^ 2 / (2 * t))) =
      Real.exp (-‖c‖ ^ 2 / (2 * t)) *
        Real.exp (-B z + gaussianStatistic z (posteriorParameters (t, c))) := by
  rw [← Real.exp_add]
  congr 1
  simp only [gaussianStatistic_apply, posteriorParameters, inner_smul_right,
    norm_sub_sq_real]
  field_simp
  ring

/-- Normalized Gaussian expectation in natural parameters. -/
def normalizedGaussianIntegral {G : Type v} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E → ℝ) (g : E → G) (p : ℝ × E) : G :=
  (gaussianIntegral B (fun _ ↦ (1 : ℝ)) p)⁻¹ • gaussianIntegral B g p

/-- All orders of normalized Gaussian parameter differentiation. -/
theorem contDiffOn_normalizedGaussianIntegral
    {G : Type v} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {B : E → ℝ} {g : E → G} (hB : Continuous B) (hc : Continuous g)
    (hg : HasGaussianMoments B g) (h1 : HasGaussianMoments B (fun _ ↦ (1 : ℝ))) :
    ContDiffOn ℝ ∞ (normalizedGaussianIntegral B g) gaussianDomain := by
  have hZ := contDiffOn_gaussianIntegral hB continuous_const h1
  have hn := contDiffOn_gaussianIntegral hB hc hg
  have hz (p : ℝ × E) (hp : p ∈ gaussianDomain) :
      gaussianIntegral B (fun _ ↦ (1 : ℝ)) p ≠ 0 := by
    have hi := integrable_gaussian_integrand hB continuous_const h1 p hp
    simp only [smul_eq_mul, mul_one] at hi
    simpa only [gaussianIntegral, smul_eq_mul, mul_one] using (integral_exp_pos hi).ne'
  exact (hZ.inv hz).smul hn

/-- The normalized natural integral equals the actual Gibbs posterior mean. -/
theorem integral_heatPosterior_eq_normalizedGaussianIntegral
    {G : Type v} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {B : E → ℝ} {m t : ℝ} (hB : ContDiff ℝ 2 B) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ B) z v v)
    (g : E → G) (c : E) :
    (∫ z, g z ∂Gibbs.heatPosterior B t c) =
      normalizedGaussianIntegral B g (posteriorParameters (t, c)) := by
  rw [Gibbs.integral_heatPosterior hB hm ht hlo]
  let K := Real.exp (-‖c‖ ^ 2 / (2 * t))
  have hK : K ≠ 0 := Real.exp_ne_zero _
  have hn : (∫ z, Real.exp (-(B z + ‖z - c‖ ^ 2 / (2 * t))) • g z) =
      K • gaussianIntegral B g (posteriorParameters (t, c)) := by
    simp_rw [posterior_density_eq_natural B t c _ ht.ne', mul_smul]
    exact integral_smul K _
  have hz : (∫ z, Real.exp (-(B z + ‖z - c‖ ^ 2 / (2 * t)))) =
      K * gaussianIntegral B (fun _ ↦ (1 : ℝ)) (posteriorParameters (t, c)) := by
    simp_rw [posterior_density_eq_natural B t c _ ht.ne']
    simpa only [gaussianIntegral, smul_eq_mul, mul_one] using integral_const_mul K _
  rw [hn, hz, mul_inv_rev, smul_smul]
  simp only [normalizedGaussianIntegral, mul_assoc, inv_mul_cancel₀ hK, mul_one]

/-- The positive-variance posterior expectation is jointly smooth in variance
and center for every continuous observable of polynomial growth. -/
theorem contDiffOn_integral_heatPosterior
    {G : Type v} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {B : E → ℝ} {m : ℝ} (hB : ContDiff ℝ 2 B) (hm : 0 ≤ m)
    (hlo : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ B) z v v)
    {g : E → G} (hc : Continuous g) (A C : ℝ) (k : ℕ)
    (hbound : ∀ z, ‖g z‖ ≤ A + C * ‖z‖ ^ k) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ ∫ z, g z ∂Gibbs.heatPosterior B p.1 p.2)
      gaussianDomain := by
  have hlower (z : E) : B 0 + inner ℝ (gradient B 0) z ≤ B z := by
    have hh := Gibbs.quadratic_lower_bound_of_hessian_lower hB hlo z
    rw [← inner_gradient_left] at hh
    have hn : 0 ≤ m / 2 * ‖z‖ ^ 2 := by positivity
    linarith
  have hg := hasGaussianMoments_of_polynomial_growth hB.continuous hc
    (B 0) (gradient B 0) hlower A C k hbound
  have h1 := hasGaussianMoments_of_polynomial_growth hB.continuous
    (continuous_const : Continuous (fun _ : E ↦ (1 : ℝ)))
    (B 0) (gradient B 0) hlower 1 0 0 (by intro z; simp)
  have hnat := contDiffOn_normalizedGaussianIntegral hB.continuous hc hg h1
  have hp : ContDiffOn ℝ ∞ (posteriorParameters (E := E)) gaussianDomain := by
    have ht : ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ p.1) gaussianDomain :=
      contDiff_fst.contDiffOn
    have hinv := ht.inv (fun p hp ↦ ne_of_gt hp)
    exact ((contDiffOn_const.mul ht).inv (by
      intro p hp
      exact mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hp))).prodMk
      (hinv.smul contDiff_snd.contDiffOn)
  have hmap : MapsTo (posteriorParameters (E := E)) gaussianDomain gaussianDomain := by
    intro p hp
    change 0 < (2 * p.1)⁻¹
    exact inv_pos.mpr (mul_pos (by norm_num) hp)
  exact (hnat.comp hp hmap).congr fun p hpt ↦
    integral_heatPosterior_eq_normalizedGaussianIntegral hB hm hpt hlo g p.2

/-- At every positive fixed variance the actual posterior mean is smooth on
all centers. -/
theorem contDiff_integral_heatPosterior
    {G : Type v} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {B : E → ℝ} {m t : ℝ} (hB : ContDiff ℝ 2 B) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ B) z v v)
    {g : E → G} (hc : Continuous g) (A C : ℝ) (k : ℕ)
    (hbound : ∀ z, ‖g z‖ ≤ A + C * ‖z‖ ^ k) :
    ContDiff ℝ ∞ (fun c ↦ ∫ z, g z ∂Gibbs.heatPosterior B t c) := by
  have hs := contDiffOn_integral_heatPosterior hB hm hlo hc A C k hbound
  apply contDiff_iff_contDiffAt.mpr
  intro c
  have hsAt : ContDiffAt ℝ ∞
      (fun p : ℝ × E ↦ ∫ z, g z ∂Gibbs.heatPosterior B p.1 p.2) (t, c) :=
    hs.contDiffAt (isOpen_gaussianDomain.mem_nhds ht)
  convert hsAt.comp c (contDiffAt_const.prodMk contDiffAt_id) using 1
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Taking any number of derivatives in the center preserves joint smoothness
in the variance and center. This is a partial-derivative statement. -/
theorem contDiffAt_iterated_center_deriv
    {G : Type v} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : ℝ × E → G}
    (hf : ∀ p : ℝ × E, 0 < p.1 → ContDiffAt ℝ ∞ f p)
    (q : ℕ) (p : ℝ × E) (hp : 0 < p.1) :
    ContDiffAt ℝ ∞
      (fun p : ℝ × E ↦ iteratedFDeriv ℝ q (fun c ↦ f (p.1, c)) p.2) p := by
  induction q generalizing p with
  | zero =>
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    exact (continuousMultilinearCurryFin0 ℝ E G).symm.contDiff.contDiffAt.comp p (hf p hp)
  | succ q ih =>
    have haux : ContDiffAt ℝ ∞
        (Function.uncurry (fun p : ℝ × E ↦
          fun c : E ↦ iteratedFDeriv ℝ q (fun z ↦ f (p.1, z)) c)) (p, p.2) := by
      convert (ih p hp).comp (p, p.2)
        ((contDiffAt_fst.fst).prodMk contDiffAt_snd) using 1
      rfl
    have hd := haux.fderiv (contDiffAt_snd :
      ContDiffAt ℝ ∞ (fun p : ℝ × E ↦ p.2) p) (by simp)
    simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (q + 1) ↦ E) G).symm.contDiff.contDiffAt.comp p hd

/-- The division-free center jets are smooth in all positive variances. -/
theorem contDiffOn_centerJet_integral_heatPosterior
    {G : Type v} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {B : E → ℝ} {m : ℝ} (hB : ContDiff ℝ 2 B) (hm : 0 ≤ m)
    (hlo : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ B) z v v)
    {g : E → G} (hc : Continuous g) (A C : ℝ) (k q : ℕ)
    (hbound : ∀ z, ‖g z‖ ≤ A + C * ‖z‖ ^ k) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × E ↦ iteratedFDeriv ℝ q
        (fun c ↦ ∫ z, g z ∂Gibbs.heatPosterior B p.1 c) p.2) gaussianDomain := by
  have hs := contDiffOn_integral_heatPosterior hB hm hlo hc A C k hbound
  intro p hp
  exact (contDiffAt_iterated_center_deriv (fun p hp ↦
    hs.contDiffAt (isOpen_gaussianDomain.mem_nhds hp)) q p hp).contDiffWithinAt

end AcceleratedLogConcave.Conditional.Tilt
