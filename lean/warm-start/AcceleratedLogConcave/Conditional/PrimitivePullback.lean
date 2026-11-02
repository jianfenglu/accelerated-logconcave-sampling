import AcceleratedLogConcave.Conditional.Definitions

noncomputable section
namespace AcceleratedLogConcave.Conditional
open MeasureTheory ProbabilityTheory
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem contDiff_primitivePotential {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (x : E) (r : ℝ) : ContDiff ℝ 2 (primitivePotential F x r) :=
  hF.comp (contDiff_const.add (contDiff_const.smul contDiff_id))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem fderiv_primitivePotential (F : E → ℝ) (x z : E) (r : ℝ) :
    fderiv ℝ (primitivePotential F x r) z = r • fderiv ℝ F (x + r • z) := by
  exact (fderiv_comp_smul (𝕜 := ℝ) (f := fun w ↦ F (x + w)) (x := z) r).trans
    (congrArg (fun D : E →L[ℝ] ℝ ↦ r • D) (fderiv_comp_add_left x))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem hessian_primitivePotential {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (x z a b : E) (r : ℝ) :
    fderiv ℝ (fderiv ℝ (primitivePotential F x r)) z a b =
      r ^ 2 * fderiv ℝ (fderiv ℝ F) (x + r • z) a b := by
  have heq : fderiv ℝ (primitivePotential F x r) =
      fun z ↦ r • fderiv ℝ F (x + r • z) := funext (fun z ↦
        fderiv_primitivePotential F x z r)
  have hd : DifferentiableAt ℝ (fun z ↦ fderiv ℝ F (x + r • z)) z := by
    apply ((hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)).differentiableAt.comp
    exact ((hasFDerivAt_id z).const_smul r |>.const_add x).differentiableAt
  have hscale := fderiv_fun_const_smul hd r
  have hchain := (fderiv_comp_smul (𝕜 := ℝ)
    (f := fun w ↦ fderiv ℝ F (x + w)) (x := z) r).trans
    (congrArg (fun D : E →L[ℝ] (E →L[ℝ] ℝ) ↦ r • D) (fderiv_comp_add_left x))
  rw [heq, hscale, hchain]
  simp only [smul_apply, smul_eq_mul]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem primitivePotential_hessian_nonneg {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a) (x : E) (r : ℝ) :
    ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ (primitivePotential F x r)) z a a := by
  intro z a
  rw [hessian_primitivePotential hF]
  exact mul_nonneg (sq_nonneg r) (hlo _ _)

theorem conditionalLaw_isProbabilityMeasure {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (x : E) (r : ℝ) {ρ : ℝ} (hρlo : -1 < ρ) (hρhi : ρ < 1) (y : E) :
    IsProbabilityMeasure (conditionalLaw F x r ρ y) := by
  apply Gibbs.heatPosterior_isProbabilityMeasure (contDiff_primitivePotential hF x r)
    (m := 0) (le_refl 0) (conditionalVariance_pos hρlo hρhi)
  simpa using primitivePotential_hessian_nonneg hF hlo x r

omit [MeasurableSpace E] [BorelSpace E] in
/-- Pulling back the potential scales its gradient by `r`, whereas the primitive
observable itself is the unscaled original gradient. -/
theorem gradient_primitivePotential (F : E → ℝ) (x z : E) (r : ℝ) :
    gradient (primitivePotential F x r) z = r • primitiveObservable F x r z := by
  simp only [gradient, primitiveObservable, fderiv_primitivePotential, map_smul]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem primitivePotential_hessian_upper {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {L : ℝ} (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ L * ‖a‖ ^ 2)
    (x : E) (r : ℝ) : ∀ z a,
    fderiv ℝ (fderiv ℝ (primitivePotential F x r)) z a a ≤ (r ^ 2 * L) * ‖a‖ ^ 2 := by
  intro z a
  rw [hessian_primitivePotential hF]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hup (x + r • z) a) (sq_nonneg r)

omit [MeasurableSpace E] [BorelSpace E] in
theorem continuous_primitiveObservable {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (x : E) (r : ℝ) : Continuous (primitiveObservable F x r) := by
  exact ((InnerProductSpace.toDual ℝ E).symm.continuous.comp
    (hF.continuous_fderiv (by norm_num))).comp
      (continuous_const.add (continuous_const.smul continuous_id))

omit [MeasurableSpace E] [BorelSpace E] in
/-- Original C² Hessian bounds give the affine observable envelope needed for
conditional differentiation; no higher derivatives of `F` enter. -/
theorem norm_primitiveObservable_le_affine {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {L : ℝ} (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ L * ‖a‖ ^ 2)
    (x : E) (r : ℝ) (z : E) :
    ‖primitiveObservable F x r z‖ ≤
      (‖gradient F 0‖ + |L| * ‖x‖) + (|L| * |r|) * ‖z‖ := by
  have h := Gibbs.norm_gradient_le_affine_of_hessian_bounds hF
    (m := 0) (by simpa using hlo) hup (x + r • z)
  simp only [abs_zero, max_eq_right (abs_nonneg L)] at h
  calc
    ‖primitiveObservable F x r z‖ ≤ ‖gradient F 0‖ + |L| * ‖x + r • z‖ := h
    _ ≤ ‖gradient F 0‖ + |L| * (‖x‖ + |r| * ‖z‖) := by
      gcongr
      simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le x (r • z)
    _ = _ := by ring

end AcceleratedLogConcave.Conditional
