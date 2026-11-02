import AcceleratedLogConcave.Conditional.Centering.Field
import AcceleratedLogConcave.Conditional.Centering.LocalFlow
import AcceleratedLogConcave.Conditional.Centering.Output

/-!
# Centering ODE on the Hilbert phase space

Finite forward and backward horizons are constructed from smoothness and
linear growth. The auxiliary globally Lipschitz cutoff is internal to the proof;
the complete coupled centering field is only locally Lipschitz.

The stationary-product-law theorem and its discharge for the actual transported
Stein kernel remain separate obligations. The modular output-law lemmas below
state their endpoint-law input explicitly and do not assert stationarity.
-/
noncomputable section
open Set MeasureTheory
open scoped Topology NNReal

namespace AcceleratedLogConcave.Conditional.Centering
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The actual centering vector field reaches every prescribed finite forward horizon. -/
theorem exists_centering_curve_forward {Kt : E → E →L[ℝ] E} {M : E → E}
    (hKt : ContDiff ℝ 1 Kt) (hM : ContDiff ℝ 1 M)
    {A : ℝ} (hA : 0 ≤ A) (hbound : ∀ y, ‖Kt y‖ ≤ A)
    {B : ℝ≥0} (hlip : LipschitzWith B M) (u : E) {s : ℝ} (hs : 0 < s)
    {a b : ℝ} (hab : a ≤ b) (z : Phase E) :
    ∃ Z : ℝ → Phase E, Continuous Z ∧ Z a = z ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt Z (velocity Kt M u s (Z t)) (Icc a b) t := by
  apply exists_curve_of_contDiff_linear_growth (contDiff_velocity hKt hM u s)
    (C := s⁻¹ * (A + B)) (D := s⁻¹ * ‖M 0 - u‖)
  · positivity
  · positivity
  · intro q
    simpa only [mul_add, add_mul, mul_assoc] using norm_velocity_le hA hbound hlip u hs q
  · exact hab

/-- The same field reaches every prescribed finite backward horizon. -/
theorem exists_centering_curve_backward {Kt : E → E →L[ℝ] E} {M : E → E}
    (hKt : ContDiff ℝ 1 Kt) (hM : ContDiff ℝ 1 M)
    {A : ℝ} (hA : 0 ≤ A) (hbound : ∀ y, ‖Kt y‖ ≤ A)
    {B : ℝ≥0} (hlip : LipschitzWith B M) (u : E) {s : ℝ} (hs : 0 < s)
    {a b : ℝ} (hab : a ≤ b) (z : Phase E) :
    ∃ Z : ℝ → Phase E, Continuous Z ∧ Z b = z ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt Z (velocity Kt M u s (Z t)) (Icc a b) t := by
  apply exists_curve_backward_of_contDiff_linear_growth (contDiff_velocity hKt hM u s)
    (C := s⁻¹ * (A + B)) (D := s⁻¹ * ‖M 0 - u‖)
  · positivity
  · positivity
  · intro q
    simpa only [mul_add, add_mul, mul_assoc] using norm_velocity_le hA hbound hlip u hs q
  · exact hab

section Global
variable {Kt : E → E →L[ℝ] E} {M : E → E}
    (hKt : ContDiff ℝ 1 Kt) (hM : ContDiff ℝ 1 M)
    {A : ℝ} (hA : 0 ≤ A) (hbound : ∀ y, ‖Kt y‖ ≤ A)
    {B : ℝ≥0} (hlip : LipschitzWith B M) (u : E) {s : ℝ} (hs : 0 < s)

include hA hbound hlip hs in
omit [FiniteDimensional ℝ E] in
private theorem growth_centering (q : Phase E) :
    ‖velocity Kt M u s q‖ ≤ (s⁻¹ * (A+B)) * ‖q‖ + s⁻¹ * ‖M 0-u‖ := by
  convert! norm_velocity_le hA hbound hlip u hs q using 1
  ring

/-- The canonical actual centering trajectory, defined at every real time. -/
def centeringFlow (z : Phase E) : ℝ → Phase E :=
  completeCurve (contDiff_velocity hKt hM u s)
    (C := s⁻¹ * (A+B)) (D := s⁻¹ * ‖M 0-u‖)
    (by positivity) (by positivity) (growth_centering hA hbound hlip u hs) z

/-- The all-real-time construction has the prescribed input. -/
theorem centeringFlow_initial (z : Phase E) :
    centeringFlow hKt hM hA hbound hlip u hs z 0 = z :=
  completeCurve_initial _ _ _ _ z

/-- The constructed trajectory solves both centering equations at all real times. -/
theorem centeringFlow_deriv (z : Phase E) (t : ℝ) :
    HasDerivAt (centeringFlow hKt hM hA hbound hlip u hs z)
      (velocity Kt M u s (centeringFlow hKt hM hA hbound hlip u hs z t)) t :=
  completeCurve_deriv _ _ _ _ z t

theorem centeringFlow_continuous (z : Phase E) :
    Continuous (centeringFlow hKt hM hA hbound hlip u hs z) :=
  completeCurve_continuous _ _ _ _ z

/-- The complete centering flow is a spatial C1 homeomorphism. -/
def centeringFlowHomeomorph (t : ℝ) : Phase E ≃ₜ Phase E :=
  completeFlowHomeomorph (contDiff_velocity hKt hM u s)
    (C := s⁻¹ * (A+B)) (D := s⁻¹ * ‖M 0-u‖)
    (by positivity) (by positivity) (growth_centering hA hbound hlip u hs) t

/-- Integration retains exactly the originally supplied momentum. -/
theorem centeringFlow_integrated_output (z : Phase E) :
    s • z.snd + ∫ t in (0 : ℝ)..1, M (centeringFlow hKt hM hA hbound hlip u hs z t).fst =
      u + s • (centeringFlow hKt hM hA hbound hlip u hs z 1).snd := by
  have hh := integrated_output_unit hs.ne' (fun t _ => centeringFlow_deriv hKt hM hA hbound hlip u hs z t)
    hM.continuous (centeringFlow_continuous hKt hM hA hbound hlip u hs z)
  rw [centeringFlow_initial] at hh
  exact hh

end Global

end AcceleratedLogConcave.Conditional.Centering
