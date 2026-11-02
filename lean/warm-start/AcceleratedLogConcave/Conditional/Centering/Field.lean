import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# The centering vector field

The argument `Kt` has the source's transpose convention: it is the integral
`∫ Bρ U₁(ρ,Yρ) dρ`, hence the first component below is `-Kt(Y) G / s`.
The field is locally Lipschitz with linear growth. No global Lipschitz
property of this coupled field is asserted.
-/
noncomputable section
open Set MeasureTheory
open scoped Topology NNReal

namespace AcceleratedLogConcave.Conditional.Centering
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Hilbert phase space, with the Euclidean sum norm. -/
abbrev Phase (E : Type*) := WithLp 2 (E × E)

/-- The actual stationary-centering differential expression. -/
def velocity (Kt : E → E →L[ℝ] E) (M : E → E) (u : E) (s : ℝ)
    (z : Phase E) : Phase E :=
  WithLp.toLp 2 (-(s⁻¹ • Kt z.fst z.snd), s⁻¹ • (M z.fst - u))

@[simp] theorem velocity_fst (Kt : E → E →L[ℝ] E) (M : E → E) (u : E) (s : ℝ)
    (z : Phase E) : (velocity Kt M u s z).fst = -(s⁻¹ • Kt z.fst z.snd) := rfl

@[simp] theorem velocity_snd (Kt : E → E →L[ℝ] E) (M : E → E) (u : E) (s : ℝ)
    (z : Phase E) : (velocity Kt M u s z).snd = s⁻¹ • (M z.fst - u) := rfl

/-- Smoothness is inherited from the transported kernel and conditional mean. -/
theorem contDiff_velocity {n : WithTop ℕ∞} {Kt : E → E →L[ℝ] E} {M : E → E}
    (hK : ContDiff ℝ n Kt) (hM : ContDiff ℝ n M) (u : E) (s : ℝ) :
    ContDiff ℝ n (velocity Kt M u s) := by
  apply WithLp.contDiff_toLp.comp
  have hf : ContDiff ℝ n (fun z : Phase E => z.fst) :=
    contDiff_fst.comp WithLp.contDiff_ofLp
  have hg : ContDiff ℝ n (fun z : Phase E => z.snd) :=
    contDiff_snd.comp WithLp.contDiff_ofLp
  exact (((hK.comp hf).clm_apply hg).const_smul s⁻¹).neg.prodMk
    ((hM.comp hf).sub contDiff_const |>.const_smul s⁻¹)

/-- The coupled field has the local regularity required for ODE uniqueness. -/
theorem locallyLipschitz_velocity {Kt : E → E →L[ℝ] E} {M : E → E}
    (hK : ContDiff ℝ 1 Kt) (hM : ContDiff ℝ 1 M) (u : E) (s : ℝ) :
    LocallyLipschitz (velocity Kt M u s) :=
  (contDiff_velocity hK hM u s).locallyLipschitz

omit [InnerProductSpace ℝ E] in
private theorem norm_phase_le_sum (z : Phase E) : ‖z‖ ≤ ‖z.fst‖ + ‖z.snd‖ := by
  have h := WithLp.prod_norm_sq_eq_of_L2 z
  nlinarith [norm_nonneg z, norm_nonneg z.fst, norm_nonneg z.snd]

/-- Linear growth follows from bounded `Kt` and Lipschitz `M`; no bound on the
spatial derivative of the complete coupled field is needed. -/
theorem norm_velocity_le {Kt : E → E →L[ℝ] E} {M : E → E} {A : ℝ} {B : ℝ≥0}
    (hA : 0 ≤ A) (hK : ∀ y, ‖Kt y‖ ≤ A) (hM : LipschitzWith B M)
    (u : E) {s : ℝ} (hs : 0 < s) (z : Phase E) :
    ‖velocity Kt M u s z‖ ≤
      s⁻¹ * ((A + B) * ‖z‖ + ‖M 0 - u‖) := by
  have hMean : ‖M z.fst - u‖ ≤ (B : ℝ) * ‖z.fst‖ + ‖M 0 - u‖ := by
    calc
      _ ≤ ‖M z.fst - M 0‖ + ‖M 0 - u‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (B : ℝ) * ‖z.fst‖ + ‖M 0 - u‖ := by
        simpa only [dist_eq_norm, sub_zero] using
          add_le_add (hM.dist_le_mul z.fst 0) (le_refl ‖M 0 - u‖)
  calc
    _ ≤ ‖(velocity Kt M u s z).fst‖ + ‖(velocity Kt M u s z).snd‖ :=
      norm_phase_le_sum _
    _ = s⁻¹ * (‖Kt z.fst z.snd‖ + ‖M z.fst - u‖) := by
      simp [norm_smul, abs_of_pos hs, mul_add]
    _ ≤ s⁻¹ * (A * ‖z.snd‖ + ((B : ℝ) * ‖z.fst‖ + ‖M 0 - u‖)) := by
      gcongr
      exact (Kt z.fst).le_opNorm z.snd |>.trans
        (mul_le_mul_of_nonneg_right (hK z.fst) (norm_nonneg _))
    _ ≤ s⁻¹ * ((A + B) * ‖z‖ + ‖M 0 - u‖) := by
      have hf := WithLp.norm_fst_le E z
      have hg := WithLp.norm_snd_le E z
      have hb := B.coe_nonneg
      nlinarith [mul_le_mul_of_nonneg_left hf hb,
        mul_le_mul_of_nonneg_left hg hA, inv_nonneg.mpr hs.le]

/-- Exact decomposition of the speed in the Hilbert phase norm. -/
theorem norm_velocity_sq (Kt : E → E →L[ℝ] E) (M : E → E) (u : E) (s : ℝ)
    (z : Phase E) :
    ‖velocity Kt M u s z‖ ^ 2 =
      (s⁻¹) ^ 2 * (‖Kt z.fst z.snd‖ ^ 2 + ‖M z.fst - u‖ ^ 2) := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp [norm_smul, mul_pow, mul_add]

end AcceleratedLogConcave.Conditional.Centering
