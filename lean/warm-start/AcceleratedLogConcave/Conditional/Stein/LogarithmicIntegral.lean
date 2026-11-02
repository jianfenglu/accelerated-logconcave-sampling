import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! Zero-endpoint calculus for the transported Stein kernel. A derivative curve
vanishing at zero has an integrable divided derivative; integration by parts
then produces the logarithmic weight without an unproved boundary term. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace AcceleratedLogConcave.Conditional.Stein
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

open scoped Classical in
/-- The divided difference with its within-derivative value at zero. -/
def zeroSlopeExtension (f : ℝ → E) (v : E) : ℝ → E :=
  Function.update (slope f 0) 0 v

omit [CompleteSpace E] in
theorem continuousOn_zeroSlopeExtension {f : ℝ → E} {v : E} {b : ℝ}
    (hf : ContinuousOn f (Icc 0 b)) (hd : HasDerivWithinAt f v (Icc 0 b) 0) :
    ContinuousOn (zeroSlopeExtension f v) (Icc 0 b) := by
  classical
  intro t ht
  by_cases h : t = 0
  · subst t
    simpa only [zeroSlopeExtension, continuousWithinAt_update_same] using
      (hasDerivWithinAt_iff_tendsto_slope.mp hd)
  · rw [zeroSlopeExtension, continuousWithinAt_update_of_ne h]
    exact ((continuousWithinAt_id.sub continuousWithinAt_const).inv₀ (sub_ne_zero.mpr h)).smul
      ((hf t ht).sub continuousWithinAt_const)

omit [CompleteSpace E] in
theorem smul_zeroSlopeExtension {f : ℝ → E} (v : E) (t : ℝ) :
    t • zeroSlopeExtension f v t = f t - f 0 := by
  classical
  by_cases h : t = 0
  · subst t; simp
  · simp only [zeroSlopeExtension, Function.update_of_ne h, slope, sub_zero,
      vsub_eq_sub, smul_smul, mul_inv_cancel₀ h, one_smul]

omit [CompleteSpace E] in
theorem intervalIntegrable_inv_smul_of_zero_within {f : ℝ → E} {v : E} {b : ℝ}
    (hb : 0 ≤ b) (hf : ContinuousOn f (Icc 0 b))
    (hd : HasDerivWithinAt f v (Icc 0 b) 0) (h0 : f 0 = 0) :
    IntervalIntegrable (fun t => t⁻¹ • f t) volume 0 b := by
  classical
  have hi : IntervalIntegrable (zeroSlopeExtension f v) volume 0 b :=
    (show ContinuousOn (zeroSlopeExtension f v) (uIcc 0 b) by
    simpa only [uIcc_of_le hb] using continuousOn_zeroSlopeExtension hf hd).intervalIntegrable
  apply hi.congr_uIoo
  intro t ht
  have ht' : t ∈ Ioo 0 b := by simpa only [uIoo_of_le hb] using ht
  simp only [zeroSlopeExtension, Function.update_of_ne ht'.1.ne', slope, h0,
    sub_zero, vsub_eq_sub]

omit [CompleteSpace E] in
theorem continuousOn_zero_dslope {f : ℝ → E} {b : ℝ}
    (hf : ContinuousOn f (Icc 0 b)) (hd : DifferentiableAt ℝ f 0) :
    ContinuousOn (dslope f 0) (Icc 0 b) := by
  intro t ht
  by_cases h : t = 0
  · subst t
    exact (continuousAt_dslope_same.mpr hd).continuousWithinAt
  · exact (continuousWithinAt_dslope_of_ne h).mpr (hf t ht)

omit [CompleteSpace E] in
/-- The singular-looking quotient has a continuous extension at zero. -/
theorem intervalIntegrable_inv_smul_of_zero {f : ℝ → E} {b : ℝ} (hb : 0 ≤ b)
    (hf : ContinuousOn f (Icc 0 b)) (hd : DifferentiableAt ℝ f 0) (h0 : f 0 = 0) :
    IntervalIntegrable (fun t => t⁻¹ • f t) volume 0 b := by
  have hc := continuousOn_zero_dslope hf hd
  have hi : IntervalIntegrable (dslope f 0) volume 0 b := (show ContinuousOn (dslope f 0) (uIcc 0 b) by
    simpa only [uIcc_of_le hb] using hc).intervalIntegrable
  apply hi.congr_uIoo
  intro t ht
  have ht' : t ∈ Ioo 0 b := by simpa only [uIoo_of_le hb] using ht
  simp only [dslope_of_ne f ht'.1.ne', slope, h0, sub_zero, vsub_eq_sub]

/-- Actual logarithmic integration by parts, with integrability and the zero
boundary term proved from C¹ regularity of the derivative curve. -/
theorem integral_inv_smul_eq_log_smul_deriv {f f' : ℝ → E} {b : ℝ} (hb : 0 < b)
    (hf : ContinuousOn f (Icc 0 b)) (hf' : ContinuousOn f' (Icc 0 b))
    (hderiv : ∀ t ∈ Icc 0 b, HasDerivWithinAt f (f' t) (Icc 0 b) t) (h0 : f 0 = 0) :
    (∫ t in 0..b, t⁻¹ • f t) = ∫ t in 0..b, Real.log (b / t) • f' t := by
  let w : ℝ → ℝ := fun t => Real.log b - Real.log t
  let F : ℝ → E := fun t => w t • f t
  have hd0 := hderiv 0 ⟨le_rfl, hb.le⟩
  have hds := continuousOn_zeroSlopeExtension hf hd0
  have hF : ContinuousOn F (Icc 0 b) := by
    have hw : Continuous (fun t : ℝ => t * Real.log b - t * Real.log t) :=
      (continuous_id.mul continuous_const).sub Real.continuous_mul_log
    have hh := hw.continuousOn.smul hds
    convert hh using 1
    ext t
    dsimp [F, w]
    rw [← mul_sub, mul_smul]
    rw [smul_comm]
    congr 1
    simpa only [h0, sub_zero] using (smul_zeroSlopeExtension (f := f) (f' 0) t).symm
  have hi := intervalIntegrable_inv_smul_of_zero_within hb.le hf hd0 h0
  have hw : IntervalIntegrable w volume 0 b :=
    intervalIntegrable_const.sub intervalIntegral.intervalIntegrable_log'
  have hwi : IntervalIntegrable (fun t => w t • f' t) volume 0 b :=
    hw.smul_continuousOn (by simpa only [uIcc_of_le hb.le] using hf')
  have hD (t : ℝ) (ht : t ∈ Ioo 0 b) :
      HasDerivAt F (-(t⁻¹ • f t) + w t • f' t) t := by
    have hl : HasDerivAt w (-t⁻¹) t := by
      simpa only [w, Pi.sub_def, zero_sub] using (hasDerivAt_const t (Real.log b)).sub
        (Real.hasDerivAt_log ht.1.ne')
    simpa only [F, Pi.smul_def, neg_smul, add_comm] using hl.fun_smul ((hderiv t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb.le hF hD (hi.neg.add hwi)
  have hni : IntervalIntegrable (fun t => -(t⁻¹ • f t)) volume 0 b := hi.neg
  rw [intervalIntegral.integral_add hni hwi, intervalIntegral.integral_neg] at he
  have hFb : F b = 0 := by simp [F, w]
  have hF0 : F 0 = 0 := by simp [F, h0]
  rw [hFb, hF0, sub_self] at he
  have hid : (∫ t in 0..b, t⁻¹ • f t) = ∫ t in 0..b, w t • f' t := by
    exact neg_add_eq_zero.mp he
  rw [hid]
  apply intervalIntegral.integral_congr_uIoo
  intro t ht
  have ht' : t ∈ Ioo 0 b := by simpa only [uIoo_of_le hb.le] using ht
  change w t • f' t = Real.log (b / t) • f' t
  rw [Real.log_div hb.ne' ht'.1.ne']

end AcceleratedLogConcave.Conditional.Stein
