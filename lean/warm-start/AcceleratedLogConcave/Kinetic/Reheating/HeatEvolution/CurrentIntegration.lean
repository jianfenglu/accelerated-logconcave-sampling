import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-! Time Cauchy--Schwarz and integration of the proved core current derivative. -/
noncomputable section
open MeasureTheory Set Filter
namespace AcceleratedLogConcave.Kinetic.Reheating

theorem interval_integral_sqrt_le {a b : ℝ} (hab : a ≤ b) (D : ℝ → ℝ)
    (hD : Continuous D) (hn : ∀ t ∈ Icc a b, 0 ≤ D t) :
    (∫ t in a..b, Real.sqrt (D t)) ≤ Real.sqrt ((b-a)*(∫ t in a..b, D t)) := by
  let μ := volume.restrict (Ioc a b)
  have hs : MemLp (fun t => Real.sqrt (D t)) 2 μ := by
    apply (memLp_two_iff_integrable_sq_norm hD.sqrt.aestronglyMeasurable).mpr
    apply (hD.intervalIntegrable a b).1.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simp only [Real.norm_eq_abs,sq_abs]
    exact (Real.sq_sqrt (hn t ⟨ht.1.le,ht.2⟩)).symm
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall (fun t => Real.sqrt_nonneg (D t)))
    (Eventually.of_forall (fun _ => (zero_le_one : (0:ℝ) ≤ 1)))
    (by simpa using hs) (by simpa using (memLp_const (1:ℝ) (μ := μ) (p := 2)))
  have he : (∫ t, (Real.sqrt (D t))^(2:ℝ) ∂μ) = ∫ t, D t ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.rpow_two,Real.sq_sqrt (hn t ⟨ht.1.le,ht.2⟩)]
  simp only [mul_one,he,Real.one_rpow,integral_const,smul_eq_mul,mul_one,← Real.sqrt_eq_rpow] at hh
  have hμ : μ.real Set.univ = b-a := by simp [μ,hab]
  rw [hμ] at hh
  rw [intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_le hab]
  calc
    _ ≤ Real.sqrt (∫ t, D t ∂μ) * Real.sqrt (b-a) := hh
    _ = Real.sqrt ((b-a)*(∫ t, D t ∂μ)) := by
      rw [mul_comm,← Real.sqrt_mul (sub_nonneg.mpr hab)]

/-- Integrating the core current estimate costs only the actual norm defect;
no strong time differentiation of arbitrary L2 inputs is used. -/
theorem current_increment_le_of_dissipation {a b N defect : ℝ} (hab : a ≤ b)
    (hN : 0 ≤ N) (J D : ℝ → ℝ) (hJ : ContinuousOn J (Icc a b))
    (hD : Continuous D) (hn : ∀ t ∈ Icc a b, 0 ≤ D t)
    (henergy : (∫ t in a..b, D t) = defect)
    (hd : ∀ t ∈ Ioo a b, ∃ d : ℝ, HasDerivAt J d t ∧
      |d| ≤ N * Real.sqrt (D t) + N^2/4) :
    |J b-J a| ≤ (b-a)/4*N^2 + Real.sqrt ((b-a)*defect)*N := by
  have hb : Continuous (fun t => N * Real.sqrt (D t) + N^2/4) :=
    (hD.sqrt.const_mul N).add continuous_const
  have hdisp := norm_sub_le_integral_of_norm_deriv_le_of_le hab hJ
    (fun t ht => (hd t ht).choose_spec.1.differentiableAt.differentiableWithinAt)
    (Eventually.of_forall (fun t ht => by
      obtain ⟨d,hd,hbound⟩ := hd t ht
      rw [hd.deriv,Real.norm_eq_abs]
      exact hbound)) (hb.intervalIntegrable a b)
  rw [Real.norm_eq_abs] at hdisp
  have hroot := interval_integral_sqrt_le hab D hD hn
  rw [henergy] at hroot
  have hmul := mul_le_mul_of_nonneg_left hroot hN
  rw [intervalIntegral.integral_add ((hD.sqrt.const_mul N).intervalIntegrable a b)
      (intervalIntegrable_const), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, smul_eq_mul] at hdisp
  nlinarith

end AcceleratedLogConcave.Kinetic.Reheating
