import AcceleratedLogConcave.Numerics.SmoothQuantitativeGuarantees
import AcceleratedLogConcave.Numerics.ProbabilityMeshBudget

/-! Concrete payments for the source smooth receiver. In particular, the
centering defect is computed from its original-data source budget, rather than
assumed as a final-error hypothesis. All seven receiver components remain the
ones in `SmoothQuantitativeAssembly.budget`. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
set_option autoImplicit false
namespace AcceleratedLogConcave.Numerics.SmoothQuadraturePayments
open MeanFlowLp MeanResidualBridge MeanCollocationLp AffineGraph AffineGraph.MeanGeometry
open SmoothQuantitativeAssembly Tensor.AdjointReduction CenterMeanSecondJetSource
variable {D m : ℕ}

private theorem negative_four_power (R : ℝ) (hR : 0 < R) (n : ℕ) :
    R ^ (-4 * (n : ℝ)) = (1 / (R ^ 2) ^ n) ^ 2 := by
  rw [one_div, inv_pow, ← pow_mul, ← pow_mul, ← Real.rpow_natCast,
    ← Real.rpow_neg hR.le]
  congr 1
  push_cast
  ring

/-- Exact physical scaling of the original-data center budget, including zero
curvature and zero dimension. No division by the curvature is used. -/
theorem centerSourceBudget_eq (d : Data (Fin D) m) (L c R : ℝ)
    (hL : 0 ≤ L) (hc : 0 ≤ c) (hR : 0 < R) (k : ℕ) :
    centerSourceBudget d L L c R k =
      Real.sqrt (2 * (D : ℝ) * PhaseBudget.Q c (5 * (k + 1) + 1)) *
        L * (L / (d.sigma / 2) / R ^ 2) ^ (k + 1) := by
  have hq := PhaseBudget.Q_nonneg hc (5 * (k + 1) + 1)
  have he := sourceJetEnergyScale_nonneg L L (d.sigma / 2) hc hR.le k
  have hleft : (centerSourceBudget d L L c R k)^2 =
      (D : ℝ) * sourceJetEnergyScale L L (d.sigma / 2) c R k := by
    unfold centerSourceBudget
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg D), Real.sq_sqrt he]
  have hpower : R ^ (-4 * ((k : ℝ) + 1)) = (1 / (R^2)^(k+1))^2 := by
    simpa only [Nat.cast_add, Nat.cast_one] using negative_four_power R hR (k+1)
  have hright : (Real.sqrt (2 * (D : ℝ) * PhaseBudget.Q c (5 * (k+1)+1)) *
      L * (L / (d.sigma/2) / R^2)^(k+1))^2 =
      (D : ℝ) * sourceJetEnergyScale L L (d.sigma/2) c R k := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    unfold sourceJetEnergyScale
    rw [hpower, div_pow, div_pow]
    ring
  have hl := centerSourceBudget_nonneg d L L c R k
  have hr : 0 ≤ Real.sqrt (2 * (D : ℝ) * PhaseBudget.Q c (5 * (k+1)+1)) *
      L * (L / (d.sigma/2) / R^2)^(k+1) := by
    have hs := d.hsigma.le
    positivity
  nlinarith

/-- The true centering speed in the physical time variable. -/
def centerSpeed (d : Data (Fin D) m) : ℝ :=
  (d.r * d.ell / (d.sigma / 2)) / d.G.R ^ 2

def centerCoefficient (d : Data (Fin D) m) : ℝ :=
  Real.sqrt (2 * (D : ℝ) * PhaseBudget.Q auxiliaryConstant (5*m+1)) * (d.r*d.ell)

theorem budget_center_eq (d : Data (Fin D) m) (hm : 1 ≤ m) :
    (budget d).center = centerCoefficient d * centerSpeed d ^ m := by
  have hx := centerSourceBudget_eq d (d.r*d.ell) auxiliaryConstant d.G.R
    (mul_nonneg d.hr.le d.hell) (by norm_num [auxiliaryConstant]) d.G.R_pos (m-1)
  simpa only [Nat.sub_add_cancel hm, budget, kernelData, centerCoefficient, centerSpeed] using hx

theorem centerSpeed_nonneg (d : Data (Fin D) m) : 0 ≤ centerSpeed d := by
  unfold centerSpeed
  have hr := d.hr.le
  have he := d.hell
  have hs := d.hsigma.le
  positivity

theorem centerCoefficient_nonneg (d : Data (Fin D) m) : 0 ≤ centerCoefficient d :=
  mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg d.hr.le d.hell)

/-- A derived centering payment for the explicit budget, not an assumed output
error. Its small-speed premise is discharged from the scalar source schedule. -/
theorem centering_defect_le (d : Data (Fin D) m) (hm : 1 ≤ m)
    {δ : ℝ} (hδ : 0 < δ) (hspeed : centerSpeed d ≤ δ ^ ((1:ℝ)/3)) :
    2 * (budget d).center / (m.factorial : ℝ) ≤
      (2 * centerCoefficient d / (m.factorial : ℝ)) * δ ^ ((m : ℝ)/3) := by
  have hp := pow_le_pow_left₀ (centerSpeed_nonneg d) hspeed m
  have hexp : (δ ^ ((1:ℝ)/3))^m = δ ^ ((m:ℝ)/3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    congr 1
    ring
  rw [hexp] at hp
  rw [budget_center_eq d hm]
  calc
    _ = (2 * centerCoefficient d / (m.factorial : ℝ)) * centerSpeed d ^ m := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity [centerCoefficient_nonneg d])

/-- The numerical size and resolution inequalities imply the centering speed
bound. The source factor two from s=sigma/2 is retained. -/
theorem centerSpeed_le_of_resolution (d : Data (Fin D) m) (hm : 2 ≤ m)
    {δ b t w S : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hw : 0 ≤ w) (hwt : w ≤ t) (ht : t ≤ (1:ℝ)/60)
    (hb : (1:ℝ)/2 ≤ b) (hS : 1 ≤ S)
    (hR : d.G.R = δ ^ t) (hsize : d.ell*d.r/d.sigma ≤ S*δ^b)
    (hres : δ ≤ (520*(m:ℝ)^5*S)^(-12:ℝ)) :
    centerSpeed d ≤ δ ^ ((1:ℝ)/3) := by
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hm5 : (1:ℝ) ≤ (m:ℝ)^5 := one_le_pow₀ hm1
  have hS0 : 0 < S := by linarith
  have ht0 : 0 ≤ t := hw.trans hwt
  have hpow : δ ^ (b-2*t) ≤ δ ^ (b-4*t-w) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hden : (δ ^ t)^2 = δ ^ (2*t) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    congr 1
    norm_num
    ring
  have hs : centerSpeed d ≤ 2*S*δ^(b-2*t) := by
    unfold centerSpeed
    rw [hR]
    have hsigma : d.sigma ≠ 0 := ne_of_gt d.hsigma
    have heq : d.r*d.ell/(d.sigma/2) = 2*(d.ell*d.r/d.sigma) := by
      field_simp
    rw [heq, hden]
    calc
      _ ≤ (2*(S*δ^b))/δ^(2*t) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsize (by norm_num))
          (Real.rpow_nonneg hδ.le _)
      _ = _ := by rw [Real.rpow_sub hδ]; ring
  exact hs.trans ((mul_le_mul
    (show 2*S ≤ 520*(m:ℝ)^5*S by nlinarith)
    hpow (Real.rpow_nonneg hδ.le _) (by positivity)).trans
    (affine_resolution_envelope_le hδ hδ1 (by positivity) hb hwt ht hres))

/-- The full final mean centering defect from original data alone. This uses
only the proved center fields, not either unpaid velocity/angle interface. -/
theorem reference_output_bound (d : Data (Fin D) m) (hm : 2 ≤ m) :
    ‖d.G.meanOutput d.sigma (initialScore d)
      ((lpGraph d).collect (operator d) (reference d)) - terminalTarget d‖ ≤
        2*(budget d).center/(m.factorial:ℝ) := by
  have hc := centerMeanLp_center_fields_original_data d (by omega)
    (c := auxiliaryConstant) (by norm_num [auxiliaryConstant])
  have hs : ∀ t ∈ Icc (0:ℝ) 1,
      ContDiffAt ℝ m ((curvesWithSmoothBranches d).centerMean d.G (operator d) 0 d.r) t := by
    rw [center_function_eq]
    exact hc.2.1
  have hb : ∀ t ∈ Icc (0:ℝ) 1,
      ‖iteratedDeriv m ((curvesWithSmoothBranches d).centerMean d.G (operator d) 0 d.r) t‖ ≤
        (budget d).center := by
    rw [center_function_eq]
    exact hc.2.2
  have ho := AffineResidual.Mean.meanFinalResidual d.G hm d.r d.sigma d.hr d.hsigma
    (operator d) 0 (initialPosition d) (initialScore d) (initialNoise d)
    (curvesWithSmoothBranches d) (budget d).center hc.1
    (smoothBranches_canonical_equations d) hs hb
  change ‖d.G.meanOutput d.sigma (initialScore d)
    ((lpGraph d).collect (operator d)
      ((curvesWithSmoothBranches d).reference d.G 0 d.r)) -
    (operator d 0 d.r + (d.sigma/2) • scoreLp d 1)‖ ≤ _ at ho
  rw [smoothBranches_reference_eq,
    offset_eq d (operator d) (primitiveLp_spec _ _)] at ho
  exact ho

/-- Paid original-data final-row centering term at the actual scalar resolution. -/
theorem reference_output_bound_of_resolution (d : Data (Fin D) m) (hm : 2 ≤ m)
    {δ b t w S : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hw : 0 ≤ w) (hwt : w ≤ t) (ht : t ≤ (1:ℝ)/60)
    (hb : (1:ℝ)/2 ≤ b) (hS : 1 ≤ S)
    (hR : d.G.R = δ ^ t) (hsize : d.ell*d.r/d.sigma ≤ S*δ^b)
    (hres : δ ≤ (520*(m:ℝ)^5*S)^(-12:ℝ)) :
    ‖d.G.meanOutput d.sigma (initialScore d)
      ((lpGraph d).collect (operator d) (reference d)) - terminalTarget d‖ ≤
        (2*centerCoefficient d/(m.factorial:ℝ))*δ^((m:ℝ)/3) :=
  (reference_output_bound d hm).trans (centering_defect_le d (by omega) hδ
    (centerSpeed_le_of_resolution d hm hδ hδ1 hw hwt ht hb hS hR hsize hres))

end AcceleratedLogConcave.Numerics.SmoothQuadraturePayments
