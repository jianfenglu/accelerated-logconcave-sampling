import AcceleratedLogConcave.Oracle.RecursiveExecutable
import AcceleratedLogConcave.Oracle.SourceMeanShift
import AcceleratedLogConcave.Numerics.AffineBounds

/-! Concrete radius and covariance domains for the actual source recursion.
All geometric and scalar fields are proved. The sole shift-mass premise in
`*_admissible` is the actual smaller child's finite shift sum, for simultaneous
rank induction with its query-shift theorem. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.RecursiveExecutableDomain
open Numerics.AffineGraph ChildAbsorption CovarianceSetup
open RecursiveMeanPublicTable TapeLowering

/-- The mean inventory always contains its base occurrence. -/
theorem mean_inventory_pos (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode) : 0 < n := by
  have h := (nodes.symm (.base M)).isLt
  omega

theorem sampling_inventory_pos (S : SamplingGeometry m) (nodes : Fin n ≃ S.Node)
    (hm : 0 < m) : 0 < n := by
  let z : S.Node := (0, ⟨0,hm⟩)
  have h := (nodes.symm z).isLt
  omega

theorem center_noise_pos (M : MeanGeometry m) (r Ds : ℝ) (hr : 0 < r) (hDs : 0 < Ds) :
    0 < centerNoise r M.R Ds := by
  have hR := M.R_pos
  unfold centerNoise
  positivity

theorem sampling_noise_pos (S : SamplingGeometry m) (r Ds : ℝ) (hr : 0 < r) (hDs : 0 < Ds) :
    0 < SourceExecutableTables.samplingNoise S r Ds := by
  have hR := S.R_pos
  unfold SourceExecutableTables.samplingNoise centerNoise
  positivity

/-- The stronger mean radius floor also pays the common sqrt(5) noise scale. -/
theorem mean_radius_floor (M : MeanGeometry m) (r : ℝ) (hr : 0 < r) (i : M.MeanNode) :
    r*M.R/Real.sqrt 5 ≤ M.radius r i := by
  have hR := M.R_pos
  have h2 : 0 < Real.sqrt 2 := by positivity
  have h5 : 0 < Real.sqrt 5 := by positivity
  have hs : Real.sqrt 2 ≤ Real.sqrt 5 := Real.sqrt_le_sqrt (by norm_num)
  have hsmall : r*M.R/Real.sqrt 5 ≤ r*M.R/Real.sqrt 2 :=
    (div_le_div_iff₀ h5 h2).2 (mul_le_mul_of_nonneg_left hs (by positivity))
  exact hsmall.trans (M.radius_lower r hr i)

/-- Noise separation at every actual main mean child. -/
theorem mean_noise_separation (M : MeanGeometry m) (r Ds : ℝ)
    (hr : 0 < r) (hDs : 0 < Ds) (i : M.MeanNode) :
    centerNoise r M.R Ds ≤ M.radius r i/(2*Ds) :=
  (source_radius_adapter hr M.R_pos hDs (mean_radius_floor M r hr i)).2

/-- The sampling graph's actual radius floor pays the same prescribed noise. -/
theorem sampling_noise_separation (S : SamplingGeometry m) (r Ds : ℝ)
    (hr : 0 < r) (hDs : 0 < Ds) (i : S.Node) :
    SourceExecutableTables.samplingNoise S r Ds ≤ S.radius r i/(2*Ds) :=
  (source_radius_adapter hr S.R_pos hDs (S.radius_lower r hr.le i)).2

theorem final_noise_separation (M : MeanGeometry m) (r Ds : ℝ)
    (hr : 0 < r) (hDs : 0 < Ds) :
    centerNoise r M.R Ds ≤ (r*M.R)/(2*Ds) := by
  have hR := M.R_pos
  apply (source_radius_adapter hr M.R_pos hDs ?_).2
  exact div_le_self (by positivity) (Real.le_sqrt_of_sq_le (by norm_num))

/-- All five concrete child covariance-domain fields; only the actual smaller
program's shift mass remains for the simultaneous induction. -/
theorem mean_admissible (M : MeanGeometry m) (r Ds : ℝ) (hr : 0 < r) (hDs : 0 < Ds)
    (i : M.MeanNode) (v : Fin N → ℝ) (hmass : shiftSq v ≤ Ds^2) :
    Admissible (centerNoise r M.R Ds) (M.radius r i) Ds v :=
  ⟨(center_noise_pos M r Ds hr hDs).le, M.radius_pos r hr i, hDs, hmass,
    mean_noise_separation M r Ds hr hDs i⟩

theorem sampling_admissible (S : SamplingGeometry m) (r Ds : ℝ) (hr : 0 < r) (hDs : 0 < Ds)
    (i : S.Node) (v : Fin N → ℝ) (hmass : shiftSq v ≤ Ds^2) :
    Admissible (SourceExecutableTables.samplingNoise S r Ds) (S.radius r i) Ds v :=
  ⟨(sampling_noise_pos S r Ds hr hDs).le, S.radius_pos r hr i, hDs, hmass,
    sampling_noise_separation S r Ds hr hDs i⟩

theorem final_admissible (M : MeanGeometry m) (r Ds : ℝ) (hr : 0 < r) (hDs : 0 < Ds)
    (v : Fin N → ℝ) (hmass : shiftSq v ≤ Ds^2) :
    Admissible (centerNoise r M.R Ds) (r*M.R) Ds v :=
  ⟨(center_noise_pos M r Ds hr hDs).le, mul_pos hr M.R_pos, hDs, hmass,
    final_noise_separation M r Ds hr hDs⟩

/-- Source-specialized private geometry inherits its exact main/final radius
and covariance domains, with the parent's same R. -/
theorem private_admissible (M : MeanGeometry m)
    (mesh : IntervalMesh 0 (samplingEnd (M.R/backwardEnd M.R)))
    (r Ds : ℝ) (hr : 0 < r) (hDs : 0 < Ds)
    (i : mesh.Source m) (v : Fin N → ℝ) (hmass : shiftSq v ≤ Ds^2) :
    Admissible (centerNoise r M.R Ds)
      ((RecursiveExecutable.privateGeometry M mesh).radius r i) Ds v :=
  sampling_admissible (RecursiveExecutable.privateGeometry M mesh) r Ds hr hDs i v hmass

theorem mean_main_width_pos (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (r σ Ds δ t w : ℝ) (hr : 0 < r) (hσ : 0 < σ) (hDs : 0 < Ds) (hδ : 0 < δ) :
    0 < mainWidth n r M.R Ds (SourceMeanExecutable.rowBound (m := m) r σ δ t w) := by
  have hA : 0 < SourceMeanExecutable.rowBound (m := m) r σ δ t w := by
    have hp := Real.rpow_pos_of_pos hδ (-4*t-w)
    unfold SourceMeanExecutable.rowBound
    positivity
  exact CovarianceSetup.sigma_pos (mean_inventory_pos M nodes) (center_noise_pos M r Ds hr hDs) hA

theorem sampling_main_width_pos (S : SamplingGeometry m) (nodes : Fin n ≃ S.Node)
    (r Ds : ℝ) (hm : 0 < m) (hr : 0 < r) (hDs : 0 < Ds) :
    0 < mainWidth n r S.R Ds (r^2) := by
  exact CovarianceSetup.sigma_pos (sampling_inventory_pos S nodes hm)
    (sampling_noise_pos S r Ds hr hDs) (sq_pos_of_pos hr)

theorem mean_final_width_pos (M : MeanGeometry m) (σ : ℝ) (hσ : 0 < σ) :
    0 < finalWidth M.R σ := by
  have hR := M.R_pos
  unfold finalWidth finalNoise
  positivity

theorem sampling_final_width_pos (S : SamplingGeometry m) (r : ℝ) (hr : 0 < r) :
    0 < SourceExecutableTables.samplingFinalWidth S r := by
  have ht : 0 < S.τ := S.R_pos.trans_le S.R_le_τ
  unfold SourceExecutableTables.samplingFinalWidth
  positivity

/-- Sampling main/final raw shifts have the numerical source shape bound. -/
theorem sampling_shift_ratio (S : SamplingGeometry m) (r : ℝ) (hr : 0 < r) (i : S.Node) :
    |(1-S.mesh.location m i*samplingEnd S.τ)*r/S.radius r i| ≤ 3 := by
  have h := S.shift_shape_le r hr i
  rw [abs_div, abs_mul, abs_of_pos hr, abs_of_pos (S.radius_pos r hr i)]
  convert h using 1
  field_simp
  simp only [SamplingGeometry.positionCoeff, mul_comm]

/-- The ordinary sampling-position coefficient has norm at most one. -/
theorem sampling_position_abs_le_one (S : SamplingGeometry m) : |-(samplingEnd S.τ)| ≤ 1 := by
  rw [abs_neg, abs_of_pos S.samplingEnd_pos]
  exact S.samplingEnd_lt_one.le

/-- The only additional private Gaussian shift is the source reserve, bounded
by two using R≤1/2 and the exact bStar=sqrt(1-R²). -/
theorem private_reserve_abs_le_two (M : MeanGeometry m) :
    |(-2*M.R)/backwardEnd M.R| ≤ 2 := by
  have hb := M.backwardEnd_pos
  have hs : (backwardEnd M.R)^2 = 1-M.R^2 :=
    Real.sq_sqrt (by nlinarith [M.R_pos, M.R_le_half])
  have hRb : M.R ≤ backwardEnd M.R := by nlinarith [M.R_pos, M.R_le_half]
  rw [abs_div, abs_mul, abs_of_pos M.R_pos, abs_of_pos hb]
  norm_num
  exact (div_le_iff₀ hb).2 (by nlinarith)

/-- Absolute local Gaussian contribution before all recursively absorbed child
shifts: one position block plus the reserve augmentation. -/
theorem private_local_shift_mass_le_five (M : MeanGeometry m) (S : SamplingGeometry ms) :
    (-(samplingEnd S.τ))^2 + ((-2*M.R)/backwardEnd M.R)^2 ≤ 5 := by
  have hp := sampling_position_abs_le_one S
  have hr := private_reserve_abs_le_two M
  have hp2 := (sq_le_sq₀ (abs_nonneg (-(samplingEnd S.τ))) (by norm_num : (0:ℝ) ≤ 1)).2 hp
  have hr2 := (sq_le_sq₀ (abs_nonneg ((-2*M.R)/backwardEnd M.R)) (by norm_num : (0:ℝ) ≤ 2)).2 hr
  simp only [sq_abs] at hp2 hr2
  nlinarith

end AcceleratedLogConcave.Oracle.RecursiveExecutableDomain
