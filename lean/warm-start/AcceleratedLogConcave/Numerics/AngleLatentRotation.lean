import AcceleratedLogConcave.Numerics.AngleRotationJets
import AcceleratedLogConcave.Numerics.RotatedMarginalLaw

/-! The all-order angle input envelope loses the latent mean exactly.
Together with lintegral_actual_observation, these are polynomial Gaussian
moment suppliers, not additional assumptions on the potential. -/
noncomputable section
open Set
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace AcceleratedLogConcave.Numerics.MeanFlowLp
open Analysis.AngleRotation Conditional AffineGraph AffineGraph.MeanGeometry
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

omit [DecidableEq ι] in
/-- Exact cancellation of the latent variable in the rotating displacement. -/
theorem observation_displacement_latent (d : Data ι m) (k : d.G.Kernel)
    (u n₁ n₂ : E) :
    (d.G.rho k • u + Real.sqrt (d.G.variance k) • n₁) -
      (d.G.rho k/(1+(d.G.rho k)^2)) •
        ((u+Real.sqrt (d.G.variance k) • n₂)+
          d.G.rho k • (d.G.rho k • u+Real.sqrt (d.G.variance k) • n₁)) =
    (Real.sqrt (d.G.variance k)/(1+(d.G.rho k)^2)) •
      (n₁-d.G.rho k • n₂) := by
  have hden : 1+(d.G.rho k)^2 ≠ 0 := ne_of_gt (by positivity)
  simp only [smul_add, smul_sub, smul_smul]
  match_scalars <;> field_simp [hden] <;> ring

omit [DecidableEq ι] in
/-- Every positive angle derivative has a Gaussian-only pointwise envelope.
No norm or moment of the latent base-law variable u appears on the right. -/
theorem norm_iteratedDeriv_rotationOfObservation_latent_le
    (d : Data ι m) (k : d.G.Kernel) (u n₁ n₂ s : E) (n : ℕ) (z : ℝ) :
    ‖iteratedDeriv (n+1) (fun t => rotationOfObservation d k t
      (d.G.rho k • u+Real.sqrt (d.G.variance k) • n₁)
      (u+Real.sqrt (d.G.variance k) • n₂) s) z‖ ≤
    ((d.G.rotationScale k)⁻¹)^(n+1) *
      ((Real.sqrt (d.G.variance k)/(1+(d.G.rho k)^2)) *
          (‖n₁‖+|d.G.rho k| *‖n₂‖)+d.G.rotationScale k*‖s‖) := by
  let B := d.G.rho k • u+Real.sqrt (d.G.variance k) • n₁
  let H := u+Real.sqrt (d.G.variance k) • n₂
  let mid := (d.G.rho k/(1+(d.G.rho k)^2)) • (H+d.G.rho k • B)
  have he : (fun t => rotationOfObservation d k t B H s) =
      fun t => mid+harmonic (d.G.rotationScale k) (B-mid) (d.G.rotationScale k • s) t := by
    funext t
    simp only [rotationOfObservation, harmonic, mid, smul_smul, mul_comm, add_assoc]
  change ‖iteratedDeriv (n+1) (fun t => rotationOfObservation d k t B H s) z‖ ≤ _
  rw [he]
  have hj := norm_iteratedDeriv_shift_harmonic_succ_le (d.G.rotationScale_pos k).le
    mid (B-mid) (d.G.rotationScale k • s) n z
  have hcancel : B-mid =
      (Real.sqrt (d.G.variance k)/(1+(d.G.rho k)^2)) •
        (n₁-d.G.rho k • n₂) := observation_displacement_latent d k u n₁ n₂
  have hcoef : 0 ≤ Real.sqrt (d.G.variance k)/(1+(d.G.rho k)^2) := by positivity
  have hdisp : ‖B-mid‖ ≤ (Real.sqrt (d.G.variance k)/(1+(d.G.rho k)^2)) *
      (‖n₁‖+|d.G.rho k| *‖n₂‖) := by
    rw [hcancel, norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoef]
    apply mul_le_mul_of_nonneg_left _ hcoef
    simpa only [norm_smul,Real.norm_eq_abs] using norm_sub_le n₁ (d.G.rho k • n₂)
  apply hj.trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (inv_nonneg.mpr (d.G.rotationScale_pos k).le) _)
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos (d.G.rotationScale_pos k), add_comm] using
    add_le_add_right hdisp ‖d.G.rotationScale k • s‖
end AcceleratedLogConcave.Numerics.MeanFlowLp
