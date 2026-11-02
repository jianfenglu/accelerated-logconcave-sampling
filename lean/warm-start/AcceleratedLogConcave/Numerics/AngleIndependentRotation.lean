import AcceleratedLogConcave.Numerics.AngleLatentRotation
import AcceleratedLogConcave.Kinetic.MomentumSplit

/-! The two Gaussian noises split into an independent midpoint noise and
normalized residual. This retains Gaussian contractions instead of replacing
them by dimension-losing pointwise powers of Gaussian norms. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace AcceleratedLogConcave.Numerics.MeanFlowLp
open Conditional AffineGraph AffineGraph.MeanGeometry
variable {ι : Type*} [Fintype ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

theorem rotationScale_mul_sqrt (d : Data ι m) (k : d.G.Kernel) :
    d.G.rotationScale k * Real.sqrt (1+(d.G.rho k)^2) = Real.sqrt (d.G.variance k) := by
  have hden : 0 < 1+(d.G.rho k)^2 := by positivity
  have hs := Real.sq_sqrt hden.le
  have hv := Real.sq_sqrt (d.G.variance_pos k).le
  have hq := d.G.rotationScale_pos k
  have hp : (d.G.rotationScale k)^2*(1+(d.G.rho k)^2)=d.G.variance k :=
    ((div_eq_iff hden.ne').mp (d.G.rotationScale_sq k).symm).symm
  have hmul : 0 ≤ d.G.rotationScale k * Real.sqrt (1+(d.G.rho k)^2) :=
    mul_nonneg hq.le (Real.sqrt_nonneg _)
  have he : (d.G.rotationScale k * Real.sqrt (1+(d.G.rho k)^2))^2 =
      (Real.sqrt (d.G.variance k))^2 := by rw [mul_pow,hs,hp,hv]
  nlinarith [Real.sqrt_nonneg (d.G.variance k)]

/-- Residual a and complementary midpoint noise c are independent standard Gaussians. -/
theorem normalized_residual_split_preserving (d : Data ι m) (k : d.G.Kernel) :
    MeasurePreserving
      (fun p : E × E =>
        ((Real.sqrt (1+(d.G.rho k)^2))⁻¹ • p.1+
          (-(d.G.rho k)/Real.sqrt (1+(d.G.rho k)^2)) • p.2,
        (d.G.rho k/Real.sqrt (1+(d.G.rho k)^2)) • p.1+
          (Real.sqrt (1+(d.G.rho k)^2))⁻¹ • p.2))
      ((stdGaussian E).prod (stdGaussian E)) ((stdGaussian E).prod (stdGaussian E)) := by
  have hden : 0 < 1+(d.G.rho k)^2 := by positivity
  have hs := Real.sq_sqrt hden.le
  have hn := (Real.sqrt_pos.mpr hden).ne'
  have hrow : ((Real.sqrt (1+(d.G.rho k)^2))⁻¹)^2+
      (-(d.G.rho k)/Real.sqrt (1+(d.G.rho k)^2))^2=1 := by
    field_simp [hn]
    nlinarith
  convert (Kinetic.gaussianRotate_measurePreserving («E» := E)
    ((Real.sqrt (1+(d.G.rho k)^2))⁻¹)
    (-(d.G.rho k)/Real.sqrt (1+(d.G.rho k)^2)) hrow) using 1
  funext p
  simp only [Kinetic.gaussianRotate, neg_div, neg_neg]

/-- Inverse split, allowing replacement of the actual two-noise integral by
independent residual/midpoint noises without losing their joint law. -/
theorem normalized_reconstruction_preserving (d : Data ι m) (k : d.G.Kernel) :
    MeasurePreserving
      (fun p : E × E =>
        ((Real.sqrt (1+(d.G.rho k)^2))⁻¹ • (p.1+d.G.rho k • p.2),
          (Real.sqrt (1+(d.G.rho k)^2))⁻¹ • (-d.G.rho k • p.1+p.2)))
      ((stdGaussian E).prod (stdGaussian E)) ((stdGaussian E).prod (stdGaussian E)) := by
  have hden : 0 < 1+(d.G.rho k)^2 := by positivity
  have hs := Real.sq_sqrt hden.le
  have hn := (Real.sqrt_pos.mpr hden).ne'
  have hrow : ((Real.sqrt (1+(d.G.rho k)^2))⁻¹)^2+
      (d.G.rho k/Real.sqrt (1+(d.G.rho k)^2))^2=1 := by
    field_simp [hn]
    nlinarith
  convert (Kinetic.gaussianRotate_measurePreserving («E» := E)
    ((Real.sqrt (1+(d.G.rho k)^2))⁻¹)
    (d.G.rho k/Real.sqrt (1+(d.G.rho k)^2)) hrow) using 1
  funext p
  apply Prod.ext <;> simp only [Kinetic.gaussianRotate,smul_add,smul_smul]
  · congr 1
    ring
  · congr 1
    ring

/-- In independent Gaussian coordinates a,c, the fixed midpoint is rho*u+rho*q*c.
Only the pair a,s rotates; neither u nor c moves with angle. -/
theorem rotationOfObservation_independent_coordinates (d : Data ι m) (k : d.G.Kernel)
    (u a c s : E) (z : ℝ) :
    rotationOfObservation d k z
      (d.G.rho k • u+Real.sqrt (d.G.variance k) •
        ((Real.sqrt (1+(d.G.rho k)^2))⁻¹ • (a+d.G.rho k • c)))
      (u+Real.sqrt (d.G.variance k) •
        ((Real.sqrt (1+(d.G.rho k)^2))⁻¹ • (-d.G.rho k • a+c))) s =
      (d.G.rho k • u+(d.G.rho k*d.G.rotationScale k) • c)+
        d.G.rotationScale k •
          (Real.cos (z/d.G.rotationScale k) • a+Real.sin (z/d.G.rotationScale k) • s) := by
  have hden : 0 < 1+(d.G.rho k)^2 := by positivity
  have hs := Real.sq_sqrt hden.le
  have hn := (Real.sqrt_pos.mpr hden).ne'
  have hq := rotationScale_mul_sqrt d k
  rw [← hq]
  unfold rotationOfObservation
  simp only [smul_add,smul_sub,smul_smul]
  match_scalars <;> field_simp [hn, hden.ne'] <;> nlinarith [hs]
end AcceleratedLogConcave.Numerics.MeanFlowLp
