import AcceleratedLogConcave.Analysis.AnglePhaseScale
import AcceleratedLogConcave.Numerics.AffineGraph

noncomputable section
namespace AcceleratedLogConcave.Analysis.AnglePhase
open Numerics.AffineGraph
variable {m : ℕ}

theorem original_rotation_scale_bounds (G : MeanGeometry m) (k : G.Kernel) :
    0 < G.rotationScale k ∧ G.rotationScale k ≤ 1 ∧ G.R ≤ 2*G.rotationScale k := by
  have hq := G.rotationScale_pos k
  have hr := G.rho_mem k
  have hr1 := hr.2.trans G.backwardEnd_lt_one
  have hsqrt : (backwardEnd G.R)^2 = 1-G.R^2 := by
    apply Real.sq_sqrt
    nlinarith [G.R_pos,G.R_le_half]
  have hv : G.R^2 ≤ 1-(G.rho k)^2 := by
    nlinarith [G.backwardEnd_pos]
  have hden : 0 < 1+(G.rho k)^2 := by positivity
  have hsq := (eq_div_iff (ne_of_gt hden)).mp (G.rotationScale_sq k)
  change (G.rotationScale k)^2 * (1+(G.rho k)^2) = 1-(G.rho k)^2 at hsq
  have hq1 : (G.rotationScale k)^2 ≤ 1 := by
    rw [G.rotationScale_sq]
    apply (div_le_one hden).mpr
    unfold MeanGeometry.variance
    nlinarith [sq_nonneg (G.rho k)]
  have hlow : G.R^2 ≤ 2*(G.rotationScale k)^2 := by
    nlinarith [mul_nonneg (sq_nonneg (G.rotationScale k))
      (show 0 ≤ 1-(G.rho k)^2 by nlinarith)]
  exact ⟨hq,by nlinarith,by nlinarith [G.R_pos]⟩

theorem original_normalized_speed_le (G : MeanGeometry m) (k : G.Kernel) :
    (G.rotationScale k)⁻¹ / (radius G.R (G.rotationScale k))^2 ≤ 2/G.R^2 := by
  obtain ⟨hq,hq1,hhalf⟩ := original_rotation_scale_bounds G k
  exact normalized_speed_le G.R_pos (by linarith [G.R_le_half]) hq hq1 hhalf
end AcceleratedLogConcave.Analysis.AnglePhase
