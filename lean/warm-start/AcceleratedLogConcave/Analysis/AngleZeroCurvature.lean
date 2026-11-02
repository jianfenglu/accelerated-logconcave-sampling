import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! Zero derivative of the displacement means a constant translation, not
necessarily zero displacement. Positive angle derivatives still vanish. -/
noncomputable section
namespace AcceleratedLogConcave.Analysis.AnglePhase
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem displacement_constant_of_derivative_identity (T : E → E)
    (hT : Differentiable ℝ T) (hDT : ∀ x, fderiv ℝ T x = ContinuousLinearMap.id ℝ E)
    (x y : E) : T x-x = T y-y := by
  apply is_const_of_fderiv_eq_zero (hT.sub differentiable_id) _ x y
  intro z
  change fderiv ℝ (fun y => T y - id y) z = 0
  rw [fderiv_fun_sub (hT z) differentiableAt_id,hDT,fderiv_id]
  simp

theorem positive_angle_derivative_zero_of_derivative_identity (T : E → E)
    (hT : Differentiable ℝ T) (hDT : ∀ x, fderiv ℝ T x = ContinuousLinearMap.id ℝ E)
    (W : ℝ → E) (n : ℕ) (z : ℝ) :
    iteratedDeriv (n+1) (fun t => T (W t)-W t) z = 0 := by
  have he : (fun t => T (W t)-W t) = fun _ => T (W 0)-W 0 := by
    funext t
    exact displacement_constant_of_derivative_identity T hT hDT _ _
  rw [he,iteratedDeriv_const]
  simp
end AcceleratedLogConcave.Analysis.AnglePhase
