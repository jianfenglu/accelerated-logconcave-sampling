import AcceleratedLogConcave.Gibbs.Normalization
import AcceleratedLogConcave.Analysis.QuadraticMinimizer

/-! Centered quadratic bounds from the original C² Hessian sandwich.
The minimizer is derived analytically. No higher derivative of the potential
and no externally supplied optimizer are required. -/
noncomputable section
open Set
open scoped ContDiff
namespace AcceleratedLogConcave.Gibbs
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem fderiv_translate {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → G} (hf : Differentiable ℝ f) (z w : E) :
    fderiv ℝ (fun u => f (z + u)) w = fderiv ℝ f (z + w) := by
  simpa [Function.comp_def] using ((hf (z + w)).hasFDerivAt.comp w
    ((hasFDerivAt_id w).const_add z)).fderiv

/-- Taylor's quadratic lower bound, based at any point. -/
theorem quadratic_lower_bound_at_of_hessian_lower {F : E → ℝ} {m : ℝ}
    (hF : ContDiff ℝ 2 F)
    (hH : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v)
    (z w : E) :
    F z + fderiv ℝ F z w + m / 2 * ‖w‖ ^ 2 ≤ F (z + w) := by
  have hd := hF.differentiable (by norm_num)
  have hdd := (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have heq : fderiv ℝ (fun u => F (z + u)) = fun u => fderiv ℝ F (z + u) :=
    funext (fderiv_translate hd z)
  have hh (u v : E) : m * ‖v‖ ^ 2 ≤
      fderiv ℝ (fderiv ℝ (fun q => F (z + q))) u v v := by
    rw [heq, fderiv_translate hdd]
    exact hH (z + u) v
  have htrans : ContDiff ℝ 2 (fun q => F (z + q)) :=
    hF.comp (contDiff_const.add contDiff_id)
  simpa only [fderiv_translate hd, add_zero] using
    quadratic_lower_bound_of_hessian_lower htrans hh w

/-- The upper Hessian bound gives the companion upper Taylor bound. -/
theorem quadratic_upper_bound_at_of_hessian_upper {F : E → ℝ} {L : ℝ}
    (hF : ContDiff ℝ 2 F)
    (hH : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ L * ‖v‖ ^ 2)
    (z w : E) :
    F (z + w) ≤ F z + fderiv ℝ F z w + L / 2 * ‖w‖ ^ 2 := by
  have heq : fderiv ℝ (fun u => -F u) = fun u => -fderiv ℝ F u := by
    funext u
    exact fderiv_fun_neg
  have hh (u v : E) : (-L) * ‖v‖ ^ 2 ≤
      fderiv ℝ (fderiv ℝ (fun q => -F q)) u v v := by
    rw [heq, fderiv_fun_neg]
    simpa only [neg_apply, neg_mul] using neg_le_neg (hH u v)
  have h := quadratic_lower_bound_at_of_hessian_lower hF.neg hh z w
  rw [heq] at h
  simp only [neg_apply] at h
  linarith

variable [FiniteDimensional ℝ E]

/-- A C² strongly convex potential has a derived actual stationary minimizer
and a centered two-sided Gaussian-scale quadratic sandwich. -/
theorem exists_minimizer_quadratic_sandwich {F : E → ℝ} {m L : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 < m)
    (hlo : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v)
    (hhi : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ L * ‖v‖ ^ 2) :
    ∃ z : E, (∀ y, F z ≤ F y) ∧ HasFDerivAt F (0 : E →L[ℝ] ℝ) z ∧
      ‖z‖ ≤ ‖fderiv ℝ F 0‖ / (m / 2) ∧
      ∀ w, m / 2 * ‖w‖ ^ 2 ≤ F (z + w) - F z ∧
        F (z + w) - F z ≤ L / 2 * ‖w‖ ^ 2 := by
  obtain ⟨z, hz, hd, hb⟩ := Analysis.QuadraticMinimizer.exists_critical_minimizer_norm_le
    hF.continuous (fderiv ℝ F 0) (by positivity : 0 < m / 2)
    (quadratic_lower_bound_of_hessian_lower hF hlo)
  have hder := (hF.differentiable (by norm_num) z).hasFDerivAt
  rw [hd] at hder
  refine ⟨z, hz, hder, hb, fun w => ?_⟩
  have hl := quadratic_lower_bound_at_of_hessian_lower hF hlo z w
  have hu := quadratic_upper_bound_at_of_hessian_upper hF hhi z w
  rw [hd, zero_apply] at hl hu
  constructor <;> linarith

end AcceleratedLogConcave.Gibbs
