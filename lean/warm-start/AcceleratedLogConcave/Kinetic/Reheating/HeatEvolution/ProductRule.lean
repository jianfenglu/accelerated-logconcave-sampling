import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.ReferenceHeat

/-! The exact product rule for the actual Hessian trace used by the heat quotient. -/
noncomputable section
open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
open AcceleratedLogConcave.HeatCalculus
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem hessian_mul_diagonal {p q : E → ℝ} (hp : ContDiff ℝ 2 p)
    (hq : ContDiff ℝ 2 q) (x v : E) :
    fderiv ℝ (fderiv ℝ (fun y => p y * q y)) x v v =
      p x * fderiv ℝ (fderiv ℝ q) x v v +
      q x * fderiv ℝ (fderiv ℝ p) x v v +
      2 * fderiv ℝ p x v * fderiv ℝ q x v := by
  have he : fderiv ℝ (fun y => p y * q y) =
      fun y => p y • fderiv ℝ q y + q y • fderiv ℝ p y := by
    funext y
    exact fderiv_fun_mul (hp.differentiable (by norm_num) y)
      (hq.differentiable (by norm_num) y)
  have hpd := compactTest_hasFDerivAt hp x
  have hqd := compactTest_hasFDerivAt hq x
  have hpdd := compactTest_hasFDerivAt_fderiv hp x
  have hqdd := compactTest_hasFDerivAt_fderiv hq x
  rw [he]
  change fderiv ℝ (p • fderiv ℝ q + q • fderiv ℝ p) x v v = _
  rw [((hpd.smul hqdd).add (hqd.smul hpdd)).fderiv]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul]
  ring

theorem compactTestLaplacian_mul {p q : E → ℝ} (hp : ContDiff ℝ 2 p)
    (hq : ContDiff ℝ 2 q) (x : E) :
    compactTestLaplacian (fun y => p y * q y) x =
      p x * compactTestLaplacian q x + q x * compactTestLaplacian p x +
      2 * inner ℝ (gradient p x) (gradient q x) := by
  unfold compactTestLaplacian
  simp_rw [hessian_mul_diagonal hp hq]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  congr 1
  have h := (EuclideanSpace.basisFun ι ℝ).sum_inner_mul_inner (gradient p x) (gradient q x)
  simp only [inner_gradient_right, conj_trivial] at h
  simp only [inner_gradient_left] at h
  rw [inner_gradient_right, conj_trivial]
  rw [← h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end AcceleratedLogConcave.Kinetic.Reheating
