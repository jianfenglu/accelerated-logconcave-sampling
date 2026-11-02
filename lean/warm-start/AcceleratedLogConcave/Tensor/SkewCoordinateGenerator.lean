import AcceleratedLogConcave.Tensor.AdjointReduction

/-! Literal skew-adjoint generator cancellation. No stationary moments or
source-jet identification are assumed by these differential identities. -/
noncomputable section
open scoped ContDiff
namespace AcceleratedLogConcave.Tensor.SkewCoordinateGenerator
open AdjointReduction
variable {I E : Type*} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem sum_skew_mul_symmetric (B A : I → I → ℝ)
    (hB : ∀ i j, B i j = - B j i) (hA : ∀ i j, A i j = A j i) :
    (∑ i, ∑ j, B i j * A i j) = 0 := by
  have he : (∑ i, ∑ j, B i j*A i j) = -(∑ i, ∑ j, B i j*A i j) := by
    calc
      _ = ∑ j, ∑ i, B i j*A i j := Finset.sum_comm
      _ = ∑ i, ∑ j, -(B i j*A i j) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hB j i,hA j i]
        ring
      _ = _ := by simp
  linarith

def column (d : I → E) (B : I → I → E → ℝ) (H : E → ℝ) (x : E) (j : I) : ℝ :=
  ∑ i, (-dir (d i) (B i j) x + dir (d i) H x * B i j x)

def velocity (d : I → E) (B : I → I → E → ℝ) (H : E → ℝ) (x : E) : E :=
  ∑ j, column d B H x j • d j

/-- Coordinate form of δ_i(B_ij ∂_j f). -/
def generator (d : I → E) (B : I → I → E → ℝ) (H f : E → ℝ) (x : E) : ℝ :=
  ∑ i, ∑ j, (-dir (d i) (fun y => B i j y * dir (d j) f y) x +
    dir (d i) H x * (B i j x * dir (d j) f x))

theorem generator_eq_column (d : I → E) (B : I → I → E → ℝ) (H f : E → ℝ)
    (hB : ∀ i j, Differentiable ℝ (B i j))
    (hskew : ∀ x i j, B i j x = -B j i x) (hf : ContDiff ℝ ∞ f) (x : E) :
    generator d B H f x = ∑ j, column d B H x j * dir (d j) f x := by
  have he (i j : I) :
      -dir (d i) (fun y => B i j y * dir (d j) f y) x +
        dir (d i) H x * (B i j x * dir (d j) f x) =
      (-dir (d i) (B i j) x + dir (d i) H x * B i j x)*dir (d j) f x -
        B i j x * dir (d i) (dir (d j) f) x := by
    rw [dir_mul (d i) (hB i j) ((contDiff_dir hf (d j)).differentiable (by simp))]
    ring
  have hz := sum_skew_mul_symmetric (fun i j => B i j x)
    (fun i j => dir (d i) (dir (d j) f) x) (hskew x)
    (fun i j => congrFun (dir_comm hf (d i) (d j)) x)
  unfold generator
  simp_rw [he,Finset.sum_sub_distrib]
  rw [hz,sub_zero,Finset.sum_comm]
  simp only [column,Finset.sum_mul]

theorem generator_eq_fderiv (d : I → E) (B : I → I → E → ℝ) (H f : E → ℝ)
    (hB : ∀ i j, Differentiable ℝ (B i j))
    (hskew : ∀ x i j, B i j x = -B j i x) (hf : ContDiff ℝ ∞ f) (x : E) :
    generator d B H f x = fderiv ℝ f x (velocity d B H x) := by
  rw [generator_eq_column d B H f hB hskew hf]
  simp [velocity,dir,map_sum,map_smul,smul_eq_mul]

theorem hasDerivAt_along_generator (d : I → E) (B : I → I → E → ℝ) (H f : E → ℝ)
    (hB : ∀ i j, Differentiable ℝ (B i j))
    (hskew : ∀ x i j, B i j x = -B j i x) (hf : ContDiff ℝ ∞ f)
    {Z : ℝ → E} {α t : ℝ} (hZ : HasDerivAt Z (α • velocity d B H (Z t)) t) :
    HasDerivAt (fun u => f (Z u)) (α * generator d B H f (Z t)) t := by
  have h := ((hf.differentiable (by simp) (Z t)).hasFDerivAt.comp_hasDerivAt t hZ)
  rw [generator_eq_fderiv d B H f hB hskew hf]
  simpa only [map_smul,smul_eq_mul,Function.comp_def] using h

end AcceleratedLogConcave.Tensor.SkewCoordinateGenerator
