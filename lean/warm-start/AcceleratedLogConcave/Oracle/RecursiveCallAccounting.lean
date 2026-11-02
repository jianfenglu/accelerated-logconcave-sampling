import AcceleratedLogConcave.Oracle.RecursiveExecutableDomain
import AcceleratedLogConcave.Oracle.SourceRecursiveRouting

/-! Scalar accounting for the four literal child parameter updates in
`RecursiveExecutable.meanCore`. Radius bounds include zero radius. Ratio
identities use Lean's total division; they do not assert positive child widths. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Numerics.AffineGraph

namespace MeanGeometry
variable {m : ℕ} (M : MeanGeometry m)

theorem normalizedRadius_le_one (i : M.MeanNode) : M.normalizedRadius i ≤ 1 := by
  have hs (s : ℝ) : Real.sqrt (1-s^2) ≤ 1 :=
    Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg s])
  rcases i with _ | b | ⟨b,j⟩ | ⟨b,ρ,j⟩ | ⟨b,ρ,z,j⟩
  · simp [normalizedRadius, radius]
  · simpa [normalizedRadius, radius] using M.R_le_half.trans (by norm_num : (1:ℝ)/2 ≤ 1)
  · simpa [normalizedRadius, radius] using hs (M.backward.location m j)
  · simpa [normalizedRadius, radius] using
      (mul_le_of_le_one_left (Real.sqrt_nonneg _) (M.matrix_sqrt_variance_le_one ρ)).trans
        (hs ((M.conditional ρ).location m j))
  · simpa [normalizedRadius, radius] using hs ((M.forward ρ).location m j)

theorem radius_nonneg (r : ℝ) (hr : 0 ≤ r) (i : M.MeanNode) : 0 ≤ M.radius r i := by
  rw [M.radius_eq_mul_normalizedRadius]
  exact mul_nonneg hr (M.normalizedRadius_pos i).le

theorem radius_le (r : ℝ) (hr : 0 ≤ r) (i : M.MeanNode) : M.radius r i ≤ r := by
  rw [M.radius_eq_mul_normalizedRadius]
  exact mul_le_of_le_one_right hr (M.normalizedRadius_le_one i)

end MeanGeometry
namespace SamplingGeometry
variable {m : ℕ} (S : SamplingGeometry m)

theorem normalizedRadius_pos (i : S.Node) : 0 < S.normalizedRadius i :=
  S.radius_pos 1 (by norm_num) i

theorem normalizedRadius_le_one (i : S.Node) : S.normalizedRadius i ≤ 1 := by
  simp only [normalizedRadius, radius, one_mul]
  exact Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg (S.mesh.location m i)])

theorem radius_nonneg (r : ℝ) (hr : 0 ≤ r) (i : S.Node) : 0 ≤ S.radius r i := by
  rw [S.radius_eq_mul_normalizedRadius]
  exact mul_nonneg hr (S.normalizedRadius_pos i).le

theorem radius_le (r : ℝ) (hr : 0 ≤ r) (i : S.Node) : S.radius r i ≤ r := by
  rw [S.radius_eq_mul_normalizedRadius]
  exact mul_le_of_le_one_right hr (S.normalizedRadius_le_one i)

end SamplingGeometry
end AcceleratedLogConcave.Numerics.AffineGraph

namespace AcceleratedLogConcave.Oracle.RecursiveCallAccounting
open Numerics.AffineGraph RecursiveMeanPublicTable
variable {m ms n ns : ℕ}

/-- The coefficient of `r / σ` in the published syntactic row bound. -/
def rowCoefficient (m : ℕ) (δ t w : ℝ) : ℝ :=
  256*(m:ℝ)^5*Real.rpow δ (-4*t-w)

theorem rowBound_eq (r σ δ t w : ℝ) :
    SourceMeanExecutable.rowBound (m := m) r σ δ t w =
      rowCoefficient m δ t w * (r/σ) + 4*r^2 := by
  unfold SourceMeanExecutable.rowBound rowCoefficient
  ring

private theorem ratio_mainWidth (n : ℕ) (r R Ds A u : ℝ)
    (hr : r ≠ 0) (hR : R ≠ 0) :
    (r*u) / mainWidth n r R Ds A =
      u * (4*Real.sqrt 5*Ds*Real.sqrt n/R)*A := by
  simp only [mainWidth, centerNoise, CovarianceSetup.sigma, div_eq_mul_inv,
    mul_inv_rev, inv_inv]
  field_simp
  ring

/-- Literal main mean child ratio. The zero-radius branch has row bound zero;
no positivity of `Ds`, inventory size, parent width or delta is inferred. -/
theorem mean_main_ratio_eq (M : MeanGeometry m) (r σ Ds δ t w : ℝ)
    (i : M.MeanNode) :
    M.radius r i / mainWidth n r M.R Ds
        (SourceMeanExecutable.rowBound (m := m) r σ δ t w) =
      M.normalizedRadius i * (4*Real.sqrt 5*Ds*Real.sqrt n/M.R) *
        SourceMeanExecutable.rowBound (m := m) r σ δ t w := by
  rw [M.radius_eq_mul_normalizedRadius]
  by_cases hr : r = 0
  · simp [hr, SourceMeanExecutable.rowBound]
  · exact ratio_mainWidth n r M.R Ds _ _ hr M.R_pos.ne'

/-- The active-final ratio amplifies by `4 / sqrt 3`, even as radius shrinks.
The identity remains valid when the parent width is zero. -/
theorem mean_final_ratio_eq (M : MeanGeometry m) (r σ : ℝ) :
    (r*M.R) / finalWidth M.R σ = (4/Real.sqrt 3)*(r/σ) := by
  rw [SourceRecursiveRouting.finalWidth_eq]
  simp only [div_eq_mul_inv, mul_inv_rev]
  have hR := M.R_pos.ne'
  field_simp

/-- Literal main sampling child ratio; its row bound is exactly `r^2`. -/
theorem sampling_main_ratio_eq (S : SamplingGeometry ms) (r Ds : ℝ) (i : S.Node) :
    S.radius r i / mainWidth ns r S.R Ds (r^2) =
      S.normalizedRadius i * (4*Real.sqrt 5*Ds*Real.sqrt ns/S.R)*r^2 := by
  rw [S.radius_eq_mul_normalizedRadius]
  by_cases hr : r = 0
  · simp [hr]
  · exact ratio_mainWidth ns r S.R Ds _ _ hr S.R_pos.ne'

/-- Literal final sampling child ratio, including total division at `r = 0`. -/
theorem sampling_final_ratio_eq (S : SamplingGeometry ms) (r : ℝ) (i : S.Node) :
    S.radius r i / SourceExecutableTables.samplingFinalWidth S r =
      S.normalizedRadius i * (2*Real.sqrt 2/S.τ)*r^2 := by
  rw [S.radius_eq_mul_normalizedRadius]
  unfold SourceExecutableTables.samplingFinalWidth
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

theorem mean_final_radius_mem (M : MeanGeometry m) (r : ℝ) (hr : 0 ≤ r) :
    0 ≤ r*M.R ∧ r*M.R ≤ r :=
  ⟨mul_nonneg hr M.R_pos.le,
    mul_le_of_le_one_right hr (M.R_le_half.trans (by norm_num))⟩

/-- All actual child radii stay in the parent's nonnegative interval. This is
one-step scalar accounting, not a reachable-call or schedule theorem. -/
theorem child_radii_mem (M : MeanGeometry m) (S : SamplingGeometry ms)
    (r : ℝ) (hr : 0 ≤ r) :
    (∀ i, 0 ≤ M.radius r i ∧ M.radius r i ≤ r) ∧
    (0 ≤ r*M.R ∧ r*M.R ≤ r) ∧
    (∀ i, 0 ≤ S.radius r i ∧ S.radius r i ≤ r) :=
  ⟨fun i => ⟨M.radius_nonneg r hr i, M.radius_le r hr i⟩,
    mean_final_radius_mem M r hr,
    fun i => ⟨S.radius_nonneg r hr i, S.radius_le r hr i⟩⟩

end AcceleratedLogConcave.Oracle.RecursiveCallAccounting
