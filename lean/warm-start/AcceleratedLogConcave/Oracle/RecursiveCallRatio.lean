import AcceleratedLogConcave.Oracle.RecursiveCallAccounting

/-! Exact next-call row bounds and a concrete failure of inherited row-smallness.
These concern the published syntactic `rowBound`, not a lower bound on the
actual matrix norm, and assert no uniform stability or schedule invariant. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Oracle.RecursiveCallAccounting
open Numerics.AffineGraph RecursiveMeanPublicTable
variable {m ms n ns : ℕ}

theorem rowCoefficient_nonneg (δ t w : ℝ) (hδ : 0 < δ) :
    0 ≤ rowCoefficient m δ t w := by
  unfold rowCoefficient
  exact mul_nonneg (by positivity) (Real.rpow_pos_of_pos hδ _).le

theorem rowBound_nonneg (r σ δ t w : ℝ)
    (hr : 0 ≤ r) (hσ : 0 ≤ σ) (hδ : 0 < δ) :
    0 ≤ SourceMeanExecutable.rowBound (m := m) r σ δ t w := by
  rw [rowBound_eq]
  exact add_nonneg (mul_nonneg (rowCoefficient_nonneg δ t w hδ) (div_nonneg hr hσ))
    (by positivity)

/-- Exact scalar update for a main mean call, at its literal radius and width. -/
theorem mean_main_rowBound_eq (M : MeanGeometry m) (r σ Ds δ t w : ℝ)
    (i : M.MeanNode) :
    SourceMeanExecutable.rowBound (m := m) (M.radius r i)
      (mainWidth n r M.R Ds (SourceMeanExecutable.rowBound (m := m) r σ δ t w)) δ t w =
      rowCoefficient m δ t w *
        (M.normalizedRadius i * (4*Real.sqrt 5*Ds*Real.sqrt n/M.R) *
          SourceMeanExecutable.rowBound (m := m) r σ δ t w) +
        4*(M.normalizedRadius i)^2*r^2 := by
  rw [rowBound_eq, mean_main_ratio_eq, M.radius_eq_mul_normalizedRadius]
  ring

/-- Exact active-final scalar update. Its precision remains `q-t` in meanCore. -/
theorem mean_final_rowBound_eq (M : MeanGeometry m) (r σ δ t w : ℝ) :
    SourceMeanExecutable.rowBound (m := m) (r*M.R) (finalWidth M.R σ) δ t w =
      rowCoefficient m δ t w * ((4/Real.sqrt 3)*(r/σ)) + 4*M.R^2*r^2 := by
  rw [rowBound_eq, mean_final_ratio_eq]
  ring

/-- Sampling children are mean calls with the parent's mean order `m`; their
sampling geometry may have the independent order `ms`. -/
theorem sampling_main_rowBound_eq (S : SamplingGeometry ms) (r Ds δ t w : ℝ)
    (i : S.Node) :
    SourceMeanExecutable.rowBound (m := m) (S.radius r i)
      (mainWidth ns r S.R Ds (r^2)) δ t w =
      rowCoefficient m δ t w *
        (S.normalizedRadius i * (4*Real.sqrt 5*Ds*Real.sqrt ns/S.R)*r^2) +
        4*(S.normalizedRadius i)^2*r^2 := by
  rw [rowBound_eq, sampling_main_ratio_eq, S.radius_eq_mul_normalizedRadius]
  ring

theorem sampling_final_rowBound_eq (S : SamplingGeometry ms) (r δ t w : ℝ)
    (i : S.Node) :
    SourceMeanExecutable.rowBound (m := m) (S.radius r i)
      (SourceExecutableTables.samplingFinalWidth S r) δ t w =
      rowCoefficient m δ t w *
        (S.normalizedRadius i * (2*Real.sqrt 2/S.τ)*r^2) +
        4*(S.normalizedRadius i)^2*r^2 := by
  rw [rowBound_eq, sampling_final_ratio_eq, S.radius_eq_mul_normalizedRadius]
  ring

theorem mean_final_ratio_strict (M : MeanGeometry m) (r σ : ℝ)
    (hr : 0 < r) (hσ : 0 < σ) :
    r/σ < (r*M.R)/finalWidth M.R σ := by
  rw [mean_final_ratio_eq]
  have hs : 0 < Real.sqrt 3 := by positivity
  have hs4 : Real.sqrt 3 < 4 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
  have hfactor : (1:ℝ) < 4/Real.sqrt 3 := (lt_div_iff₀ hs).2 (by simpa using hs4)
  simpa using mul_lt_mul_of_pos_right hfactor (div_pos hr hσ)

/-- For every actual order-one mean geometry, the positive parent parameters
`r=1/64`, `sigma=16`, `delta=1` have row bound below 1/2, whereas the literal
active-final child exceeds 1/2. Radius shrinkage does not preserve row-smallness. -/
theorem rowBound_half_not_inherited (M : MeanGeometry 1) (t w : ℝ) :
    SourceMeanExecutable.rowBound (m := 1) (1/64) 16 1 t w ≤ 1/2 ∧
    1/2 < SourceMeanExecutable.rowBound (m := 1) ((1/64)*M.R)
      (finalWidth M.R 16) 1 t w := by
  constructor
  · norm_num [SourceMeanExecutable.rowBound]
  · rw [mean_final_rowBound_eq]
    norm_num [rowCoefficient]
    have hs : 0 < Real.sqrt 3 := by positivity
    have hs2 : Real.sqrt 3 < 2 := by
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
    have hh : (1:ℝ)/2 < 1/Real.sqrt 3 := (lt_div_iff₀ hs).2 (by nlinarith)
    calc
      (1:ℝ)/2 < 1/Real.sqrt 3 := hh
      _ ≤ 1/Real.sqrt 3 + 4*M.R^2*(1/4096) := le_add_of_nonneg_right (by positivity)
      _ = _ := by ring

end AcceleratedLogConcave.Oracle.RecursiveCallAccounting
