import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Group.Bounded

/-! # Actual compact C² tests for the channel weak equation

The Hessian and its coordinate trace are literal Fréchet derivatives. All support,
continuity and finite bounds below follow from C² regularity and compact support.
No derivative bound or substitute Hessian is supplied as test data.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.HeatCalculus
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The actual coordinate trace of the Fréchet Hessian. -/
def compactTestLaplacian (f : E → ℝ) (z : E) : ℝ :=
  ∑ i, fderiv ℝ (fderiv ℝ f) z (EuclideanSpace.basisFun ι ℝ i)
    (EuclideanSpace.basisFun ι ℝ i)

theorem compactTest_hasFDerivAt {f : E → ℝ} (hf : ContDiff ℝ 2 f) (z : E) :
    HasFDerivAt f (fderiv ℝ f z) z :=
  (hf.differentiable (by norm_num) z).hasFDerivAt

theorem compactTest_hasFDerivAt_fderiv {f : E → ℝ} (hf : ContDiff ℝ 2 f) (z : E) :
    HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) z) z := by
  have h : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  exact (h.differentiable (by norm_num) z).hasFDerivAt

theorem continuous_compactTest_fderiv {f : E → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)

theorem continuous_compactTest_hessian {f : E → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (fderiv ℝ (fderiv ℝ f)) := by
  have h : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  exact h.continuous_fderiv (by norm_num)

omit [Fintype ι] in
theorem compactTest_derivatives_support {f : E → ℝ} (hc : HasCompactSupport f) :
    HasCompactSupport (fderiv ℝ f) ∧ HasCompactSupport (fderiv ℝ (fderiv ℝ f)) :=
  ⟨hc.fderiv ℝ, (hc.fderiv ℝ).fderiv ℝ⟩

theorem compactTest_bounds {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) :
    ∃ C₀ C₁ C₂ : ℝ, 0 ≤ C₀ ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      (∀ z, ‖f z‖ ≤ C₀) ∧ (∀ z, ‖fderiv ℝ f z‖ ≤ C₁) ∧
      (∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ C₂) := by
  have hb₀ : ∃ C : ℝ, ∀ z : E, ‖f z‖ ≤ C :=
    hf.continuous.bounded_above_of_compact_support hc
  have hb₁ : ∃ C : ℝ, ∀ z : E, ‖fderiv ℝ f z‖ ≤ C :=
    (hf.continuous_fderiv (by norm_num)).bounded_above_of_compact_support (hc.fderiv ℝ)
  have h2 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hb₂ : ∃ C : ℝ, ∀ z : E, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ C :=
    (h2.continuous_fderiv (by norm_num)).bounded_above_of_compact_support ((hc.fderiv ℝ).fderiv ℝ)
  obtain ⟨C₀,h₀⟩ := hb₀
  obtain ⟨C₁,h₁⟩ := hb₁
  obtain ⟨C₂,h₂⟩ := hb₂
  refine ⟨C₀,C₁,C₂,?_,?_,?_,h₀,h₁,h₂⟩
  · exact (norm_nonneg (f 0)).trans (h₀ 0)
  · exact (norm_nonneg (fderiv ℝ f 0)).trans (h₁ 0)
  · exact (norm_nonneg (fderiv ℝ (fderiv ℝ f) 0)).trans (h₂ 0)

theorem continuous_compactTestLaplacian {f : E → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (compactTestLaplacian f) := by
  have h := continuous_compactTest_hessian hf
  unfold compactTestLaplacian
  fun_prop

theorem compactTestLaplacian_norm_le (f : E → ℝ) (z : E) :
    ‖compactTestLaplacian f z‖ ≤ (Fintype.card ι : ℝ)*‖fderiv ℝ (fderiv ℝ f) z‖ := by
  classical
  unfold compactTestLaplacian
  calc
    _ ≤ ∑ i, ‖fderiv ℝ (fderiv ℝ f) z (EuclideanSpace.basisFun ι ℝ i)
      (EuclideanSpace.basisFun ι ℝ i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, ‖fderiv ℝ (fderiv ℝ f) z‖ := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ‖fderiv ℝ (fderiv ℝ f) z (EuclideanSpace.basisFun ι ℝ i)‖ :=
          (fderiv ℝ (fderiv ℝ f) z _).unit_le_opNorm (EuclideanSpace.basisFun ι ℝ i) (by
            rw [(EuclideanSpace.basisFun ι ℝ).norm_eq_one])
        _ ≤ ‖fderiv ℝ (fderiv ℝ f) z‖ :=
          (fderiv ℝ (fderiv ℝ f) z).unit_le_opNorm (EuclideanSpace.basisFun ι ℝ i) (by
            rw [(EuclideanSpace.basisFun ι ℝ).norm_eq_one])
    _ = _ := by simp

theorem compactTestLaplacian_empty (f : EuclideanSpace ℝ (Fin 0) → ℝ)
    (z : EuclideanSpace ℝ (Fin 0)) : compactTestLaplacian f z = 0 := by
  simp [compactTestLaplacian]

end AcceleratedLogConcave.HeatCalculus
