import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Integral.Prod

/-! Exact Gaussian contraction, retaining the Hilbert–Schmidt sum rather than
an operator-norm times dimension bound. The product-law theorem requires actual
independence and explicit integrability; it does not assert independence after
transport. Source: warm-start.tex lines 2005–2007. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Analysis.GaussianLinearIsometry
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The covariance identity for the literal standard Gaussian. -/
theorem integral_inner_mul (u v : E) :
    (∫ z, ⟪u, z⟫ * ⟪v, z⟫ ∂stdGaussian E) = ⟪u, v⟫ := by
  have h := covarianceBilin_apply (IsGaussian.memLp_two_id (μ := stdGaussian E)) u v
  rw [covarianceBilin_stdGaussian] at h
  change ⟪u, v⟫ = _ at h
  simpa only [integral_id_stdGaussian, id_eq, sub_zero] using h.symm

/-- Gaussian contraction for two actual continuous linear maps, in any finite
orthonormal basis of the input space. The output need not be finite dimensional. -/
theorem integral_inner_linear {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (A B : E →L[ℝ] F) :
    (∫ z, ⟪A z, B z⟫ ∂stdGaussian E) = ∑ i, ⟪A (b i), B (b i)⟫ := by
  classical
  have hi (i j : ι) : Integrable
      (fun z => (⟪b i, z⟫ * ⟪b j, z⟫) * ⟪A (b i), B (b j)⟫)
      (stdGaussian E) := by
    exact (((IsGaussian.memLp_two_id (μ := stdGaussian E)).const_inner (b i)).integrable_mul
      ((IsGaussian.memLp_two_id (μ := stdGaussian E)).const_inner (b j))).mul_const _
  have heq (z : E) : ⟪A z, B z⟫ =
      ∑ i, ∑ j, (⟪b i, z⟫ * ⟪b j, z⟫) * ⟪A (b i), B (b j)⟫ := by
    nth_rw 1 [← b.sum_repr' z]
    nth_rw 2 [← b.sum_repr' z]
    simp only [map_sum, map_smul]
    rw [sum_inner]
    simp only [inner_sum, real_inner_smul_left, real_inner_smul_right, mul_assoc, mul_left_comm]
  simp_rw [heq]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hi _ j), integral_mul_const,
    integral_inner_mul, orthonormal_iff_ite.mp b.orthonormal]
  simp

/-- Exact squared Hilbert–Schmidt isometry, including zero-dimensional input. -/
theorem integral_norm_sq_linear {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] F) :
    (∫ z, ‖A z‖ ^ 2 ∂stdGaussian E) = ∑ i, ‖A (b i)‖ ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq] using integral_inner_linear b A A

/-- Spatially varying coefficients, on the literal independent product law.
The integrability hypothesis is explicit, so the Bochner integral is not being
silently totalized in a nonintegrable case. -/
theorem integral_norm_sq_linear_prod {X ι : Type*} [MeasurableSpace X]
    [Fintype ι] (μ : Measure X) [SFinite μ]
    (b : OrthonormalBasis ι ℝ E) (A : X → E →L[ℝ] F)
    (hA : Integrable (fun z : X × E => ‖A z.1 z.2‖ ^ 2) (μ.prod (stdGaussian E))) :
    (∫ z : X × E, ‖A z.1 z.2‖ ^ 2 ∂μ.prod (stdGaussian E)) =
      ∫ x, ∑ i, ‖A x (b i)‖ ^ 2 ∂μ := by
  rw [integral_prod _ hA]
  simp_rw [integral_norm_sq_linear b]

end AcceleratedLogConcave.Analysis.GaussianLinearIsometry
