import AcceleratedLogConcave.Kinetic.GaussianEmbedding
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Transposing weak Hessian rows and Gaussian phase norms

The coordinate transpose converts gradients of vector-field coefficients into
position-derivative directions. Its L2 squared norm is exactly preserved;
standard Gaussian covariance then gives the same identity on phase space.
-/
noncomputable section
open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E)

/-- Transpose coordinate rows in the fixed orthonormal basis. -/
def transposeGradientRows (R : Fin (Module.finrank ℝ E) → Lp E 2 μ)
    (i : Fin (Module.finrank ℝ E)) : Lp E 2 μ :=
  ∑ j, (ContinuousLinearMap.toSpanSingleton ℝ ((stdOrthonormalBasis ℝ E) j)).compLp
    ((innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).compLp (R j))

omit [BorelSpace E] in
theorem transposeGradientRows_coe (R : Fin (Module.finrank ℝ E) → Lp E 2 μ)
    (i : Fin (Module.finrank ℝ E)) :
    transposeGradientRows μ R i =ᵐ[μ] fun x =>
      ∑ j, inner ℝ ((stdOrthonormalBasis ℝ E) i) (R j x) • ((stdOrthonormalBasis ℝ E) j) := by
  apply (Lp.coeFn_finsetSum _ _).trans
  have hterm (j : Fin (Module.finrank ℝ E)) :
      (ContinuousLinearMap.toSpanSingleton ℝ ((stdOrthonormalBasis ℝ E) j)).compLp
        ((innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).compLp (R j)) =ᵐ[μ]
      fun x => inner ℝ ((stdOrthonormalBasis ℝ E) i) (R j x) • ((stdOrthonormalBasis ℝ E) j) := by
    filter_upwards [(ContinuousLinearMap.toSpanSingleton ℝ ((stdOrthonormalBasis ℝ E) j)).coeFn_compLp
        ((innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).compLp (R j)),
      (innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).coeFn_compLp (R j)] with x hx hy
    rw [hx, hy]
    rfl
  filter_upwards [ae_all_iff.mpr hterm] with x hx
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun j _ => hx j)

omit [MeasurableSpace E] [BorelSpace E] in
private theorem transpose_rows_norm_sq_sum (R : Fin (Module.finrank ℝ E) → E) :
    ∑ i, ‖∑ j, inner ℝ ((stdOrthonormalBasis ℝ E) i) (R j) • ((stdOrthonormalBasis ℝ E) j)‖ ^ 2 =
      ∑ j, ‖R j‖ ^ 2 := by
  let b := stdOrthonormalBasis ℝ E
  have hcoord (i k) : inner ℝ (b k) (∑ j, inner ℝ (b i) (R j) • b j) = inner ℝ (b i) (R k) := by
    simp only [inner_sum, inner_smul_right, b.inner_eq_ite]
    simp
  calc
    _ = ∑ i, ∑ k, (inner ℝ (b i) (R k)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← b.sum_sq_inner_right]
      apply Finset.sum_congr rfl
      intro k _
      rw [hcoord]
    _ = ∑ k, ∑ i, (inner ℝ (b i) (R k)) ^ 2 := Finset.sum_comm
    _ = _ := by simp only [b.sum_sq_inner_right]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
private theorem norm_sq_eq_integral {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (G : Lp F 2 μ) : ‖G‖ ^ 2 = ∫ x, ‖G x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

omit [BorelSpace E] in
/-- Transposition preserves the actual weighted L2 Hilbert--Schmidt norm. -/
theorem transposeGradientRows_norm_sq_sum (R : Fin (Module.finrank ℝ E) → Lp E 2 μ) :
    ∑ i, ‖transposeGradientRows μ R i‖ ^ 2 = ∑ j, ‖R j‖ ^ 2 := by
  have hI (G : Lp E 2 μ) : Integrable (fun x => ‖G x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable G)).mp (Lp.memLp G)
  simp only [norm_sq_eq_integral]
  rw [← integral_finsetSum _ (fun i _ => hI (transposeGradientRows μ R i)),
    ← integral_finsetSum _ (fun j _ => hI (R j))]
  apply integral_congr_ae
  have hall : ∀ᵐ x ∂μ, ∀ i, transposeGradientRows μ R i x =
      ∑ j, inner ℝ ((stdOrthonormalBasis ℝ E) i) (R j x) • ((stdOrthonormalBasis ℝ E) j) :=
    (ae_all_iff).mpr (fun i => transposeGradientRows_coe μ R i)
  filter_upwards [hall] with x hx
  simp only [hx]
  exact transpose_rows_norm_sq_sum (fun j => R j x)

omit [BorelSpace E] in
/-- Parseval for the actual L2 coordinate fields. -/
theorem gradientComponents_norm_sq_sum (G : Lp E 2 μ) :
    ∑ i, ‖(innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).compLp G‖ ^ 2 = ‖G‖ ^ 2 := by
  have hI (i : Fin (Module.finrank ℝ E)) : Integrable
      (fun x => ‖((innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).compLp G) x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
  simp only [norm_sq_eq_integral]
  rw [← integral_finsetSum _ (fun i _ => hI i)]
  apply integral_congr_ae
  have hall : ∀ᵐ x ∂μ, ∀ i, ((innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).compLp G) x =
      inner ℝ ((stdOrthonormalBasis ℝ E) i) (G x) :=
    ae_all_iff.mpr (fun i => (innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).coeFn_compLp G)
  filter_upwards [hall] with x hx
  simp only [hx, Real.norm_eq_abs, sq_abs]
  exact (stdOrthonormalBasis ℝ E).sum_sq_inner_right (G x)

omit [BorelSpace E] in
/-- Position embedding also preserves the weak-gradient coordinate norm. -/
theorem gaussianPositionGradientComponents_norm_sq_sum [IsProbabilityMeasure μ] (G : Lp E 2 μ) :
    ∑ i, ‖positionEmbedding μ ((innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).compLp G)‖ ^ 2 = ‖G‖ ^ 2 := by
  simp only [(positionEmbedding μ).norm_map]
  exact gradientComponents_norm_sq_sum μ G

/-- Standard Gaussian covariance preserves the transposed-row norm in phase L2. -/
theorem gaussianTransposeGradientRows_norm_sq_sum [IsProbabilityMeasure μ]
    (R : Fin (Module.finrank ℝ E) → Lp E 2 μ) :
    ∑ i, ‖gaussianMomentumEmbedding μ (transposeGradientRows μ R i)‖ ^ 2 = ∑ j, ‖R j‖ ^ 2 := by
  simp only [(gaussianMomentumEmbedding μ).norm_map]
  exact transposeGradientRows_norm_sq_sum μ R
end AcceleratedLogConcave.Kinetic
