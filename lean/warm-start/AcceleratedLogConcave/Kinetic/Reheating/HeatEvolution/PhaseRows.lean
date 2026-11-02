import AcceleratedLogConcave.Kinetic.GaussianRows
import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.PhaseGreen

/-! Actual vector-valued momentum chaos of weak Hessian rows. Gaussian covariance
preserves the sum of squared row norms, giving the sharp phase gradient bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private theorem lp_norm_sq_integral {Ω K : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] (μ : Measure Ω) (g : Lp K 2 μ) :
    ‖g‖^2 = ∫ x, ‖g x‖^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

omit [MeasurableSpace E] [BorelSpace E] in
private theorem reconstruction_norm_sq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (r : Fin (Module.finrank ℝ E) → Lp ℝ 2 μ) :
    ‖∑ i, (ContinuousLinearMap.toSpanSingleton ℝ ((stdOrthonormalBasis ℝ E) i)).compLp (r i)‖^2 =
      ∑ i, ‖r i‖^2 := by
  let b := stdOrthonormalBasis ℝ E
  have hae : (∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLp (r i)) =ᵐ[μ]
      fun x => ∑ i, r i x • b i := by
    apply (Lp.coeFn_finsetSum _ _).trans
    have hi (i) := (ContinuousLinearMap.toSpanSingleton ℝ (b i)).coeFn_compLp (r i)
    filter_upwards [ae_all_iff.mpr hi] with x hx
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl (fun i _ => hx i)
  simp only [lp_norm_sq_integral]
  rw [← integral_finsetSum _ (fun i _ => (Lp.memLp (r i)).integrable_norm_pow (by norm_num))]
  apply integral_congr_ae
  filter_upwards [hae] with x hx
  rw [hx, ← b.sum_sq_inner_right]
  apply Finset.sum_congr rfl
  intro i _
  simp only [inner_sum, inner_smul_right, b.inner_eq_ite]
  simp

variable (μ : Measure E) [IsProbabilityMeasure μ]

/-- The actual vector phase gradient associated with weak component rows. -/
def momentumRowField (R : Fin (Module.finrank ℝ E) → Lp E 2 μ) :
    Lp E 2 (μ.prod (stdGaussian E)) :=
  ∑ i, (ContinuousLinearMap.toSpanSingleton ℝ ((stdOrthonormalBasis ℝ E) i)).compLp
    (momentumEmbedding μ (transposeGradientRows μ R i))

/-- Gaussian covariance gives exactly the weak Hessian's Hilbert--Schmidt norm. -/
theorem momentumRowField_norm_sq (R : Fin (Module.finrank ℝ E) → Lp E 2 μ) :
    ‖momentumRowField μ R‖^2 = ∑ j, ‖R j‖^2 := by
  rw [momentumRowField, reconstruction_norm_sq]
  simp only [(momentumEmbedding μ).norm_map]
  exact transposeGradientRows_norm_sq_sum μ R

/-- Its representative is the literal Gaussian linear combination of the rows. -/
theorem momentumRowField_coe (R : Fin (Module.finrank ℝ E) → Lp E 2 μ) :
    momentumRowField μ R =ᵐ[μ.prod (stdGaussian E)] fun z =>
      ∑ j, inner ℝ ((stdOrthonormalBasis ℝ E) j) z.2 • R j z.1 := by
  let b := stdOrthonormalBasis ℝ E
  have hterm (i) :
      (ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLp
        (momentumEmbedding μ (transposeGradientRows μ R i)) =ᵐ[μ.prod (stdGaussian E)]
      fun z => inner ℝ (∑ j, inner ℝ (b i) (R j z.1) • b j) z.2 • b i := by
    filter_upwards [(ContinuousLinearMap.toSpanSingleton ℝ (b i)).coeFn_compLp
        (momentumEmbedding μ (transposeGradientRows μ R i)),
      momentumEmbedding_coe μ (transposeGradientRows μ R i),
      measurePreserving_fst.quasiMeasurePreserving.ae (transposeGradientRows_coe μ R i)] with z hz hz' hz''
    rw [hz, hz', hz'']
    rfl
  apply (Lp.coeFn_finsetSum _ _).trans
  filter_upwards [ae_all_iff.mpr hterm] with z hz
  simp only [Finset.sum_apply]
  change (∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLp
    (momentumEmbedding μ (transposeGradientRows μ R i)) z) = ∑ j, inner ℝ (b j) z.2 • R j z.1
  simp only [hz, sum_inner, real_inner_smul_left, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = inner ℝ (b j) z.2 • ∑ i, inner ℝ (b i) (R j z.1) • b i := by
      simp only [Finset.smul_sum, smul_smul]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_comm]
    _ = _ := by rw [← OrthonormalBasis.repr_apply_apply, b.sum_repr']


end AcceleratedLogConcave.Kinetic.Reheating
