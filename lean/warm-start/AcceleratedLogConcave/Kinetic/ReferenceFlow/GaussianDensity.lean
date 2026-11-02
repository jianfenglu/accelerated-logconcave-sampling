import AcceleratedLogConcave.Probability.WarmInitialization
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.FDeriv.Norm

/-! Actual volume density and classical score of Mathlib's finite-dimensional
standard Gaussian. The measure identity is proved from the independent real
Gaussian coordinates and the volume-preserving orthonormal coordinate map. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace Set Function
open scoped ENNReal Topology RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic

/-- Change of a nonnegative density under a proved measure-preserving equivalence. -/
theorem map_withDensity_of_measurePreserving {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] (e : A ≃ᵐ B)
    (μ : Measure A) (ν : Measure B) (he : MeasurePreserving e μ ν) (r : A → ℝ≥0∞) :
    (μ.withDensity r).map e = ν.withDensity (r ∘ e.symm) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs]
  simpa only [Function.comp_apply, e.symm_apply_apply] using
    he.setLIntegral_comp_preimage_emb e.measurableEmbedding (r ∘ e.symm) s

private theorem gaussian_pi_density (ι : Type*) [Fintype ι] :
    Measure.pi (fun _ : ι => gaussianReal 0 1) =
      volume.withDensity (fun x : ι → ℝ => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), volume_pi,
    Measure.restrict_pi_pi]
  have hI : Integrable (fun x : ι → ℝ => ∏ i, gaussianPDFReal 0 1 (x i))
      (Measure.pi (fun i => volume.restrict (s i))) :=
    Integrable.fintype_prod (fun _ => (integrable_gaussianPDFReal 0 1).restrict)
  rw [← ofReal_integral_eq_lintegral_ofReal hI
    (Filter.Eventually.of_forall (fun x => Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _))),
    integral_fintype_prod_eq_prod, ENNReal.ofReal_prod_of_nonneg]
  · apply Finset.prod_congr rfl
    intro i _
    rw [gaussianReal_of_var_ne_zero 0 (by norm_num), withDensity_apply _ (hs i)]
    exact ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPDFReal 0 1).restrict
      (Filter.Eventually.of_forall (gaussianPDFReal_nonneg 0 1))
  · intro i _
    exact integral_nonneg (gaussianPDFReal_nonneg 0 1)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The standard Gaussian density with the exact dimension-dependent normalization. -/
def standardGaussianDensity (x : E) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ ^ Module.finrank ℝ E * Real.exp (-‖x‖ ^ 2 / 2)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem standardGaussianDensity_pos (x : E) : 0 < standardGaussianDensity x := by
  unfold standardGaussianDensity
  positivity

private def gaussianCoordinates : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
  (stdOrthonormalBasis ℝ E).repr.toContinuousLinearEquiv.trans
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (Module.finrank ℝ E) => ℝ))

omit [MeasurableSpace E] [BorelSpace E] in
private theorem gaussianCoordinates_density (x : E) :
    (∏ i, gaussianPDFReal 0 1 (gaussianCoordinates x i)) = standardGaussianDensity x := by
  simp only [gaussianPDFReal, sub_zero, NNReal.coe_one, mul_one, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_sum, standardGaussianDensity]
  congr 1
  rw [← Finset.sum_div, Finset.sum_neg_distrib]
  congr 2
  simpa [gaussianCoordinates, OrthonormalBasis.repr_apply_apply] using
    congrArg Neg.neg ((stdOrthonormalBasis ℝ E).sum_sq_inner_right x)

/-- Mathlib's actual standard Gaussian equals the explicit smooth volume density. -/
theorem stdGaussian_eq_volume_density : stdGaussian E =
    volume.withDensity (fun x : E => ENNReal.ofReal (standardGaussianDensity x)) := by
  let e := (gaussianCoordinates (E := E)).symm.toHomeomorph.toMeasurableEquiv
  have hemp : MeasurePreserving e volume volume :=
    ((stdOrthonormalBasis ℝ E).repr.symm.measurePreserving).comp
      (PiLp.volume_preserving_toLp (Fin (Module.finrank ℝ E)))
  have heq : (stdGaussian E) = (Measure.pi (fun _ : Fin (Module.finrank ℝ E) => gaussianReal 0 1)).map e := by
    rw [stdGaussian]
    congr 1
    funext x
    exact ((stdOrthonormalBasis ℝ E).sum_repr_symm (WithLp.toLp 2 x))
  rw [heq, gaussian_pi_density,
    map_withDensity_of_measurePreserving e volume volume hemp]
  congr 1
  funext x
  exact congrArg ENNReal.ofReal (gaussianCoordinates_density x)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem standardGaussianDensity_contDiff : ContDiff ℝ 1 (standardGaussianDensity (E := E)) := by
  unfold standardGaussianDensity
  exact contDiff_const.mul (((contDiff_norm_sq ℝ (E := E)).neg.div_const 2).exp)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem standardGaussianDensity_hasFDerivAt (x : E) :
    HasFDerivAt standardGaussianDensity ((-standardGaussianDensity x) • innerSL ℝ x) x := by
  have h := (((hasFDerivAt_id x).norm_sq).neg.mul_const (2:ℝ)⁻¹).exp.const_mul
    ((Real.sqrt (2 * Real.pi))⁻¹ ^ Module.finrank ℝ E)
  convert h using 1
  · funext y
    simp [standardGaussianDensity, div_eq_mul_inv]
  · ext v
    simp [standardGaussianDensity, div_eq_mul_inv]
    ring

end AcceleratedLogConcave.Kinetic
