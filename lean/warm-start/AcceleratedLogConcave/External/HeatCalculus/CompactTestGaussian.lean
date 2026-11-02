import AcceleratedLogConcave.External.HeatCalculus.CompactTestIntegrability
import AcceleratedLogConcave.External.HeatCalculus.GaussianCoordinateIntegrationByParts

/-! # Genuine variance-one Gaussian correction for compact C² tests

The coordinate Stein hypotheses, including the coordinate-weighted integrability,
are derived from the actual compact-test bounds. The finite sum retains every
original coordinate and is valid in empty dimension.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.HeatCalculus
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

 theorem compactTest_coordinate_hasFDerivAt {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (y g e : E) :
    HasFDerivAt (fun w => fderiv ℝ f (y+w) e)
      ((fderiv ℝ (fderiv ℝ f) (y+g)).flip e) g := by
  simpa only [ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.comp_id,Function.comp_def] using
    (((compactTest_hasFDerivAt_fderiv hf (y+g)).comp g
      ((hasFDerivAt_id g).const_add y)).clm_apply (hasFDerivAt_const e g))

 theorem integrable_compactTest_coordinate {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (y : E) (i : ι) :
    Integrable (fun g => fderiv ℝ f (y+g) (EuclideanSpace.basisFun ι ℝ i))
      (stdGaussian E) :=
  integrable_compactTest_fderiv_apply hf hc (by fun_prop) (integrable_const _)

 theorem integrable_compactTest_hessian_coordinate {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (y : E) (i : ι) :
    Integrable (fun g => fderiv ℝ (fderiv ℝ f) (y+g)
      (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ i)) (stdGaussian E) := by
  obtain ⟨C₀,C₁,C₂,h₀,h₁,h₂,b₀,b₁,b₂⟩ := compactTest_bounds hf hc
  have hd := continuous_compactTest_hessian hf
  apply (integrable_const C₂).mono' (by fun_prop : Continuous (fun g : E =>
    fderiv ℝ (fderiv ℝ f) (y+g) (EuclideanSpace.basisFun ι ℝ i)
      (EuclideanSpace.basisFun ι ℝ i))).aestronglyMeasurable
  filter_upwards [] with g
  exact ((fderiv ℝ (fderiv ℝ f) (y+g) _).unit_le_opNorm _
    (by rw [(EuclideanSpace.basisFun ι ℝ).norm_eq_one])).trans
    (((fderiv ℝ (fderiv ℝ f) (y+g)).unit_le_opNorm _
      (by rw [(EuclideanSpace.basisFun ι ℝ).norm_eq_one])).trans (b₂ _))

 theorem integrable_compactTest_weighted_coordinate {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (y : E) (i : ι) :
    Integrable (fun g : E => g i * fderiv ℝ f (y+g) (EuclideanSpace.basisFun ι ℝ i))
      (stdGaussian E) := by
  obtain ⟨C₀,C₁,C₂,h₀,h₁,h₂,b₀,b₁,b₂⟩ := compactTest_bounds hf hc
  have hd := continuous_compactTest_fderiv hf
  have hi : Integrable (fun g : E => g i) (stdGaussian E) :=
    by
    have hx : MemLp (fun g : E => g i) 2 (stdGaussian E) := by
      simpa only [EuclideanSpace.basisFun_inner,id_eq] using
        (IsGaussian.memLp_two_id (μ := stdGaussian E)).const_inner (𝕜 := ℝ)
          (EuclideanSpace.basisFun ι ℝ i)
    exact hx.integrable (by norm_num)
  apply (hi.norm.mul_const C₁).mono' (by fun_prop : Continuous (fun g : E =>
    g i * fderiv ℝ f (y+g) (EuclideanSpace.basisFun ι ℝ i))).aestronglyMeasurable
  filter_upwards [] with g
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (((fderiv ℝ f (y+g)).unit_le_opNorm _
      (by rw [(EuclideanSpace.basisFun ι ℝ).norm_eq_one])).trans (b₁ _)) (norm_nonneg _)

 theorem compactTest_gaussian_coordinate {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (y : E) (i : ι) :
    (∫ g : E, g i * fderiv ℝ f (y+g) (EuclideanSpace.basisFun ι ℝ i) ∂stdGaussian E) =
      ∫ g : E, fderiv ℝ (fderiv ℝ f) (y+g)
        (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ i) ∂stdGaussian E := by
  classical
  exact stdGaussian_integral_coordinate_mul_of_hasFDerivAt i
    (f' := fun g => (fderiv ℝ (fderiv ℝ f) (y+g)).flip (EuclideanSpace.basisFun ι ℝ i))
    (fun g => compactTest_coordinate_hasFDerivAt hf y g _)
    (integrable_compactTest_coordinate hf hc y i)
    (integrable_compactTest_hessian_coordinate hf hc y i)
    (integrable_compactTest_weighted_coordinate hf hc y i)

 theorem compactTest_fderiv_sum_coordinates (f : E → ℝ) (z g : E) :
    (∑ i, g i * fderiv ℝ f z (EuclideanSpace.basisFun ι ℝ i)) = fderiv ℝ f z g := by
  calc
    _ = fderiv ℝ f z (∑ i, (EuclideanSpace.basisFun ι ℝ).repr g i •
      EuclideanSpace.basisFun ι ℝ i) := by
        simp only [map_sum,map_smul,EuclideanSpace.basisFun_repr,smul_eq_mul]
    _ = _ := by rw [(EuclideanSpace.basisFun ι ℝ).sum_repr g]

 theorem compactTest_gaussian_correction {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (y : E) :
    (∫ g : E, fderiv ℝ f (y+g) g ∂stdGaussian E) =
      ∫ g : E, compactTestLaplacian f (y+g) ∂stdGaussian E := by
  classical
  calc
    _ = ∫ g : E, ∑ i, g i * fderiv ℝ f (y+g) (EuclideanSpace.basisFun ι ℝ i)
      ∂stdGaussian E := integral_congr_ae (Filter.Eventually.of_forall fun g =>
        (compactTest_fderiv_sum_coordinates f (y+g) g).symm)
    _ = _ := by
      unfold compactTestLaplacian
      rw [integral_finsetSum _ (fun i _ => integrable_compactTest_weighted_coordinate hf hc y i),
        integral_finsetSum _ (fun i _ => integrable_compactTest_hessian_coordinate hf hc y i)]
      exact Finset.sum_congr rfl (fun i _ => compactTest_gaussian_coordinate hf hc y i)

end AcceleratedLogConcave.HeatCalculus
