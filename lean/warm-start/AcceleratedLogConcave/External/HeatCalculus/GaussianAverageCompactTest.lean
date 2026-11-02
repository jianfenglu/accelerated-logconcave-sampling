import AcceleratedLogConcave.External.HeatCalculus.CompactTestGaussian
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! # Gaussian averages of genuine compact C² tests

The scalar scale parameter is differentiated under the actual Gaussian integral.
The resulting derivative is converted to the Laplacian by the coordinate Stein
identity. The zero-variance endpoint follows by continuity, without asserting a
derivative of the square root at zero.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace AcceleratedLogConcave.HeatCalculus
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Gaussian averaging with scalar noise scale. -/
def gaussianScaleCompactTest (f : E → ℝ) (a : ℝ) (x : E) : ℝ :=
  ∫ g : E, f (x + a • g) ∂stdGaussian E

/-- Heat averaging, with variance `2 * r` in each Euclidean coordinate. -/
def heatCompactTest (f : E → ℝ) (r : ℝ) (x : E) : ℝ :=
  gaussianScaleCompactTest f (Real.sqrt (2 * r)) x

@[simp] theorem gaussianScaleCompactTest_zero (f : E → ℝ) (x : E) :
    gaussianScaleCompactTest f 0 x = f x := by
  simp [gaussianScaleCompactTest]

@[simp] theorem heatCompactTest_zero (f : E → ℝ) (x : E) :
    heatCompactTest f 0 x = f x := by
  simp [heatCompactTest]

 theorem hasDerivAt_gaussianScaleCompactTest {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) (a : ℝ) (x : E) :
    HasDerivAt (fun b => gaussianScaleCompactTest f b x)
      (∫ g : E, fderiv ℝ f (x + a • g) g ∂stdGaussian E) a := by
  obtain ⟨C₀,C₁,C₂,h₀,h₁,h₂,b₀,b₁,b₂⟩ := compactTest_bounds hf hc
  have hd := continuous_compactTest_fderiv hf
  have hg : Integrable (id : E → E) (stdGaussian E) :=
    (IsGaussian.memLp_two_id (μ := stdGaussian E)).integrable (by norm_num)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun b g => f (x + b • g))
    (F' := fun b g => fderiv ℝ f (x + b • g) g)
    (bound := fun g => C₁ * ‖g‖) (s := Set.univ) (by simp)
    (Eventually.of_forall fun b =>
      (by fun_prop : Continuous (fun g : E => f (x + b • g))).aestronglyMeasurable)
    (integrable_compactTest_comp hf hc (by fun_prop))
    (by fun_prop : Continuous (fun g : E => fderiv ℝ f (x + a • g) g)).aestronglyMeasurable
    ?_ (hg.norm.const_mul C₁) ?_).2
  · exact Eventually.of_forall fun g b _ =>
      ((fderiv ℝ f (x + b • g)).le_opNorm g).trans
        (mul_le_mul_of_nonneg_right (b₁ _) (norm_nonneg _))
  · exact Eventually.of_forall fun g b _ => by
      simpa only [one_smul, Function.comp_def, id_eq] using
        ((hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp_hasDerivAt b
          (((hasDerivAt_id b).smul_const g).const_add x))

 theorem continuous_gaussianScaleCompactTest {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) (x : E) :
    Continuous (fun a => gaussianScaleCompactTest f a x) :=
  continuous_iff_continuousAt.mpr fun a =>
    (hasDerivAt_gaussianScaleCompactTest hf hc a x).continuousAt

 theorem continuous_heatCompactTest {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) (x : E) :
    Continuous (fun r => heatCompactTest f r x) :=
  (continuous_gaussianScaleCompactTest hf hc x).comp (by fun_prop)

 theorem tendsto_heatCompactTest_zero {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) (x : E) :
    Tendsto (fun r => heatCompactTest f r x) (𝓝 0) (𝓝 (f x)) := by
  simpa only [ContinuousAt, heatCompactTest_zero] using
    (continuous_heatCompactTest hf hc x).continuousAt (x := 0)

 theorem integrable_compactTest_scaled_hessian_coordinate {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) (a : ℝ) (x : E) (i : ι) :
    Integrable (fun g : E => fderiv ℝ (fderiv ℝ f) (x + a • g)
      (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ i)) (stdGaussian E) := by
  obtain ⟨C₀,C₁,C₂,h₀,h₁,h₂,b₀,b₁,b₂⟩ := compactTest_bounds hf hc
  have hd := continuous_compactTest_hessian hf
  apply (integrable_const C₂).mono' (by fun_prop : Continuous (fun g : E =>
    fderiv ℝ (fderiv ℝ f) (x + a • g) (EuclideanSpace.basisFun ι ℝ i)
      (EuclideanSpace.basisFun ι ℝ i))).aestronglyMeasurable
  exact Eventually.of_forall fun g =>
    ((fderiv ℝ (fderiv ℝ f) (x + a • g) _).unit_le_opNorm _
      (by rw [(EuclideanSpace.basisFun ι ℝ).norm_eq_one])).trans
    (((fderiv ℝ (fderiv ℝ f) (x + a • g)).unit_le_opNorm _
      (by rw [(EuclideanSpace.basisFun ι ℝ).norm_eq_one])).trans (b₂ _))

 theorem integrable_compactTest_scaled_weighted_coordinate {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) (a : ℝ) (x : E) (i : ι) :
    Integrable (fun g : E => g i * fderiv ℝ f (x + a • g)
      (EuclideanSpace.basisFun ι ℝ i)) (stdGaussian E) := by
  obtain ⟨C₀,C₁,C₂,h₀,h₁,h₂,b₀,b₁,b₂⟩ := compactTest_bounds hf hc
  have hd := continuous_compactTest_fderiv hf
  have hi : Integrable (fun g : E => g i) (stdGaussian E) := by
    have hx : MemLp (fun g : E => g i) 2 (stdGaussian E) := by
      simpa only [EuclideanSpace.basisFun_inner,id_eq] using
        (IsGaussian.memLp_two_id (μ := stdGaussian E)).const_inner (𝕜 := ℝ)
          (EuclideanSpace.basisFun ι ℝ i)
    exact hx.integrable (by norm_num)
  apply (hi.norm.mul_const C₁).mono' (by fun_prop : Continuous (fun g : E =>
    g i * fderiv ℝ f (x + a • g) (EuclideanSpace.basisFun ι ℝ i))).aestronglyMeasurable
  filter_upwards [] with g
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (((fderiv ℝ f (x + a • g)).unit_le_opNorm _
      (by rw [(EuclideanSpace.basisFun ι ℝ).norm_eq_one])).trans (b₁ _)) (norm_nonneg _)

 theorem compactTest_scaled_coordinate_hasFDerivAt {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (a : ℝ) (x g e : E) :
    HasFDerivAt (fun w => fderiv ℝ f (x + a • w) e)
      (a • (fderiv ℝ (fderiv ℝ f) (x + a • g)).flip e) g := by
  convert (((compactTest_hasFDerivAt_fderiv hf (x + a • g)).comp g
    (((hasFDerivAt_id g).const_smul a).const_add x)).clm_apply
      (hasFDerivAt_const e g)) using 1 <;>
    simp

 theorem compactTest_scaled_gaussian_coordinate {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) (a : ℝ) (x : E) (i : ι) :
    (∫ g : E, g i * fderiv ℝ f (x + a • g) (EuclideanSpace.basisFun ι ℝ i)
      ∂stdGaussian E) =
      a * ∫ g : E, fderiv ℝ (fderiv ℝ f) (x + a • g)
        (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ i) ∂stdGaussian E := by
  classical
  have h := stdGaussian_integral_coordinate_mul_of_hasFDerivAt i
    (fun g => compactTest_scaled_coordinate_hasFDerivAt hf a x g
      (EuclideanSpace.basisFun ι ℝ i))
    (integrable_compactTest_fderiv_apply hf hc (by fun_prop) (integrable_const _))
    (by simpa using (integrable_compactTest_scaled_hessian_coordinate hf hc a x i).const_mul a)
    (integrable_compactTest_scaled_weighted_coordinate hf hc a x i)
  simpa only [smul_apply, ContinuousLinearMap.flip_apply,
    smul_eq_mul, integral_const_mul] using h

/-- Scaled Stein correction, including the degenerate scale `a = 0`. -/
 theorem compactTest_scaled_gaussian_correction {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) (a : ℝ) (x : E) :
    (∫ g : E, fderiv ℝ f (x + a • g) g ∂stdGaussian E) =
      a * ∫ g : E, compactTestLaplacian f (x + a • g) ∂stdGaussian E := by
  classical
  calc
    _ = ∫ g : E, ∑ i, g i * fderiv ℝ f (x + a • g) (EuclideanSpace.basisFun ι ℝ i)
      ∂stdGaussian E := integral_congr_ae (Eventually.of_forall fun g =>
        (compactTest_fderiv_sum_coordinates f (x + a • g) g).symm)
    _ = _ := by
      unfold compactTestLaplacian
      rw [integral_finsetSum _ (fun i _ =>
        integrable_compactTest_scaled_weighted_coordinate hf hc a x i),
        integral_finsetSum _ (fun i _ =>
          integrable_compactTest_scaled_hessian_coordinate hf hc a x i), Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => compactTest_scaled_gaussian_coordinate hf hc a x i)

/-- The genuine positive-time heat identity. The derivative and the trace on the
right are both derived from `f`; no PDE certificate is an input. -/
 theorem hasDerivAt_heatCompactTest {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) {r : ℝ} (hr : 0 < r) (x : E) :
    HasDerivAt (fun s => heatCompactTest f s x)
      (∫ g : E, compactTestLaplacian f (x + Real.sqrt (2 * r) • g) ∂stdGaussian E) r := by
  have hpos : 0 < 2 * r := by positivity
  have hsqrt : Real.sqrt (2 * r) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  have hs : HasDerivAt (fun s : ℝ => Real.sqrt (2 * s))
      (2 / (2 * Real.sqrt (2 * r))) r := by
    simpa using ((hasDerivAt_id r).const_mul 2).sqrt (ne_of_gt hpos)
  have h := (hasDerivAt_gaussianScaleCompactTest hf hc (Real.sqrt (2 * r)) x).comp r hs
  rw [compactTest_scaled_gaussian_correction hf hc] at h
  convert h using 1
  · rfl
  · field_simp

/-- Joint continuity of Gaussian scalar averages from a literal uniform bound. -/
 theorem continuous_gaussianScaleCompactTest_joint_of_bounded {f : E → ℝ}
    (hf : Continuous f) {C : ℝ} (hC : ∀ z, ‖f z‖ ≤ C) :
    Continuous (fun p : ℝ × E => gaussianScaleCompactTest f p.1 p.2) := by
  apply continuous_of_dominated
    (F := fun (p : ℝ × E) (g : E) => f (p.2 + p.1 • g))
    (μ := stdGaussian E) (bound := fun _ : E => C)
    (fun p => (by fun_prop : Continuous (fun g : E => f (p.2 + p.1 • g))).aestronglyMeasurable)
    (fun p => Eventually.of_forall fun g => hC _) (integrable_const C)
  exact Eventually.of_forall fun g => by fun_prop

 theorem continuous_heatCompactTest_laplacian {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) (x : E) :
    Continuous (fun r => ∫ g : E,
      compactTestLaplacian f (x + Real.sqrt (2 * r) • g) ∂stdGaussian E) := by
  obtain ⟨C₀,C₁,C₂,h₀,h₁,h₂,b₀,b₁,b₂⟩ := compactTest_bounds hf hc
  have h := continuous_gaussianScaleCompactTest_joint_of_bounded
    (continuous_compactTestLaplacian hf)
    (fun z => (compactTestLaplacian_norm_le f z).trans
      (mul_le_mul_of_nonneg_left (b₂ z) (by positivity)))
  exact h.comp (by fun_prop : Continuous (fun r : ℝ => (Real.sqrt (2 * r), x)))

 theorem tendsto_heatCompactTest_laplacian_zero {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) (x : E) :
    Tendsto (fun r => ∫ g : E,
      compactTestLaplacian f (x + Real.sqrt (2 * r) • g) ∂stdGaussian E)
      (𝓝 0) (𝓝 (compactTestLaplacian f x)) := by
  simpa [ContinuousAt] using
    (continuous_heatCompactTest_laplacian hf hc x).continuousAt (x := 0)

/-- Spatial differentiation under the Gaussian integral at any scale. -/
 theorem hasFDerivAt_gaussianScaleCompactTest {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) (a : ℝ) (x : E) :
    HasFDerivAt (gaussianScaleCompactTest f a)
      (∫ g : E, fderiv ℝ f (x + a • g) ∂stdGaussian E) x := by
  obtain ⟨C₀,C₁,C₂,h₀,h₁,h₂,b₀,b₁,b₂⟩ := compactTest_bounds hf hc
  have hd := continuous_compactTest_fderiv hf
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y g => f (y + a • g))
    (F' := fun y g => fderiv ℝ f (y + a • g))
    (bound := fun _ : E => C₁) (s := Set.univ) (by simp)
    (Eventually.of_forall fun y =>
      (by fun_prop : Continuous (fun g : E => f (y + a • g))).aestronglyMeasurable)
    (integrable_compactTest_comp hf hc (by fun_prop))
    (by fun_prop : Continuous (fun g : E => fderiv ℝ f (x + a • g))).aestronglyMeasurable
    (Eventually.of_forall fun g y _ => b₁ _) (integrable_const C₁)
  exact Eventually.of_forall fun g y _ => by
    simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq] using
      (compactTest_hasFDerivAt hf (y + a • g)).comp y
        ((hasFDerivAt_id y).add_const (a • g))

 theorem fderiv_heatCompactTest {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) (r : ℝ) (x : E) :
    fderiv ℝ (heatCompactTest f r) x =
      ∫ g : E, fderiv ℝ f (x + Real.sqrt (2 * r) • g) ∂stdGaussian E :=
  (hasFDerivAt_gaussianScaleCompactTest hf hc (Real.sqrt (2 * r)) x).fderiv

 theorem fderiv_heatCompactTest_apply {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) (r : ℝ) (x v : E) :
    fderiv ℝ (heatCompactTest f r) x v =
      ∫ g : E, fderiv ℝ f (x + Real.sqrt (2 * r) • g) v ∂stdGaussian E := by
  rw [fderiv_heatCompactTest hf hc]
  apply ContinuousLinearMap.integral_apply
  obtain ⟨C₀,C₁,C₂,h₀,h₁,h₂,b₀,b₁,b₂⟩ := compactTest_bounds hf hc
  have hd := continuous_compactTest_fderiv hf
  exact (integrable_const C₁).mono'
    (by fun_prop : Continuous (fun g : E =>
      fderiv ℝ f (x + Real.sqrt (2 * r) • g))).aestronglyMeasurable
    (Eventually.of_forall fun g => b₁ _)

end AcceleratedLogConcave.HeatCalculus
