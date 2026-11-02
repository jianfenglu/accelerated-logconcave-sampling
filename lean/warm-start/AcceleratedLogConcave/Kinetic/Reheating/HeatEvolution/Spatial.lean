import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution

/-!
Spatial differentiation of actual Gaussian averages, including their actual
Hessian. The argument generalizes the compact-test differentiation proof in the
attributed HeatCalculus port to Banach-valued C1 functions; this permits the
second derivative without strengthening the source C2 assumption.
-/
noncomputable section
set_option maxHeartbeats 300000
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace AcceleratedLogConcave.Kinetic.Reheating
open AcceleratedLogConcave.HeatCalculus
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

private theorem integrable_compact_gaussian {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} (hf : Continuous f) (hc : HasCompactSupport f)
    (a : ℝ) (x : E) : Integrable (fun g => f (x + a • g)) (stdGaussian E) := by
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous hf
  exact (integrable_const C).mono' (by fun_prop : Continuous (fun g : E =>
    f (x + a • g))).aestronglyMeasurable (Eventually.of_forall fun g => hC _)

/-- Differentiating the actual integral requires only C1 of the integrand. -/
theorem gaussianAverage_hasFDerivAt {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {f : E → F}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (a : ℝ) (x : E) :
    HasFDerivAt (fun y => ∫ g, f (y + a • g) ∂stdGaussian E)
      (∫ g, fderiv ℝ f (x + a • g) ∂stdGaussian E) x := by
  have hd := hf.continuous_fderiv (by norm_num)
  obtain ⟨C,hC⟩ := (hc.fderiv ℝ).exists_bound_of_continuous hd
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y g => f (y + a • g))
    (F' := fun y g => fderiv ℝ f (y + a • g))
    (bound := fun _ : E => C) (s := Set.univ) (by simp)
    (Eventually.of_forall fun y =>
      (by fun_prop : Continuous (fun g : E => f (y + a • g))).aestronglyMeasurable)
    (integrable_compact_gaussian hf.continuous hc a x)
    (by fun_prop : Continuous (fun g : E => fderiv ℝ f (x + a • g))).aestronglyMeasurable
    (Eventually.of_forall fun g y _ => hC _) (integrable_const C)
  exact Eventually.of_forall fun g y _ => by
    simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq] using
      (hf.differentiable_one (y + a • g)).hasFDerivAt.comp y
        ((hasFDerivAt_id y).add_const (a • g))

/-- Compact continuous Banach-valued integrands have continuous Gaussian averages. -/
theorem gaussianAverage_continuous {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} (hf : Continuous f) (hc : HasCompactSupport f)
    (a : ℝ) : Continuous (fun y => ∫ g, f (y + a • g) ∂stdGaussian E) := by
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous hf
  apply continuous_of_dominated
    (F := fun (y : E) (g : E) => f (y + a • g))
    (μ := stdGaussian E) (bound := fun _ : E => C)
    (fun y => (by fun_prop : Continuous (fun g : E => f (y + a • g))).aestronglyMeasurable)
    (fun y => Eventually.of_forall fun g => hC _) (integrable_const C)
  exact Eventually.of_forall fun g => by fun_prop

theorem gaussianAverage_contDiff_one {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {f : E → F}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (a : ℝ) :
    ContDiff ℝ 1 (fun y => ∫ g, f (y + a • g) ∂stdGaussian E) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  exact ⟨_, gaussianAverage_continuous (hf.continuous_fderiv (by norm_num)) (hc.fderiv ℝ) a,
    gaussianAverage_hasFDerivAt hf hc a⟩

theorem heatAverage_fderiv {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (t : ℝ) (x : E) :
    fderiv ℝ (heatAverage f t) x =
      ∫ g, fderiv ℝ f (x + Real.sqrt t • g) ∂stdGaussian E :=
  (gaussianAverage_hasFDerivAt (hf.of_le (by norm_num)) hc _ x).fderiv

/-- Gaussian smoothing preserves the exact C2 regularity used in the source. -/
theorem heatAverage_contDiff_two {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (t : ℝ) : ContDiff ℝ 2 (heatAverage f t) := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_fderiv]
  refine ⟨fun x => (gaussianAverage_hasFDerivAt (hf.of_le (by norm_num)) hc _ x).differentiableAt, by simp, ?_⟩
  have he : fderiv ℝ (heatAverage f t) =
      fun y => ∫ g, fderiv ℝ f (y + Real.sqrt t • g) ∂stdGaussian E :=
    funext (heatAverage_fderiv hf hc t)
  rw [he]
  exact gaussianAverage_contDiff_one (hf.fderiv_right (by norm_num)) (hc.fderiv ℝ) _

/-- The actual Hessian of the Gaussian-smoothed compact C2 numerator. -/
theorem heatAverage_hessian {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (t : ℝ) (x : E) :
    fderiv ℝ (fderiv ℝ (heatAverage f t)) x =
      ∫ g, fderiv ℝ (fderiv ℝ f) (x + Real.sqrt t • g) ∂stdGaussian E := by
  have he : fderiv ℝ (heatAverage f t) =
      fun y => ∫ g, fderiv ℝ f (y + Real.sqrt t • g) ∂stdGaussian E :=
    funext (heatAverage_fderiv hf hc t)
  rw [he]
  exact (gaussianAverage_hasFDerivAt (hf.fderiv_right (by norm_num)) (hc.fderiv ℝ) _ x).fderiv

/-- Commutation with the literal trace of the Hessian, at physical variance t. -/
theorem heatAverage_laplacian {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (t : ℝ) (x : E) :
    compactTestLaplacian (heatAverage f t) x = heatAverage (compactTestLaplacian f) t x := by
  classical
  let b := EuclideanSpace.basisFun ι ℝ
  have hAvg := heatAverage_contDiff_two hf hc t
  have hfd (y : E) (v : E) : fderiv ℝ (heatAverage f t) y v =
      ∫ g, fderiv ℝ f (y + Real.sqrt t • g) v ∂stdGaussian E := by
    rw [heatAverage_fderiv hf hc]
    exact ContinuousLinearMap.integral_apply
      (integrable_compact_gaussian (continuous_compactTest_fderiv hf) (hc.fderiv ℝ) _ _) v
  have hdiag (i : ι) : fderiv ℝ (fderiv ℝ (heatAverage f t)) x (b i) (b i) =
      ∫ g, fderiv ℝ (fderiv ℝ f) (x + Real.sqrt t • g) (b i) (b i) ∂stdGaussian E := by
    let k : E → ℝ := fun y => fderiv ℝ f y (b i)
    have hk : ContDiff ℝ 1 k := (hf.fderiv_right (by norm_num)).clm_apply contDiff_const
    have hkc : HasCompactSupport k :=
      (hc.fderiv ℝ).comp_left (g := fun L : E →L[ℝ] ℝ => L (b i)) rfl
    have he : (fun y => fderiv ℝ (heatAverage f t) y (b i)) =
        fun y => ∫ g, k (y + Real.sqrt t • g) ∂stdGaussian E :=
      funext fun y => hfd y (b i)
    have hd := ((compactTest_hasFDerivAt_fderiv hAvg x).clm_apply
      (hasFDerivAt_const (b i) x))
    rw [he] at hd
    have hd2 := gaussianAverage_hasFDerivAt hk hkc (Real.sqrt t) x
    have hh := congrArg (fun L : E →L[ℝ] ℝ => L (b i)) (hd.unique hd2)
    simp only [ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply] at hh
    rw [ContinuousLinearMap.integral_apply
      (integrable_compact_gaussian (hk.continuous_fderiv (by norm_num))
        (hkc.fderiv ℝ) _ _)] at hh
    convert hh using 1
    apply integral_congr_ae
    filter_upwards [] with g
    have hd' := ((compactTest_hasFDerivAt_fderiv hf (x + Real.sqrt t • g)).clm_apply
      (hasFDerivAt_const (b i) (x + Real.sqrt t • g))).fderiv
    simpa [k] using (congrArg (fun L : E →L[ℝ] ℝ => L (b i)) hd').symm
  change (∑ i, fderiv ℝ (fderiv ℝ (heatAverage f t)) x (b i) (b i)) =
    ∫ g, ∑ i, fderiv ℝ (fderiv ℝ f) (x + Real.sqrt t • g) (b i) (b i) ∂stdGaussian E
  simp_rw [hdiag]
  exact (integral_finsetSum _ (fun i _ =>
    integrable_compactTest_scaled_hessian_coordinate hf hc (Real.sqrt t) x i)).symm

/-- The numerator solves the classical heat equation, with its actual Hessian. -/
theorem heatAverage_classical_heat {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) {t : ℝ} (ht : 0 < t) (x : E) :
    HasDerivAt (fun s => heatAverage f s x)
      ((1/2:ℝ) * compactTestLaplacian (heatAverage f t) x) t := by
  rw [heatAverage_laplacian hf hc]
  exact heatAverage_hasDerivAt hf hc ht x

end AcceleratedLogConcave.Kinetic.Reheating
