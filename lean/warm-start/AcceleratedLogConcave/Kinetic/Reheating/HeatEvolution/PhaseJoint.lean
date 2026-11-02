import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.PhaseDerivativeBounds

/-! Joint continuity for actual phase heat numerator derivatives. The compact
joint input supplies a single domination bound across retained momentum. -/
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson AcceleratedLogConcave.HeatCalculus
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Position-only Gaussian averaging preserves joint continuity in variance,
position and retained momentum, including zero variance. -/
theorem phaseGaussianAverage_joint_continuous {K : Type*} [NormedAddCommGroup K]
    [NormedSpace ℝ K] {h : E×E → K} (hh : Continuous h) (hc : HasCompactSupport h) :
    Continuous (fun z : ℝ×(E×E) => ∫ g, h (z.2.1+Real.sqrt z.1 • g,z.2.2) ∂stdGaussian E) := by
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous hh
  apply continuous_of_dominated (bound := fun _ : E => C)
  · intro z
    exact (by fun_prop : Continuous (fun g : E => h (z.2.1+Real.sqrt z.1 • g,z.2.2))).aestronglyMeasurable
  · intro z
    exact Eventually.of_forall fun g => hC _
  · exact integrable_const C
  · exact Eventually.of_forall fun g => by fun_prop

/-- The position derivative of every slice average is jointly continuous. -/
theorem phaseHeatAverage_joint_fderiv_continuous {h : E×E → ℝ}
    (hh : ContDiff ℝ 2 h) (hc : HasCompactSupport h) :
    Continuous (fun z : ℝ×(E×E) => fderiv ℝ
      (heatAverage (fun y => h (y,z.2.2)) z.1) z.2.1) := by
  simp only [heatAverage_fderiv (phase_position_slice_C2 hh _) (phase_position_slice_compact hc _),
    phase_slice_fderiv (hh.of_le (by norm_num))]
  exact phaseGaussianAverage_joint_continuous
    ((hh.continuous_fderiv (by norm_num)).clm_comp continuous_const)
    ((hc.fderiv ℝ).comp_left
      (g := fun L : E×E →L[ℝ] ℝ => L.comp (ContinuousLinearMap.inl ℝ E E)) (by simp))

/-- The genuine position Laplacian of the slice average is jointly continuous. -/
theorem phaseHeatAverage_joint_laplacian_continuous {h : E×E → ℝ}
    (hh : ContDiff ℝ 2 h) (hc : HasCompactSupport h) :
    Continuous (fun z : ℝ×(E×E) => compactTestLaplacian
      (heatAverage (fun y => h (y,z.2.2)) z.1) z.2.1) := by
  simp only [heatAverage_laplacian (phase_position_slice_C2 hh _) (phase_position_slice_compact hc _)]
  simp only [heatAverage, compactTestLaplacian, phase_slice_hessian hh]
  apply phaseGaussianAverage_joint_continuous (h := fun z : E×E => ∑ i,
    fderiv ℝ (fderiv ℝ h) z (EuclideanSpace.basisFun ι ℝ i,0) (EuclideanSpace.basisFun ι ℝ i,0))
  · have hH := (hh.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
    fun_prop
  · exact ((hc.fderiv ℝ).fderiv ℝ).comp_left
      (g := fun H : E×E →L[ℝ] (E×E →L[ℝ] ℝ) => ∑ i, H
        (EuclideanSpace.basisFun ι ℝ i,0) (EuclideanSpace.basisFun ι ℝ i,0)) (by simp)

/-- Actual phase numerator position derivatives are jointly continuous. -/
theorem compactPhaseHeatNumerator_fderiv_continuous {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    Continuous (fun z : ℝ×(E×E) => fderiv ℝ
      (compactHeatNumerator F (fun y => f (y,z.2.2)) z.1) z.2.1) := by
  have hh : ContDiff ℝ 2 (fun z : E×E => f z * F.density a z.1) :=
    hf.mul ((reference_density_C2 F a ⟨le_rfl,F.ordered⟩).comp contDiff_fst)
  have hhc : HasCompactSupport (fun z : E×E => f z * F.density a z.1) := hc.mul_right
  have hcont : Continuous (fun z : ℝ×(E×E) => (z.1-a,z.2)) :=
    (continuous_fst.sub continuous_const).prodMk continuous_snd
  unfold compactHeatNumerator
  exact (phaseHeatAverage_joint_fderiv_continuous hh hhc).comp hcont

/-- Actual phase numerator position Laplacians are jointly continuous. -/
theorem compactPhaseHeatNumerator_laplacian_continuous {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    Continuous (fun z : ℝ×(E×E) => compactTestLaplacian
      (compactHeatNumerator F (fun y => f (y,z.2.2)) z.1) z.2.1) := by
  have hh : ContDiff ℝ 2 (fun z : E×E => f z * F.density a z.1) :=
    hf.mul ((reference_density_C2 F a ⟨le_rfl,F.ordered⟩).comp contDiff_fst)
  have hhc : HasCompactSupport (fun z : E×E => f z * F.density a z.1) := hc.mul_right
  have hcont : Continuous (fun z : ℝ×(E×E) => (z.1-a,z.2)) :=
    (continuous_fst.sub continuous_const).prodMk continuous_snd
  have hb := (phaseHeatAverage_joint_laplacian_continuous hh hhc).comp hcont
  apply hb.congr
  intro z
  exact congrArg (fun k : E → ℝ => compactTestLaplacian k z.2.1)
    (show heatAverage (fun y => f (y,z.2.2)*F.density a y) (z.1-a) =
      compactHeatNumerator F (fun y => f (y,z.2.2)) z.1 from rfl)

end AcceleratedLogConcave.Kinetic.Reheating
