import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.PhaseCore
import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.DerivativeBounds

/-! Uniform position-derivative bounds for a joint compact visible heat input.
The constants are chosen on the original joint compact support, so they are
uniform in retained momentum as well as heat time, including zero variance. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson AcceleratedLogConcave.HeatCalculus
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The first position derivative is the genuine derivative restricted to the
position-coordinate inclusion. -/
theorem phase_slice_fderiv {f : E×E → ℝ} (hf : ContDiff ℝ 1 f) (x p : E) :
    fderiv ℝ (fun y => f (y,p)) x =
      (fderiv ℝ f (x,p)).comp (ContinuousLinearMap.inl ℝ E E) := by
  have hh := (hf.differentiable_one (x,p)).hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const p x))
  exact hh.fderiv

/-- The actual slice Hessian is the joint Hessian in the two position directions. -/
theorem phase_slice_hessian {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (x p v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => f (y,p))) x v w =
      fderiv ℝ (fderiv ℝ f) (x,p) (v,0) (w,0) := by
  have he : fderiv ℝ (fun y => f (y,p)) = fun y =>
      (fderiv ℝ f (y,p)).comp (ContinuousLinearMap.inl ℝ E E) := by
    funext y
    exact phase_slice_fderiv (hf.of_le (by norm_num)) y p
  rw [he]
  have hD := ((hf.fderiv_right (m := 1) (by norm_num)).differentiable_one (x,p)).hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const p x))
  have hh := hD.clm_comp (hasFDerivAt_const (ContinuousLinearMap.inl ℝ E E) x)
  dsimp only [Function.comp_def, id_eq] at hh
  rw [hh.fderiv]
  simp

omit [Fintype ι] in
private theorem joint_compact_norm_le_density {K : Type*} [NormedAddCommGroup K]
    {h : E×E → K} (hh : Continuous h) (hc : HasCompactSupport h)
    {p : E → ℝ} (hp : Continuous p) (hpos : ∀ x, 0 < p x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖h z‖ ≤ C*p z.1 := by
  have hs : HasCompactSupport (fun z => ‖h z‖ / p z.1) := by
    have hn := hc.comp_left (g := fun v : K => ‖v‖) norm_zero
    simp only [div_eq_mul_inv]
    exact hn.mul_right
  obtain ⟨C,hC⟩ := hs.exists_bound_of_continuous
    (hh.norm.div (hp.comp continuous_fst) (fun z => (hpos z.1).ne'))
  refine ⟨max C 0, le_max_right _ _, fun z => ?_⟩
  apply (div_le_iff₀ (hpos z.1)).mp
  exact (le_abs_self _).trans ((hC z).trans (le_max_left _ _))

/-- A single triple of constants bounds every slice numerator, position
first derivative and literal position Laplacian over the whole heat window. -/
theorem compactPhaseHeatNumerator_derivative_bounds {a b : ℝ}
    (F : ReferencePoissonFamily E a b) {f : E×E → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a)) :
    ∃ C₀ C₁ C₂ : ℝ, 0 ≤ C₀ ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      ∀ t ∈ Icc a b, ∀ x p,
        ‖compactHeatNumerator F (fun y => f (y,p)) t x‖ ≤ C₀*F.density t x ∧
        ‖fderiv ℝ (compactHeatNumerator F (fun y => f (y,p)) t) x‖ ≤ C₁*F.density t x ∧
        ‖compactTestLaplacian (compactHeatNumerator F (fun y => f (y,p)) t) x‖ ≤ C₂*F.density t x := by
  let h := fun z : E×E => f z * F.density a z.1
  have h2 : ContDiff ℝ 2 h := hf.mul ((reference_density_C2 F a ⟨le_rfl,F.ordered⟩).comp contDiff_fst)
  have hh : HasCompactSupport h := hc.mul_right
  let D := fun z => (fderiv ℝ h z).comp (ContinuousLinearMap.inl ℝ E E)
  let Δ := fun z => ∑ i, fderiv ℝ (fderiv ℝ h) z
    (EuclideanSpace.basisFun ι ℝ i,0) (EuclideanSpace.basisFun ι ℝ i,0)
  have hD : Continuous D := (h2.continuous_fderiv (by norm_num)).clm_comp continuous_const
  have hcD : HasCompactSupport D := (hh.fderiv ℝ).comp_left
    (g := fun L : E×E →L[ℝ] ℝ => L.comp (ContinuousLinearMap.inl ℝ E E)) (by simp)
  have hΔ : Continuous Δ := by
    have hh' := (h2.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
    dsimp [Δ]
    fun_prop
  have hcΔ : HasCompactSupport Δ := ((hh.fderiv ℝ).fderiv ℝ).comp_left
    (g := fun H : E×E →L[ℝ] (E×E →L[ℝ] ℝ) => ∑ i, H
      (EuclideanSpace.basisFun ι ℝ i,0) (EuclideanSpace.basisFun ι ℝ i,0)) (by simp)
  have hp := (reference_density_C2 F a ⟨le_rfl,F.ordered⟩).continuous
  have hpos := reference_density_pos F a ⟨le_rfl,F.ordered⟩
  obtain ⟨B,hB⟩ := reference_density_bounded F a ⟨le_rfl,F.ordered⟩
  obtain ⟨C₀,h₀,b₀⟩ := joint_compact_norm_le_density h2.continuous hh hp hpos
  obtain ⟨C₁,h₁,b₁⟩ := joint_compact_norm_le_density hD hcD hp hpos
  obtain ⟨C₂,h₂,b₂⟩ := joint_compact_norm_le_density hΔ hcΔ hp hpos
  refine ⟨C₀,C₁,C₂,h₀,h₁,h₂,fun t ht x p => ?_⟩
  have hs : ContDiff ℝ 2 (fun y => h (y,p)) := phase_position_slice_C2 h2 p
  have hcs := phase_position_slice_compact hh p
  have e := reference_density_eq_heatAverage F t ht (hheat t ht)
  have n₀ := gaussianAverage_norm_le_density hs.continuous hcs hp hB (fun y => b₀ (y,p)) (t-a) x
  have n₁ := gaussianAverage_norm_le_density (continuous_compactTest_fderiv hs)
    (hcs.fderiv ℝ) hp hB (fun y => by
      rw [phase_slice_fderiv (h2.of_le (by norm_num))]
      exact b₁ (y,p)) (t-a) x
  have n₂ := gaussianAverage_norm_le_density (continuous_compactTestLaplacian hs)
    (compactTestLaplacian_compactSupport hcs) hp hB (fun y => by
      have he : compactTestLaplacian (fun z => h (z,p)) y = Δ (y,p) := by
        simp only [compactTestLaplacian, phase_slice_hessian h2, Δ]
      rw [he]
      exact b₂ (y,p)) (t-a) x
  rw [← e] at n₀ n₁ n₂
  refine ⟨n₀, ?_, ?_⟩
  · change ‖fderiv ℝ (heatAverage (fun y => h (y,p)) (t-a)) x‖ ≤ _
    rw [heatAverage_fderiv hs hcs]
    exact n₁
  · change ‖compactTestLaplacian (heatAverage (fun y => h (y,p)) (t-a)) x‖ ≤ _
    rw [heatAverage_laplacian hs hcs]
    exact n₂

end AcceleratedLogConcave.Kinetic.Reheating
