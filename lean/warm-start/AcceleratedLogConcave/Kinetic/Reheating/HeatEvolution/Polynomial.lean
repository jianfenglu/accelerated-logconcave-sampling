import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.DerivativeBounds
import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.Green

/-! Polynomial bounds and genuine Gibbs integrability for the smooth heat core. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson AcceleratedLogConcave.HeatCalculus
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem reference_density_laplacian {a b : ℝ} (F : ReferencePoissonFamily E a b)
    (t : ℝ) (ht : t ∈ Icc a b) (x : E) :
    compactTestLaplacian (F.density t) x = F.density t x *
      (‖gradient (F.potential t) x‖^2 - compactTestLaplacian (F.potential t) x) := by
  have hp := reference_density_C2 F t ht
  rw [← fluxDivergence_gradient hp]
  have he : gradient (F.density t) =
      fun y => (-F.density t y) • gradient (F.potential t) y :=
    funext (reference_density_gradient F t ht)
  rw [he, fluxDivergence_smul (r := fun y => -F.density t y) (hp.differentiable (by norm_num) x).neg
    (gradient_hasFDerivAt_hessian (F.potential_C2 t) x).differentiableAt,
    (show HasFDerivAt (fun y => -F.density t y)
      (-(-F.density t x • fderiv ℝ (F.potential t) x)) x from
      (reference_density_hasFDerivAt F t ht x).neg).fderiv,
    fluxDivergence_gradient (F.potential_C2 t)]
  simp only [neg_apply, smul_apply, smul_eq_mul]
  rw [← inner_gradient_left, real_inner_self_eq_norm_sq]
  ring

theorem reference_laplacian_bounds {a b : ℝ} (F : ReferencePoissonFamily E a b)
    (t : ℝ) (ht : t ∈ Icc a b) (x : E) :
    0 ≤ compactTestLaplacian (F.potential t) x ∧
      compactTestLaplacian (F.potential t) x ≤ Fintype.card ι := by
  classical
  constructor
  · exact Finset.sum_nonneg fun i _ => F.hessian_nonneg t ht x _
  · calc
      _ ≤ ∑ i : ι, (1:ℝ) := Finset.sum_le_sum fun i _ => by
        simpa using F.hessian_upper t ht x (EuclideanSpace.basisFun ι ℝ i)
      _ = _ := by simp

theorem reference_gradient_linear_bound {a b : ℝ} (F : ReferencePoissonFamily E a b) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc a b, ∀ x,
      ‖gradient (F.potential t) x‖ ≤ B + ‖x‖ := by
  have hc : Continuous (fun t => gradient (F.potential t) (0:E)) :=
    F.gradient_continuous.comp (continuous_id.prodMk continuous_const)
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun t ht x => ?_⟩
  have hL := (gradient_lipschitz_of_unit_hessian (F.potential_C2 t)
    (F.hessian_nonneg t ht) (F.hessian_upper t ht)).dist_le_mul x 0
  simp only [NNReal.coe_one, one_mul, dist_eq_norm, sub_zero] at hL
  calc
    _ ≤ ‖gradient (F.potential t) 0‖ + ‖gradient (F.potential t) x -
      gradient (F.potential t) 0‖ := by
      simpa [add_comm] using norm_le_insert' (gradient (F.potential t) x) (gradient (F.potential t) 0)
    _ ≤ B + ‖x‖ := add_le_add (hB t ht) hL
    _ ≤ max B 0 + ‖x‖ := by gcongr; exact le_max_left _ _

theorem reference_integrable_norm_pow {a b : ℝ} (F : ReferencePoissonFamily E a b)
    (t : ℝ) (ht : t ∈ Icc a b) (n : ℕ) :
    Integrable (fun x : E => ‖x‖^n) (F.law t) := by
  rw [F.gibbs_law t ht, integrable_tilted_iff (F.integrable t ht)]
  simpa only [smul_eq_mul, mul_comm] using
    Gibbs.integrable_norm_pow_mul_exp_neg_of_hessian_lower (F.potential_C2 t)
      (F.lower_pos t ht) (F.hessian_lower t ht) n

theorem reference_memLp_norm_pow {a b : ℝ} (F : ReferencePoissonFamily E a b)
    (t : ℝ) (ht : t ∈ Icc a b) (n : ℕ) :
    MemLp (fun x : E => ‖x‖^n) 2 (F.law t) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  simpa only [← pow_mul] using reference_integrable_norm_pow F t ht (n*2)

/-- Every continuous function with quadratic growth belongs to the actual
moving Gibbs L2 space; the moment bound is derived from strong convexity. -/
theorem reference_memLp_of_quadratic_bound {K : Type*} [NormedAddCommGroup K]
    [NormedSpace ℝ K] {a b : ℝ} (F : ReferencePoissonFamily E a b)
    (t : ℝ) (ht : t ∈ Icc a b) {h : E → K} (hh : Continuous h)
    (C : ℝ) (hC : ∀ x, ‖h x‖ ≤ C*(1+‖x‖^2)) : MemLp h 2 (F.law t) := by
  have hm := ((memLp_const (1:ℝ) (μ := F.law t) (p := 2)).add
    (reference_memLp_norm_pow F t ht 2)).const_mul C
  apply hm.mono hh.aestronglyMeasurable
  filter_upwards [] with x
  exact (hC x).trans (le_abs_self _)

end AcceleratedLogConcave.Kinetic.Reheating
