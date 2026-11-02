import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution
import AcceleratedLogConcave.Kinetic.ReferenceFlow.Score
import AcceleratedLogConcave.Kinetic.ReferenceFlow.Divergence
import AcceleratedLogConcave.Gibbs.Normalization

/-! The reference heat equation follows from the source's actual Gibbs law,
its classical continuity equation, and the heat velocity scale -1/2. In
particular, a second independent heat-PDE certificate is not required. -/
noncomputable section
open MeasureTheory InnerProductSpace Set
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson AcceleratedLogConcave.HeatCalculus
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The genuine divergence of the gradient is the coordinate Hessian trace. -/
theorem fluxDivergence_gradient {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x : E) :
    fluxDivergence (gradient f) x = compactTestLaplacian f x := by
  classical
  rw [fluxDivergence_eq_sum_basis (EuclideanSpace.basisFun ι ℝ)
    (gradient_hasFDerivAt_hessian hf x).differentiableAt,
    (gradient_hasFDerivAt_hessian hf x).fderiv]
  unfold compactTestLaplacian
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm, inner_hessianOperator]

theorem reference_density_C2 {a b : ℝ} (F : ReferencePoissonFamily E a b)
    (t : ℝ) (ht : t ∈ Icc a b) : ContDiff ℝ 2 (F.density t) := by
  have hc : Continuous (F.density t) := F.density_continuous.comp_continuous
    (continuous_const.prodMk continuous_id) (fun x => ⟨ht, mem_univ x⟩)
  rw [density_eq_normalized_gibbs (F.potential t) (F.density t)
    ((F.potential_C2 t).of_le (by norm_num)) hc (F.density_nonneg t ht)
    ((F.density_law t ht).symm.trans (F.gibbs_law t ht))]
  exact (F.potential_C2 t).neg.exp.div_const _

theorem reference_density_pos {a b : ℝ} (F : ReferencePoissonFamily E a b)
    (t : ℝ) (ht : t ∈ Icc a b) (x : E) : 0 < F.density t x := by
  have hc : Continuous (F.density t) := (reference_density_C2 F t ht).continuous
  rw [density_eq_normalized_gibbs (F.potential t) (F.density t)
    ((F.potential_C2 t).of_le (by norm_num)) hc (F.density_nonneg t ht)
    ((F.density_law t ht).symm.trans (F.gibbs_law t ht))]
  exact div_pos (Real.exp_pos _) (integral_exp_pos (F.integrable t ht))

/-- Strong convexity bounds the actual normalized density globally. -/
theorem reference_density_bounded {a b : ℝ} (F : ReferencePoissonFamily E a b)
    (t : ℝ) (ht : t ∈ Icc a b) : ∃ C : ℝ, ∀ x, ‖F.density t x‖ ≤ C := by
  let m := F.lower t
  let A := ‖fderiv ℝ (F.potential t) 0‖
  let Z := ∫ y, Real.exp (-F.potential t y)
  have hm : 0 < m := F.lower_pos t ht
  have hZ : 0 < Z := integral_exp_pos (F.integrable t ht)
  refine ⟨Real.exp (-F.potential t 0 + A^2/m) / Z, fun x => ?_⟩
  have hl := Gibbs.quadratic_lower_bound_of_hessian_lower (F.potential_C2 t)
    (F.hessian_lower t ht) x
  have hD : -A * ‖x‖ ≤ fderiv ℝ (F.potential t) 0 x := by
    have h := (fderiv ℝ (F.potential t) 0).le_opNorm x
    have hh := neg_le_abs (fderiv ℝ (F.potential t) 0 x)
    rw [← Real.norm_eq_abs] at hh
    dsimp [A]
    linarith
  have hs : 0 ≤ (m * ‖x‖ - A)^2 := sq_nonneg _
  have hAm : 0 ≤ A^2/m := div_nonneg (sq_nonneg A) hm.le
  have hmA : m * (A^2/m) = A^2 := mul_div_cancel₀ _ hm.ne'
  have hlo : F.potential t 0 - A^2/m ≤ F.potential t x := by
    dsimp [m] at hmA hs hAm hD ⊢
    nlinarith
  have he := density_eq_normalized_gibbs (F.potential t) (F.density t)
    ((F.potential_C2 t).of_le (by norm_num)) (reference_density_C2 F t ht).continuous
    (F.density_nonneg t ht) ((F.density_law t ht).symm.trans (F.gibbs_law t ht))
  rw [he, Real.norm_of_nonneg (div_nonneg (Real.exp_pos _).le hZ.le)]
  exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hZ.le

theorem reference_density_gradient {a b : ℝ} (F : ReferencePoissonFamily E a b)
    (t : ℝ) (ht : t ∈ Icc a b) (x : E) :
    gradient (F.density t) x = (-F.density t x) • gradient (F.potential t) x := by
  simp only [gradient, (reference_density_hasFDerivAt F t ht x).fderiv, map_smul]

/-- The heat reference flux is minus one half of its actual gradient. -/
theorem reference_heat_flux {a b : ℝ} (F : ReferencePoissonFamily E a b)
    (t : ℝ) (ht : t ∈ Icc a b) (hscale : F.scale t = -(1/2:ℝ)) :
    (fun x => F.density t x • referenceDrift F.potential F.scale t x) =
      fun x => -(1/2:ℝ) • gradient (F.density t) x := by
  funext x
  rw [reference_density_gradient F t ht x]
  simp [referenceDrift, hscale, smul_smul, mul_comm]

/-- The classical reference heat equation is derived, with the actual Hessian. -/
theorem reference_density_classical_heat {a b : ℝ} (F : ReferencePoissonFamily E a b)
    (t : ℝ) (ht : t ∈ Ioo a b) (hscale : F.scale t = -(1/2:ℝ)) (x : E) :
    HasDerivAt (fun s => F.density s x)
      ((1/2:ℝ) * compactTestLaplacian (F.density t) x) t := by
  have ht' := Ioo_subset_Icc_self ht
  have hp := reference_density_C2 F t ht'
  have hc := F.continuity_equation t ht x
  rw [reference_heat_flux F t ht' hscale] at hc
  rw [fluxDivergence_smul (differentiableAt_const _)
    (gradient_hasFDerivAt_hessian hp x).differentiableAt,
    fderiv_const_apply, zero_apply, zero_add,
    fluxDivergence_gradient hp] at hc
  convert F.density_hasDerivAt t ht x using 1
  linarith

end AcceleratedLogConcave.Kinetic.Reheating
