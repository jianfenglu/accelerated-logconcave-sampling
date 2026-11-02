import AcceleratedLogConcave.Analysis.Poisson.GradientRange
import Mathlib.Analysis.InnerProductSpace.Adjoint
import AcceleratedLogConcave.Analysis.Bochner

/-!
# Bounded gradient Poisson inverse and its adjoint

Both operators are built from the genuine closed-gradient variational problems.
Their adjoint relation follows by testing their full-domain weak equations
against each other's solutions.
-/

noncomputable section
open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace

namespace AcceleratedLogConcave.Analysis.Poisson

private theorem inner_centerForcing_of_mean_zero {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f g : Lp ℝ 2 μ) (hg : mean μ g = 0) :
    inner ℝ (centerForcing μ f) g = inner ℝ f g := by
  rw [centerForcing_apply, inner_sub_left, real_inner_smul_left]
  change inner ℝ f g - mean μ f * mean μ g = _
  rw [hg, mul_zero, sub_zero]

open WeightedGradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [IsProbabilityMeasure μ] (V : E → ℝ)
  (hV : ContDiff ℝ 2 V) (hI : Integrable (fun x => Real.exp (-V x)))
  (hμ : μ = volume.tilted (fun x => -V x))
  (m L : ℝ) (hm : 0 < m)
  (hlower : ∀ x a, m * ‖a‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x a a)
  (hupper : ∀ x a, fderiv ℝ (fderiv ℝ V) x a a ≤ L * ‖a‖ ^ 2)

theorem gradientPoissonSolution_norm_le (f : Lp ℝ 2 μ) :
    ‖closedGradient μ V (hV.of_le (by norm_num)) hI hμ
      (poissonSolution μ V hV hI hμ m L hm hlower hupper f)‖ ≤
        (Real.sqrt m)⁻¹ * ‖f‖ := by
  have hs := poissonSolution_spec (μ := μ) (V := V) (hV := hV) (hI := hI)
    (hμ := hμ) (m := m) (L := L) (hm := hm) (hlower := hlower) (hupper := hupper) f
  have he := (weak_poisson_estimates μ V hV hI hμ m L hm hlower hupper
    (centerForcing μ f) _ hs.1 hs.2).2.2
  have hc := norm_centerForcing_le μ f
  rw [← div_eq_inv_mul, le_div_iff₀ (Real.sqrt_pos.mpr hm)]
  apply (sq_le_sq₀ (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg m)) (norm_nonneg f)).mp
  rw [mul_pow, Real.sq_sqrt hm.le]
  nlinarith [norm_nonneg (centerForcing μ f)]

/-- The gradient of the actual scalar Poisson inverse as a bounded linear map. -/
def gradientPoissonInverse : Lp ℝ 2 μ →L[ℝ] Lp E 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun f => closedGradient μ V (hV.of_le (by norm_num)) hI hμ
        (poissonSolution μ V hV hI hμ m L hm hlower hupper f)
      map_add' := fun f g => by rw [poissonSolution_add, LinearPMap.map_add]
      map_smul' := fun c f => by rw [poissonSolution_smul, LinearPMap.map_smul]; rfl }
    (Real.sqrt m)⁻¹ (fun f => by
      change ‖closedGradient μ V (hV.of_le (by norm_num)) hI hμ
        (poissonSolution μ V hV hI hμ m L hm hlower hupper f)‖ ≤ _
      exact gradientPoissonSolution_norm_le μ V hV hI hμ m L hm hlower hupper f)

@[simp] theorem gradientPoissonInverse_apply (f : Lp ℝ 2 μ) :
    gradientPoissonInverse μ V hV hI hμ m L hm hlower hupper f =
      closedGradient μ V (hV.of_le (by norm_num)) hI hμ
        (poissonSolution μ V hV hI hμ m L hm hlower hupper f) := rfl

theorem gradientPoissonInverse_norm_le :
    ‖gradientPoissonInverse μ V hV hI hμ m L hm hlower hupper‖ ≤ (Real.sqrt m)⁻¹ :=
  LinearMap.mkContinuous_norm_le _ (inv_nonneg.mpr (Real.sqrt_nonneg m)) _

/-- The vector variational inverse is the adjoint of the scalar gradient inverse. -/
theorem vectorPoissonInverse_adjoint :
    (vectorPoissonInverse μ V hV hI hμ m L hm hlower hupper).adjoint =
      gradientPoissonInverse μ V hV hI hμ m L hm hlower hupper := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f w
  let u := poissonSolution μ V hV hI hμ m L hm hlower hupper f
  let z := vectorPoissonSolution μ V hV hI hμ m L hm hlower hupper w
  let D := closedGradient μ V (hV.of_le (by norm_num)) hI hμ
  have hu := poissonSolution_spec (μ := μ) (V := V) (hV := hV) (hI := hI)
    (hμ := hμ) (m := m) (L := L) (hm := hm) (hlower := hlower) (hupper := hupper) f
  have hz := vectorPoissonSolution_spec (μ := μ) (V := V) (hV := hV) (hI := hI)
    (hμ := hμ) (m := m) (L := L) (hm := hm) (hlower := hlower) (hupper := hupper) w
  change inner ℝ (D u) w = inner ℝ f (z : Lp ℝ 2 μ)
  calc
    _ = inner ℝ w (D u) := real_inner_comm _ _
    _ = inner ℝ (D z) (D u) := (hz.2 u).symm
    _ = inner ℝ (D u) (D z) := real_inner_comm _ _
    _ = inner ℝ (centerForcing μ f) (z : Lp ℝ 2 μ) := hu.2 z
    _ = _ := inner_centerForcing_of_mean_zero μ f z ((mean_apply μ z).trans hz.1)

/-- The centered scalar Poisson inverse is self-adjoint on the full scalar L2 space. -/
theorem poissonInverse_adjoint :
    (poissonInverse μ V hV hI hμ m L hm hlower hupper).adjoint =
      poissonInverse μ V hV hI hμ m L hm hlower hupper := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  let u := poissonSolution μ V hV hI hμ m L hm hlower hupper f
  let z := poissonSolution μ V hV hI hμ m L hm hlower hupper g
  let D := closedGradient μ V (hV.of_le (by norm_num)) hI hμ
  have hu := poissonSolution_spec (μ := μ) (V := V) (hV := hV) (hI := hI)
    (hμ := hμ) (m := m) (L := L) (hm := hm) (hlower := hlower) (hupper := hupper) f
  have hz := poissonSolution_spec (μ := μ) (V := V) (hV := hV) (hI := hI)
    (hμ := hμ) (m := m) (L := L) (hm := hm) (hlower := hlower) (hupper := hupper) g
  change inner ℝ (u : Lp ℝ 2 μ) g = inner ℝ f (z : Lp ℝ 2 μ)
  calc
    _ = inner ℝ g (u : Lp ℝ 2 μ) := real_inner_comm _ _
    _ = inner ℝ (centerForcing μ g) (u : Lp ℝ 2 μ) :=
      (inner_centerForcing_of_mean_zero μ g u ((mean_apply μ u).trans hu.1)).symm
    _ = inner ℝ (D z) (D u) := (hz.2 u).symm
    _ = inner ℝ (D u) (D z) := real_inner_comm _ _
    _ = inner ℝ (centerForcing μ f) (z : Lp ℝ 2 μ) := hu.2 z
    _ = _ := inner_centerForcing_of_mean_zero μ f z ((mean_apply μ z).trans hz.1)


/-- The reverse adjoint identity for the two genuine inverse-gradient maps. -/
theorem gradientPoissonInverse_adjoint :
    (gradientPoissonInverse μ V hV hI hμ m L hm hlower hupper).adjoint =
      vectorPoissonInverse μ V hV hI hμ m L hm hlower hupper := by
  rw [← vectorPoissonInverse_adjoint, ContinuousLinearMap.adjoint_adjoint]

/-- Bochner yields the sharp curvature-composed gradient bound, with no spectral-gap factor. -/
theorem hessianMultiplier_comp_gradientPoissonInverse_norm_le
    (hupper_one : ∀ x a, fderiv ℝ (fderiv ℝ V) x a a ≤ 1 * ‖a‖ ^ 2) :
    ‖(hessianMultiplier μ V hV m 1 hlower hupper_one).comp
      (gradientPoissonInverse μ V hV hI hμ m 1 hm hlower hupper_one)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  have hs := poissonSolution_spec (μ := μ) (V := V) (hV := hV) (hI := hI)
    (hμ := hμ) (m := m) (L := 1) (hm := hm) (hlower := hlower) (hupper := hupper_one) f
  have hb := weak_poisson_hessianGradient_norm_le μ V hV hI hμ m hm hlower hupper_one
    (poissonSolution μ V hV hI hμ m 1 hm hlower hupper_one f) (centerForcing μ f) hs.2
  change ‖hessianMultiplier μ V hV m 1 hlower hupper_one
    (closedGradient μ V (hV.of_le (by norm_num)) hI hμ
      (poissonSolution μ V hV hI hμ m 1 hm hlower hupper_one f))‖ ≤ 1 * ‖f‖
  simpa only [one_mul] using hb.trans (norm_centerForcing_le μ f)

/-- The adjoint curvature-composed vector inverse satisfies the same sharp bound. -/
theorem vectorPoissonInverse_comp_hessianMultiplier_norm_le
    (hupper_one : ∀ x a, fderiv ℝ (fderiv ℝ V) x a a ≤ 1 * ‖a‖ ^ 2) :
    ‖(vectorPoissonInverse μ V hV hI hμ m 1 hm hlower hupper_one).comp
      (hessianMultiplier μ V hV m 1 hlower hupper_one)‖ ≤ 1 := by
  calc
    _ = ‖((vectorPoissonInverse μ V hV hI hμ m 1 hm hlower hupper_one).comp
        (hessianMultiplier μ V hV m 1 hlower hupper_one)).adjoint‖ :=
      (ContinuousLinearMap.adjoint.norm_map _).symm
    _ = ‖(hessianMultiplier μ V hV m 1 hlower hupper_one).comp
        (gradientPoissonInverse μ V hV hI hμ m 1 hm hlower hupper_one)‖ := by
      rw [ContinuousLinearMap.adjoint_comp, vectorPoissonInverse_adjoint,
        (hessianMultiplier_symmetric μ V hV m 1 hlower hupper_one).clm_adjoint_eq]
    _ ≤ 1 := hessianMultiplier_comp_gradientPoissonInverse_norm_le
      μ V hV hI hμ m hm hlower hupper_one

end AcceleratedLogConcave.Analysis.Poisson
