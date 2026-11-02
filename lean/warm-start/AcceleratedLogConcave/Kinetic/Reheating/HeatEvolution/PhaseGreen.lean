import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.PhaseGrowth
import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.CoreL2

/-! Exact Green energy for the actual joint compact phase heat core. The scalar
closed-gradient identity is integrated over the retained Gaussian coordinate;
all product integrability follows from proved product-L2 bounds. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson Analysis.WeightedGradient
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Raw integral version of the scalar core's proved energy identity. -/
theorem compactHeatQuotient_green_integral {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
    (t : ℝ) (ht : t ∈ Icc a b) :
    (∫ x, ‖gradient (compactHeatQuotient F f t) x‖^2 ∂F.law t) =
      ∫ x, weightedHeatGenerator (F.potential t) (compactHeatQuotient F f t) x *
        compactHeatQuotient F f t x ∂F.law t := by
  let h := compactHeatQuotient_memLp F hf hc hheat t ht
  have he := compactHeatQuotient_green_energy F hf hc hheat t ht
  change ‖h.2.1.toLp _‖^2 = inner ℝ (h.2.2.toLp _) (h.1.toLp _) at he
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def] at he
  calc
    _ = ∫ x, inner ℝ (h.2.1.toLp _ x) (h.2.1.toLp _ x) ∂F.law t := by
      apply integral_congr_ae
      filter_upwards [h.2.1.coeFn_toLp] with x hx
      rw [hx, real_inner_self_eq_norm_sq]
    _ = _ := he
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [h.2.2.coeFn_toLp, h.1.coeFn_toLp] with x hx hy
      rw [hx, hy]
      simp only [RCLike.inner_apply, conj_trivial, mul_comm]

/-- Exact phase Green energy for arbitrary compact joint inputs. -/
theorem compactPhaseHeatQuotient_green_integral {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
    (t : ℝ) (ht : t ∈ Icc a b) :
    (∫ z, ‖compactPhaseHeatGradient F f t z‖^2 ∂(F.law t).prod (stdGaussian E)) =
      ∫ z, compactPhaseHeatGenerator F f t z * compactPhaseHeatQuotient F f t z
        ∂(F.law t).prod (stdGaussian E) := by
  have h := compactPhaseHeatQuotient_memLp F hf hc hheat t ht
  have hleft : Integrable (fun z => ‖compactPhaseHeatGradient F f t z‖^2)
      ((F.law t).prod (stdGaussian E)) := h.2.1.integrable_norm_pow (by norm_num)
  have hright : Integrable (fun z => compactPhaseHeatGenerator F f t z *
      compactPhaseHeatQuotient F f t z) ((F.law t).prod (stdGaussian E)) :=
    h.2.2.integrable_mul h.1
  rw [integral_prod_symm _ hleft, integral_prod_symm _ hright]
  apply integral_congr_ae
  filter_upwards [] with p
  exact compactHeatQuotient_green_integral F (phase_position_slice_C2 hf p)
    (phase_position_slice_compact hc p) hheat t ht

private theorem phase_tensor_memLp {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (μ : Measure E) [IsProbabilityMeasure μ] {u : E → K} (hu : MemLp u 2 μ)
    (r : Lp ℝ 2 (stdGaussian E)) : MemLp (fun z : E×E => r z.2 • u z.1) 2 (μ.prod (stdGaussian E)) := by
  have hm : AEStronglyMeasurable (fun z : E×E => r z.2 • u z.1) (μ.prod (stdGaussian E)) :=
    ((Lp.memLp r).comp_snd μ).aestronglyMeasurable.smul (hu.comp_fst (stdGaussian E)).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hh := (hu.integrable_norm_pow (by norm_num)).mul_prod (Lp.memLp r).integrable_sq
  apply hh.congr
  filter_upwards [] with z
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-- Tensor tests use a true Sobolev position function and an arbitrary Gaussian
L2 multiplier. This covers the position and momentum sectors of both correctors. -/
theorem compactPhaseHeatQuotient_green_tensor {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
    (t : ℝ) (ht : t ∈ Icc a b)
    (u : Sobolev (F.law t) (F.potential t) ((F.potential_C2 t).of_le (by norm_num))
      (F.integrable t ht) (F.gibbs_law t ht)) (r : Lp ℝ 2 (stdGaussian E)) :
    let Du := closedGradient (F.law t) (F.potential t) ((F.potential_C2 t).of_le (by norm_num))
      (F.integrable t ht) (F.gibbs_law t ht) u
    Integrable (fun z : E×E => inner ℝ (compactPhaseHeatGradient F f t z) (r z.2 • Du z.1))
      ((F.law t).prod (stdGaussian E)) ∧
    Integrable (fun z : E×E => compactPhaseHeatGenerator F f t z * (r z.2 * (u : Lp ℝ 2 (F.law t)) z.1))
      ((F.law t).prod (stdGaussian E)) ∧
    (∫ z : E×E, inner ℝ (compactPhaseHeatGradient F f t z) (r z.2 • Du z.1)
      ∂(F.law t).prod (stdGaussian E)) =
    ∫ z : E×E, compactPhaseHeatGenerator F f t z * (r z.2 * (u : Lp ℝ 2 (F.law t)) z.1)
      ∂(F.law t).prod (stdGaussian E) := by
  let Du := closedGradient (F.law t) (F.potential t) ((F.potential_C2 t).of_le (by norm_num))
    (F.integrable t ht) (F.gibbs_law t ht) u
  let uv : Lp ℝ 2 (F.law t) := u
  have h := compactPhaseHeatQuotient_memLp F hf hc hheat t ht
  have hT := phase_tensor_memLp (F.law t) (Lp.memLp Du) r
  have hU := phase_tensor_memLp (F.law t) (Lp.memLp uv) r
  have hleft : Integrable (fun z : E×E => inner ℝ (compactPhaseHeatGradient F f t z) (r z.2 • Du z.1))
      ((F.law t).prod (stdGaussian E)) := by
    apply (L2.integrable_inner (𝕜 := ℝ) (h.2.1.toLp _) (hT.toLp _)).congr
    filter_upwards [h.2.1.coeFn_toLp, hT.coeFn_toLp] with z hz hz'
    rw [hz, hz']
  have hright : Integrable (fun z : E×E => compactPhaseHeatGenerator F f t z * (r z.2 * uv z.1))
      ((F.law t).prod (stdGaussian E)) := h.2.2.integrable_mul hU
  refine ⟨hleft, hright, ?_⟩
  rw [integral_prod_symm _ hleft, integral_prod_symm _ hright]
  apply integral_congr_ae
  filter_upwards [] with p
  have hs := compactHeatQuotient_memLp F (phase_position_slice_C2 hf p) (phase_position_slice_compact hc p) hheat t ht
  have he := weighted_green_closedGradient (F.law t) (F.potential t)
    (compactHeatQuotient F (fun x => f (x,p)) t)
    ((F.potential_C2 t).of_le (by norm_num))
    (compactHeatQuotient_C2 F (phase_position_slice_C2 hf p) (phase_position_slice_compact hc p) t ht)
    (F.integrable t ht) (F.gibbs_law t ht) hs.2.1 hs.2.2 u
  have hi : (∫ x, inner ℝ (compactPhaseHeatGradient F f t (x,p)) (Du x) ∂F.law t) =
      ∫ x, compactPhaseHeatGenerator F f t (x,p) * uv x ∂F.law t := by
    rw [L2.inner_def, L2.inner_def] at he
    calc
      _ = ∫ x, inner ℝ (hs.2.1.toLp _ x) (Du x) ∂F.law t := by
        apply integral_congr_ae
        filter_upwards [hs.2.1.coeFn_toLp] with x hx
        rw [hx]
        rfl
      _ = _ := he
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hs.2.2.coeFn_toLp] with x hx
        rw [hx]
        simp only [RCLike.inner_apply, conj_trivial]
        change uv x * compactPhaseHeatGenerator F f t (x,p) = _
        ring
  calc
    _ = r p * ∫ x, inner ℝ (compactPhaseHeatGradient F f t (x,p)) (Du x) ∂F.law t := by
      simp only [inner_smul_right, integral_const_mul]
    _ = _ := congrArg (fun z => r p*z) hi
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      ring

end AcceleratedLogConcave.Kinetic.Reheating
