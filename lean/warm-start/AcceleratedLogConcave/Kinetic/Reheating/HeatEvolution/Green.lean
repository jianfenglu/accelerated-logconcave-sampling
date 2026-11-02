import AcceleratedLogConcave.Analysis.WeightedGradient.Basic
import AcceleratedLogConcave.External.HeatCalculus.CompactTest

/-! Actual weighted Green identity for C2 functions with L2 value, gradient and
weighted Laplacian. Compact integration by parts is extended along the actual
closed gradient graph. No Hessian-row integrability or Green identity is assumed.
The local scalar calculation follows the C1 compact directional calculation in
Samplinglib's `WeightedGradientWeak` (retained under External/Samplinglib). -/
noncomputable section
open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace Topology
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.WeightedGradient

private theorem weighted_compact_directional
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) (V f φ : E → ℝ) (hV : ContDiff ℝ 1 V)
    (hf : ContDiff ℝ 1 f) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hμ : μ = volume.tilted (fun x => -V x)) (v : E) :
    (∫ x, f x * fderiv ℝ φ x v ∂μ) =
      ∫ x, (f x * fderiv ℝ V x v - fderiv ℝ f x v) * φ x ∂μ := by
  let F := fun x => Real.exp (-V x) * φ x
  have hF : ContDiff ℝ 1 F := hV.neg.exp.mul hφ
  have hFc : HasCompactSupport F := hc.mul_left
  have hDF := (hF.continuous_fderiv one_ne_zero).clm_apply (continuous_const (y := v))
  have hDf := (hf.continuous_fderiv one_ne_zero).clm_apply (continuous_const (y := v))
  have h1 : Integrable (fun x => fderiv ℝ F x v * f x) :=
    (hDF.mul hf.continuous).integrable_of_hasCompactSupport (hFc.fderiv_apply ℝ v).mul_right
  have h2 : Integrable (fun x => F x * fderiv ℝ f x v) :=
    (hF.continuous.mul hDf).integrable_of_hasCompactSupport hFc.mul_right
  have h3 : Integrable (fun x => F x * f x) :=
    (hF.continuous.mul hf.continuous).integrable_of_hasCompactSupport hFc.mul_right
  have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3
    (fun x _ => hF.differentiable_one x) (fun x _ => hf.differentiable_one x)
  have hd (x) : fderiv ℝ F x v = Real.exp (-V x) *
      (fderiv ℝ φ x v - φ x * fderiv ℝ V x v) := by
    have hd := ((hV.differentiable_one x).hasFDerivAt.neg.exp).mul
      (hφ.differentiable_one x).hasFDerivAt
    rw [show fderiv ℝ F x = _ from hd.fderiv]
    simp only [add_apply, smul_apply, neg_apply, smul_eq_mul, Pi.neg_apply]
    ring
  have ha : Integrable (fun x => Real.exp (-V x) * f x * fderiv ℝ φ x v) :=
    ((hV.neg.exp.continuous.mul hf.continuous).mul
      ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const)).integrable_of_hasCompactSupport
        (hc.fderiv_apply ℝ v).mul_left
  have hb : Integrable (fun x => Real.exp (-V x) *
      (f x * fderiv ℝ V x v - fderiv ℝ f x v) * φ x) := by
    apply Continuous.integrable_of_hasCompactSupport _ hc.mul_left
    exact ((hV.neg.exp.continuous.mul ((hf.continuous.mul
      ((hV.continuous_fderiv one_ne_zero).clm_apply continuous_const)).sub hDf)).mul hφ.continuous)
  have he : (∫ x, Real.exp (-V x) * f x * fderiv ℝ φ x v) =
      ∫ x, Real.exp (-V x) * (f x * fderiv ℝ V x v - fderiv ℝ f x v) * φ x := by
    have hz : (∫ x, Real.exp (-V x) * f x * fderiv ℝ φ x v -
        Real.exp (-V x) * (f x * fderiv ℝ V x v - fderiv ℝ f x v) * φ x) = 0 := by
      calc
        _ = ∫ x, fderiv ℝ F x v * f x + F x * fderiv ℝ f x v := by
          apply integral_congr_ae
          filter_upwards [] with x
          rw [hd]
          dsimp [F]
          ring
        _ = 0 := by rw [integral_add h1 h2]; linarith
    rw [integral_sub ha hb] at hz
    linarith
  have ht (g : E → ℝ) : (∫ x, g x ∂μ) =
      (∫ x, Real.exp (-V x))⁻¹ * ∫ x, Real.exp (-V x) * g x := by
    rw [hμ, integral_tilted, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    change (Real.exp (-V x) / (∫ z, Real.exp (-V z))) • g x = _
    simp only [smul_eq_mul, div_eq_mul_inv]
    ring
  rw [ht, ht]
  congr 1
  simpa only [mul_assoc] using he

variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The literal negative weighted Laplacian, with the source coordinate trace. -/
def weightedHeatGenerator (V q : E → ℝ) (x : E) : ℝ :=
  -AcceleratedLogConcave.HeatCalculus.compactTestLaplacian q x + inner ℝ (gradient V x) (gradient q x)

/-- Compact tests require no global integrability of the Hessian or score product. -/
theorem weighted_green_compact (μ : Measure E) [IsFiniteMeasure μ]
    (V q : E → ℝ) (hV : ContDiff ℝ 1 V) (hq : ContDiff ℝ 2 q)
    (hμ : μ = volume.tilted (fun x => -V x))
    (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    (∫ x, inner ℝ (gradient q x) (gradient φ x) ∂μ) =
      ∫ x, weightedHeatGenerator V q x * φ x ∂μ := by
  let e := EuclideanSpace.basisFun ι ℝ
  let d := fun i x => fderiv ℝ q x (e i)
  have hd (i) : ContDiff ℝ 1 (d i) :=
    (hq.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hdd (i) (x) : fderiv ℝ (d i) x (e i) =
      fderiv ℝ (fderiv ℝ q) x (e i) (e i) := by
    simpa only [ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply] using congrArg (fun T => T (e i))
      (((hq.fderiv_right (m := 1) (by norm_num)).differentiable_one x).hasFDerivAt.clm_apply
        (hasFDerivAt_const (e i) x)).fderiv
  have hg (f : E → ℝ) (hf : Differentiable ℝ f) (x v : E) :
      fderiv ℝ f x v = inner ℝ (gradient f x) v :=
    AutoSamplingTheory.TechnicalLemmas.Analysis.Calculus.Gradient.fderiv_apply_eq_inner_gradient_of_differentiableAt (hf x)
  have hleft (i) : Integrable (fun x => d i x * fderiv ℝ φ x (e i)) μ :=
    ((hd i).continuous.mul ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ (e i)).mul_left
  have hright (i) : Integrable (fun x =>
      (d i x * fderiv ℝ V x (e i) - fderiv ℝ (d i) x (e i)) * φ x) μ := by
    apply Continuous.integrable_of_hasCompactSupport _ hc.mul_left
    exact (((hd i).continuous.mul ((hV.continuous_fderiv one_ne_zero).clm_apply continuous_const)).sub
      (((hd i).continuous_fderiv one_ne_zero).clm_apply continuous_const)).mul hφ.continuous
  have hle (x) : (∑ i, d i x * fderiv ℝ φ x (e i)) =
      inner ℝ (gradient q x) (gradient φ x) := by
    simp only [d, hg q (hq.differentiable (by norm_num)), hg φ hφ.differentiable_one]
    simpa only [real_inner_comm] using e.sum_inner_mul_inner (gradient q x) (gradient φ x)
  have hre (x) : (∑ i, (d i x * fderiv ℝ V x (e i) -
      fderiv ℝ (d i) x (e i)) * φ x) = weightedHeatGenerator V q x * φ x := by
    simp only [← Finset.sum_mul, Finset.sum_sub_distrib, hdd, weightedHeatGenerator,
      AcceleratedLogConcave.HeatCalculus.compactTestLaplacian]
    have hs : (∑ i, d i x * fderiv ℝ V x (e i)) =
        inner ℝ (gradient V x) (gradient q x) := by
      simp only [d, hg q (hq.differentiable (by norm_num)), hg V hV.differentiable_one]
      simpa only [real_inner_comm] using e.sum_inner_mul_inner (gradient q x) (gradient V x)
    rw [hs]
    ring
  calc
    _ = ∫ x, ∑ i, d i x * fderiv ℝ φ x (e i) ∂μ := by simp_rw [hle]
    _ = ∑ i, ∫ x, d i x * fderiv ℝ φ x (e i) ∂μ := integral_finsetSum _ (fun i _ => hleft i)
    _ = ∑ i, ∫ x, (d i x * fderiv ℝ V x (e i) - fderiv ℝ (d i) x (e i)) * φ x ∂μ :=
      Finset.sum_congr rfl fun i _ => weighted_compact_directional μ V (d i) φ hV (hd i) hφ hc hμ (e i)
    _ = ∫ x, ∑ i, (d i x * fderiv ℝ V x (e i) - fderiv ℝ (d i) x (e i)) * φ x ∂μ :=
      (integral_finsetSum _ (fun i _ => hright i)).symm
    _ = _ := by simp_rw [hre]

private theorem graph_closure_pairing {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (D : H →ₗ.[ℝ] K) (g : K) (k : H)
    (hb : ∀ p ∈ D.graph, inner ℝ g p.2 = inner ℝ k p.1)
    {p : H×K} (hp : p ∈ D.graph.topologicalClosure) :
    inner ℝ g p.2 = inner ℝ k p.1 := by
  have hc : IsClosed {p : H×K | inner ℝ g p.2 = inner ℝ k p.1} :=
    isClosed_eq (continuous_const.inner continuous_snd) (continuous_const.inner continuous_fst)
  exact hc.closure_subset_iff.mpr hb hp

/-- The global Green identity on the actual closed-gradient domain. Its only
integrability inputs are the genuine gradient and weighted Laplacian in L2. -/
theorem weighted_green_closedGradient (μ : Measure E)
    (V q : E → ℝ) (hV : ContDiff ℝ 1 V) (hq : ContDiff ℝ 2 q)
    (hI : Integrable (fun x => Real.exp (-V x)))
    (hμ : μ = volume.tilted (fun x => -V x))
    (hgrad : MemLp (gradient q) 2 μ) (hgen : MemLp (weightedHeatGenerator V q) 2 μ)
    (u : Sobolev μ V hV hI hμ) :
    inner ℝ (hgrad.toLp (gradient q)) (closedGradient μ V hV hI hμ u) =
      inner ℝ (hgen.toLp (weightedHeatGenerator V q)) (u : Lp ℝ 2 μ) := by
  have : IsProbabilityMeasure μ := hμ ▸ isProbabilityMeasure_tilted hI
  have hu := (closedGradient μ V hV hI hμ).mem_graph u
  rw [closedGradient_graph_eq] at hu
  apply graph_closure_pairing (compactGradient μ V hV hI hμ)
    (hgrad.toLp (gradient q)) (hgen.toLp (weightedHeatGenerator V q)) ?_ hu
  rintro ⟨f,G⟩ hfg
  obtain ⟨φ,hφ,hc,hf,hG⟩ := (mem_compactGradient_graph μ V hV hI hμ f G).mp hfg
  change inner ℝ (hgrad.toLp (gradient q)) G = inner ℝ (hgen.toLp (weightedHeatGenerator V q)) f
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ x, inner ℝ (gradient q x) (gradient φ x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hgrad.coeFn_toLp, hG] with x hx hy
      rw [hx, hy]
    _ = ∫ x, weightedHeatGenerator V q x * φ x ∂μ :=
      weighted_green_compact μ V q hV hq hμ φ (hφ.of_le (by norm_num)) hc
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hgen.coeFn_toLp, hf] with x hx hy
      rw [hx, hy]
      simp only [RCLike.inner_apply, conj_trivial]
      ring

/-- Taking the actual C1 graph member q as test yields its true energy identity. -/
theorem weighted_green_energy (μ : Measure E)
    (V q : E → ℝ) (hV : ContDiff ℝ 1 V) (hq : ContDiff ℝ 2 q)
    (hI : Integrable (fun x => Real.exp (-V x)))
    (hμ : μ = volume.tilted (fun x => -V x))
    (hval : MemLp q 2 μ) (hgrad : MemLp (gradient q) 2 μ)
    (hgen : MemLp (weightedHeatGenerator V q) 2 μ) :
    ‖hgrad.toLp (gradient q)‖^2 =
      inner ℝ (hgen.toLp (weightedHeatGenerator V q)) (hval.toLp q) := by
  have hg := c1_mem_closedGradient_graph μ V hV hI hμ (hq.of_le (by norm_num)) hval hgrad
  obtain ⟨u, hu, hDu⟩ := (LinearPMap.mem_graph_iff _).mp hg
  have he := weighted_green_closedGradient μ V q hV hq hI hμ hgrad hgen u
  rw [hu, hDu, real_inner_self_eq_norm_sq] at he
  exact he

end AcceleratedLogConcave.Kinetic.Reheating
