import AcceleratedLogConcave.External.Samplinglib.TechnicalLemmas.Analysis.HessianSecantOperator
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The actual Hessian as a bounded weighted L2 multiplier

Two quadratic Hessian bounds give a bounded multiplication operator on vector
L2. Its quadratic form is the actual integral of the Hessian, and is continuous.
For a positive Hessian bounded by the identity, its squared action is bounded
by that quadratic form. No score moments or derivatives above order two enter.
-/

noncomputable section
open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace

namespace AcceleratedLogConcave.Analysis.Poisson

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Riesz realization of the genuine second Frechet derivative. -/
def hessianOperator (V : E → ℝ) (x : E) : E →L[ℝ] E :=
  continuousLinearMapOfBilin (fderiv ℝ (fderiv ℝ V) x)

theorem inner_hessianOperator (V : E → ℝ) (x v w : E) :
    inner ℝ (hessianOperator V x v) w = fderiv ℝ (fderiv ℝ V) x v w :=
  continuousLinearMapOfBilin_apply _ _ _

theorem continuous_hessianOperator {V : E → ℝ} (hV : ContDiff ℝ 2 V) :
    Continuous (hessianOperator V) := by
  have hfd : ContDiff ℝ 1 (fderiv ℝ V) := hV.fderiv_right (by norm_num)
  unfold hessianOperator continuousLinearMapOfBilin
  exact continuous_const.clm_comp (hfd.continuous_fderiv one_ne_zero)

theorem hessianOperator_symmetric {V : E → ℝ} (hV : ContDiff ℝ 2 V) (x : E) :
    (hessianOperator V x).IsSymmetric := by
  intro v w
  change inner ℝ (hessianOperator V x v) w = inner ℝ v (hessianOperator V x w)
  rw [inner_hessianOperator, real_inner_comm (hessianOperator V x w) v, inner_hessianOperator]
  exact hV.contDiffAt.isSymmSndFDerivAt (by norm_num) v w

omit [FiniteDimensional ℝ E] in
private theorem symmetric_operator_norm_le (T : E →L[ℝ] E) (hs : T.IsSymmetric)
    (m L : ℝ) (hlo : ∀ v, m * ‖v‖ ^ 2 ≤ inner ℝ (T v) v)
    (hup : ∀ v, inner ℝ (T v) v ≤ L * ‖v‖ ^ 2) :
    ‖T‖ ≤ max |m| |L| := by
  rw [T.norm_eq_iSup_rayleighQuotient hs]
  apply ciSup_le
  intro v
  change |inner ℝ (T v) v / ‖v‖ ^ 2| ≤ max |m| |L|
  by_cases hv : v = 0
  · simp [hv]
  · simp only [abs_div, abs_pow, abs_norm]
    apply (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hv))).mpr
    have hl := mul_le_mul_of_nonneg_right
      ((neg_le_abs m).trans (le_max_left |m| |L|)) (sq_nonneg ‖v‖)
    have hu := mul_le_mul_of_nonneg_right
      ((le_abs_self L).trans (le_max_right |m| |L|)) (sq_nonneg ‖v‖)
    exact abs_le.mpr ⟨by nlinarith [hlo v], by nlinarith [hup v]⟩

theorem hessianOperator_norm_le {V : E → ℝ} (hV : ContDiff ℝ 2 V) {m L : ℝ}
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hup : ∀ x v, fderiv ℝ (fderiv ℝ V) x v v ≤ L * ‖v‖ ^ 2) (x : E) :
    ‖hessianOperator V x‖ ≤ max |m| |L| :=
  symmetric_operator_norm_le _ (hessianOperator_symmetric hV x) m L
    (fun v => (inner_hessianOperator V x v v).symm ▸ hlo x v)
    (fun v => (inner_hessianOperator V x v v).symm ▸ hup x v)

variable [MeasurableSpace E] [BorelSpace E]

section Multiplier

variable (μ : Measure E) (V : E → ℝ) (hV : ContDiff ℝ 2 V) (m L : ℝ)
  (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
  (hup : ∀ x v, fderiv ℝ (fderiv ℝ V) x v v ≤ L * ‖v‖ ^ 2)

include hV hlo hup

private theorem hessian_action_memLp (G : Lp E 2 μ) :
    MemLp (fun x => hessianOperator V x (G x)) 2 μ := by
  apply (Lp.memLp G).of_le_mul
    ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      ((continuous_hessianOperator hV).aestronglyMeasurable.prodMk (Lp.aestronglyMeasurable G)))
  exact Filter.Eventually.of_forall fun x =>
    ((hessianOperator V x).le_opNorm (G x)).trans
      (mul_le_mul_of_nonneg_right (hessianOperator_norm_le hV hlo hup x) (norm_nonneg _))

private def hessianAction (G : Lp E 2 μ) : Lp E 2 μ :=
  (hessian_action_memLp μ V hV m L hlo hup G).toLp _

private theorem hessianAction_coe (G : Lp E 2 μ) :
    hessianAction μ V hV m L hlo hup G =ᵐ[μ] fun x => hessianOperator V x (G x) :=
  (hessian_action_memLp μ V hV m L hlo hup G).coeFn_toLp

private theorem hessianAction_norm_le (G : Lp E 2 μ) :
    ‖hessianAction μ V hV m L hlo hup G‖ ≤ max |m| |L| * ‖G‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hessianAction_coe μ V hV m L hlo hup G] with x hx
  rw [hx]
  exact ((hessianOperator V x).le_opNorm (G x)).trans
    (mul_le_mul_of_nonneg_right (hessianOperator_norm_le hV hlo hup x) (norm_nonneg _))

/-- Multiplication by the actual Hessian on vector-valued weighted L2. -/
def hessianMultiplier : Lp E 2 μ →L[ℝ] Lp E 2 μ :=
  LinearMap.mkContinuous
    { toFun := hessianAction μ V hV m L hlo hup
      map_add' := by
        intro G F
        apply Lp.ext
        filter_upwards [hessianAction_coe μ V hV m L hlo hup (G + F),
          hessianAction_coe μ V hV m L hlo hup G,
          hessianAction_coe μ V hV m L hlo hup F,
          Lp.coeFn_add G F,
          Lp.coeFn_add (hessianAction μ V hV m L hlo hup G)
            (hessianAction μ V hV m L hlo hup F)] with x hGF hG hF ha hb
        simp only [hGF, ha, hb, Pi.add_apply, hG, hF, map_add]
      map_smul' := by
        intro c G
        apply Lp.ext
        filter_upwards [hessianAction_coe μ V hV m L hlo hup (c • G),
          hessianAction_coe μ V hV m L hlo hup G,
          Lp.coeFn_smul c G,
          Lp.coeFn_smul c (hessianAction μ V hV m L hlo hup G)] with x hcG hG ha hb
        simp only [RingHom.id_apply, hcG, ha, hb, Pi.smul_apply, hG, map_smul] }
    (max |m| |L|) (hessianAction_norm_le μ V hV m L hlo hup)

theorem hessianMultiplier_coe (G : Lp E 2 μ) :
    hessianMultiplier μ V hV m L hlo hup G =ᵐ[μ]
      fun x => hessianOperator V x (G x) :=
  hessianAction_coe μ V hV m L hlo hup G

theorem hessianMultiplier_norm_le :
    ‖hessianMultiplier μ V hV m L hlo hup‖ ≤ max |m| |L| :=
  LinearMap.mkContinuous_norm_le _ (le_trans (abs_nonneg m) (le_max_left _ _)) _

/-- The L2 quadratic form is exactly the genuine Hessian curvature integral. -/
theorem inner_hessianMultiplier (G F : Lp E 2 μ) :
    inner ℝ (hessianMultiplier μ V hV m L hlo hup G) F =
      ∫ x, fderiv ℝ (fderiv ℝ V) x (G x) (F x) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hessianMultiplier_coe μ V hV m L hlo hup G] with x hx
  rw [hx, inner_hessianOperator]

theorem integrable_hessian_pairing (G F : Lp E 2 μ) :
    Integrable (fun x => fderiv ℝ (fderiv ℝ V) x (G x) (F x)) μ := by
  apply (L2.integrable_inner (hessianMultiplier μ V hV m L hlo hup G) F).congr
  filter_upwards [hessianMultiplier_coe μ V hV m L hlo hup G] with x hx
  rw [hx, inner_hessianOperator]

theorem hessianMultiplier_symmetric : (hessianMultiplier μ V hV m L hlo hup).IsSymmetric := by
  intro G F
  change inner ℝ (hessianMultiplier μ V hV m L hlo hup G) F =
    inner ℝ G (hessianMultiplier μ V hV m L hlo hup F)
  rw [inner_hessianMultiplier, real_inner_comm (hessianMultiplier μ V hV m L hlo hup F) G, inner_hessianMultiplier]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    hV.contDiffAt.isSymmSndFDerivAt (by norm_num) (G x) (F x)

/-- Curvature energy is a continuous quadratic form on the actual vector L2 space. -/
theorem continuous_curvatureForm :
    Continuous (fun G : Lp E 2 μ =>
      ∫ x, fderiv ℝ (fderiv ℝ V) x (G x) (G x) ∂μ) := by
  simp_rw [← inner_hessianMultiplier μ V hV m L hlo hup]
  exact (hessianMultiplier μ V hV m L hlo hup).continuous.inner continuous_id

end Multiplier

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem symmetric_contraction_sq_le (T : E →L[ℝ] E) (hs : T.IsSymmetric)
    (hlo : ∀ v, 0 ≤ inner ℝ (T v) v)
    (hup : ∀ v, inner ℝ (T v) v ≤ ‖v‖ ^ 2) (v : E) :
    ‖T v‖ ^ 2 ≤ inner ℝ (T v) v := by
  let B : E →L[ℝ] E := (2 : ℝ) • T - ContinuousLinearMap.id ℝ E
  have hBs : B.IsSymmetric := by
    intro a b
    change inner ℝ ((2 : ℝ) • T a - a) b = inner ℝ a ((2 : ℝ) • T b - b)
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    have hsab : inner ℝ (T a) b = inner ℝ a (T b) := hs a b
    rw [hsab]
  have hBn : ‖B‖ ≤ 1 := by
    have h := symmetric_operator_norm_le B hBs (-1) 1
      (fun w => by
        change -1 * ‖w‖ ^ 2 ≤ inner ℝ ((2 : ℝ) • T w - w) w
        rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
        nlinarith [hlo w])
      (fun w => by
        change inner ℝ ((2 : ℝ) • T w - w) w ≤ 1 * ‖w‖ ^ 2
        rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
        nlinarith [hup w])
    simpa using h
  have hb : ‖(2 : ℝ) • T v - v‖ ≤ ‖v‖ :=
    (B.le_opNorm v).trans (by simpa using mul_le_mul_of_nonneg_right hBn (norm_nonneg v))
  have hsq := (sq_le_sq₀ (norm_nonneg ((2 : ℝ) • T v - v)) (norm_nonneg v)).mpr hb
  rw [norm_sub_sq_real, norm_smul, real_inner_smul_left] at hsq
  norm_num at hsq
  nlinarith

/-- The contraction conclusion is independent of which finite bounds constructed the multiplier. -/
theorem hessianMultiplier_norm_sq_le_curvature_of_bounds (μ : Measure E) (V : E → ℝ)
    (hV : ContDiff ℝ 2 V) (m L : ℝ)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hup : ∀ x v, fderiv ℝ (fderiv ℝ V) x v v ≤ L * ‖v‖ ^ 2)
    (hpos : ∀ x v, 0 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hunit : ∀ x v, fderiv ℝ (fderiv ℝ V) x v v ≤ ‖v‖ ^ 2)
    (G : Lp E 2 μ) :
    ‖hessianMultiplier μ V hV m L hlo hup G‖ ^ 2 ≤
      inner ℝ (hessianMultiplier μ V hV m L hlo hup G) G := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def]
  apply integral_mono_ae (L2.integrable_inner _ _) (L2.integrable_inner _ _)
  filter_upwards [hessianMultiplier_coe μ V hV m L hlo hup G] with x hx
  rw [hx, real_inner_self_eq_norm_sq]
  exact symmetric_contraction_sq_le _ (hessianOperator_symmetric hV x)
    (fun v => by simpa only [inner_hessianOperator] using hpos x v)
    (fun v => by simpa only [inner_hessianOperator] using hunit x v) (G x)

/-- A positive Hessian bounded by the identity satisfies H squared <= H on vector L2. -/
theorem hessianMultiplier_norm_sq_le_curvature (μ : Measure E) (V : E → ℝ)
    (hV : ContDiff ℝ 2 V)
    (hlo : ∀ x v, 0 * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hup : ∀ x v, fderiv ℝ (fderiv ℝ V) x v v ≤ 1 * ‖v‖ ^ 2)
    (G : Lp E 2 μ) :
    ‖hessianMultiplier μ V hV 0 1 hlo hup G‖ ^ 2 ≤
      inner ℝ (hessianMultiplier μ V hV 0 1 hlo hup G) G := by
  exact hessianMultiplier_norm_sq_le_curvature_of_bounds μ V hV 0 1 hlo hup
    (fun x v => by simpa only [zero_mul] using hlo x v)
    (fun x v => by simpa only [one_mul] using hup x v) G

end AcceleratedLogConcave.Analysis.Poisson
