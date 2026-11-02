import AcceleratedLogConcave.Numerics.AffineFlowIdentities
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Strong L² suppliers for the actual sampling probability flow

Under the manuscript's C² convex potential and upper-Hessian bound, this file
derives uniform affine envelopes, Gaussian L² membership, canonical continuous
L² lifts and their signed integral equations. The center is deterministic.

The explicit time clamp agrees with the actual flow on its closed source slab.
It is used only for continuity and envelopes: no ordinary endpoint derivative,
joint exceptional-set selection, quantitative high-order cell bound, or random-
center/coupling conclusion is asserted. The generic integral bridge uses scalar
L² pairings and Fubini, never point evaluation as a continuous linear map.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ContDiff
set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace AcceleratedLogConcave.Numerics.SamplingFlowLp

variable {ι : Type*} [Fintype ι]

private theorem norm_sq_toLp {g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (hg : MemLp g 2 (stdGaussian (EuclideanSpace ℝ ι))) :
    ‖hg.toLp g‖ ^ 2 = ∫ p, ‖g p‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with p hp
  rw [hp, real_inner_self_eq_norm_sq]

/-- Joint continuity and one genuine L² envelope give continuity of the canonical L² classes. -/
theorem continuous_toLp_of_dominated
    (g : ℝ → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (hg : Continuous (Function.uncurry g))
    (B : EuclideanSpace ℝ ι → ℝ)
    (hB : MemLp B 2 (stdGaussian (EuclideanSpace ℝ ι)))
    (hbound : ∀ t p, ‖g t p‖ ≤ B p)
    (hm : ∀ t, MemLp (g t) 2 (stdGaussian (EuclideanSpace ℝ ι))) :
    Continuous (fun t => (hm t).toLp (g t)) := by
  rw [continuous_iff_continuousAt]
  intro s
  have hc : Continuous (fun t => ∫ p, ‖g t p - g s p‖ ^ 2
      ∂stdGaussian (EuclideanSpace ℝ ι)) := by
    apply continuous_of_dominated (bound := fun p => (2 * B p)^2)
    · intro t
      exact ((hg.comp (continuous_const.prodMk continuous_id)).sub
        (hg.comp (continuous_const.prodMk continuous_id))).norm.pow 2 |>.aestronglyMeasurable
    · intro t
      filter_upwards [] with p
      have hn : ‖g t p - g s p‖ ≤ 2 * B p :=
        (norm_sub_le _ _).trans (by linarith [hbound t p, hbound s p])
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖g t p - g s p‖)]
      exact pow_le_pow_left₀ (norm_nonneg _) hn 2
    · exact (hB.const_mul 2).integrable_sq
    · filter_upwards [] with p
      exact ((hg.comp (continuous_id.prodMk continuous_const)).sub continuous_const).norm.pow 2
  have heq (t : ℝ) :
      dist ((hm t).toLp (g t)) ((hm s).toLp (g s)) =
        Real.sqrt (∫ p, ‖g t p - g s p‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι)) := by
    rw [dist_eq_norm, ← MemLp.toLp_sub, ← norm_sq_toLp]
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  simp_rw [heq]
  simpa [Function.comp_def] using ((Real.continuous_sqrt.comp hc).continuousAt (x := s)).tendsto

/-- Signed pointwise integration commutes with the canonical L² lift under genuine
joint continuity and a common L² envelope. The proof uses scalar pairings and Fubini. -/
theorem toLp_intervalIntegral_of_dominated
    (g : ℝ → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (hg : Continuous (Function.uncurry g))
    (B : EuclideanSpace ℝ ι → ℝ)
    (hB : MemLp B 2 (stdGaussian (EuclideanSpace ℝ ι)))
    (hbound : ∀ t p, ‖g t p‖ ≤ B p)
    (hm : ∀ t, MemLp (g t) 2 (stdGaussian (EuclideanSpace ℝ ι)))
    (a b : ℝ) :
    ∃ hi : MemLp (fun p => ∫ t in a..b, g t p) 2
        (stdGaussian (EuclideanSpace ℝ ι)),
      hi.toLp (fun p => ∫ t in a..b, g t p) = ∫ t in a..b, (hm t).toLp (g t) := by
  let μ := stdGaussian (EuclideanSpace ℝ ι)
  have hmeas : StronglyMeasurable (fun p => ∫ t in a..b, g t p) := by
    unfold intervalIntegral
    exact hg.stronglyMeasurable.integral_prod_left.sub hg.stronglyMeasurable.integral_prod_left
  have hi : MemLp (fun p => ∫ t in a..b, g t p) 2 μ := by
    apply (hB.const_mul |b-a|).mono' hmeas.aestronglyMeasurable
    filter_upwards [] with p
    simpa only [mul_comm] using
      intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ => hbound t p)
  refine ⟨hi, ?_⟩
  have hgi (p) : IntervalIntegrable (fun t => g t p) volume a b :=
    (hg.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b
  have hli : IntervalIntegrable (fun t => (hm t).toLp (g t)) volume a b :=
    (continuous_toLp_of_dominated g hg B hB hbound hm).intervalIntegrable a b
  apply ext_inner_left ℝ
  intro w
  have : IsFiniteMeasure (volume.restrict (uIoc a b)) := by
    unfold uIoc
    infer_instance
  have hprod : Integrable (fun q : ℝ × EuclideanSpace ℝ ι =>
      inner ℝ (w q.2) (g q.1 q.2)) ((volume.restrict (uIoc a b)).prod μ) := by
    apply (((Lp.memLp w).norm.integrable_mul hB).comp_snd _).mono'
      ((Lp.aestronglyMeasurable w).comp_snd.inner hg.aestronglyMeasurable)
    filter_upwards [] with q
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hbound q.1 q.2) (norm_nonneg _))
  calc
    inner ℝ w (hi.toLp (fun p => ∫ t in a..b, g t p)) =
        ∫ p, inner ℝ (w p) (∫ t in a..b, g t p) ∂μ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hi.coeFn_toLp] with p hp
      rw [hp]
    _ = ∫ p, (∫ t in a..b, inner ℝ (w p) (g t p)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with p
      exact ((innerSL ℝ (w p)).intervalIntegral_comp_comm (hgi p)).symm
    _ = ∫ t in a..b, ∫ p, inner ℝ (w p) (g t p) ∂μ :=
      (intervalIntegral_integral_swap hprod).symm
    _ = ∫ t in a..b, inner ℝ w ((hm t).toLp (g t)) := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(hm t).coeFn_toLp] with p hp
      rw [hp]
    _ = inner ℝ w (∫ t in a..b, (hm t).toLp (g t)) :=
      (innerSL ℝ w).intervalIntegral_comp_comm hli

section ActualFlow
variable {F : EuclideanSpace ℝ ι → ℝ} (hF : ContDiff ℝ 2 F)
  {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
  (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
  (x : EuclideanSpace ℝ ι) {r : ℝ} (hr : 0 < r)
  {T : ℝ} (hT : 0 ≤ T) (hT1 : T < 1)

/-- Explicit clipping prevents any claim about the chosen raw flow outside its source slab. -/
def sourceTime (t : ℝ) : ℝ := (projIcc 0 T hT t : ℝ)

/-- The actual probability flow with standard Gaussian input, observed at clipped time. -/
def sourcePath (t : ℝ) (p : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  Conditional.convexProbabilityFlow hF hell hlo hup x hr hT
    (by norm_num) hT1 ⟨0, le_rfl, hT⟩ p (sourceTime hT t)

/-- The actual centered physical primitive reply on the same probability path. -/
def centeredReply (t : ℝ) (p : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  Gibbs.primitiveMean F
    (x + (r * sourceTime hT t) • sourcePath hF hell hlo hup x hr hT hT1 t p)
    (r * Real.sqrt (1 - (sourceTime hT t)^2)) - Gibbs.primitiveMean F x r

theorem sourceTime_mem (t : ℝ) : sourceTime hT t ∈ Icc 0 T := (projIcc 0 T hT t).property

theorem sourceTime_eq {t : ℝ} (ht : t ∈ Icc 0 T) : sourceTime hT t = t := by
  simp [sourceTime, projIcc_of_mem hT ht]

theorem continuous_sourceTime : Continuous (sourceTime hT) :=
  continuous_subtype_val.comp continuous_projIcc

theorem sourcePath_eq {t : ℝ} (ht : t ∈ Icc 0 T) (p) :
    sourcePath hF hell hlo hup x hr hT hT1 t p =
      Conditional.convexProbabilityFlow hF hell hlo hup x hr hT
        (by norm_num) hT1 ⟨0, le_rfl, hT⟩ p t := by
  simp only [sourcePath, sourceTime_eq hT ht]

theorem continuous_sourcePath : Continuous (Function.uncurry (sourcePath hF hell hlo hup x hr hT hT1)) := by
  unfold sourcePath Conditional.convexProbabilityFlow Conditional.probabilityFlow
    Conditional.meanProbabilityFlow
  exact (OAI.LogConcaveSampling.GlobalODE.flow_joint_continuous _ _ _).comp
    (continuous_snd.prodMk ((continuous_projIcc (h := hT)).comp continuous_fst))

theorem lipschitzWith_sourcePath (t : ℝ) :
    LipschitzWith ⟨Real.exp (r^2 * ell * T), (Real.exp_pos _).le⟩
      (sourcePath hF hell hlo hup x hr hT hT1 t) := by
  have h := OAI.LogConcaveSampling.GlobalODE.flow_lipschitz
    (fun u (_hu : u ∈ Icc 0 T) => Conditional.clippedProbabilityVelocity_lipschitz hT r
      (fun v hv => Conditional.lipschitzWith_conditionalMean hF hell hlo hup x hr
        (by linarith [hv.1]) (hv.2.trans_lt hT1)) u)
    (Conditional.clippedProbabilityVelocity_continuous hT r
      (Conditional.continuousOn_conditionalMean hF hlo hup x r (a := 0) (b := T) (by norm_num) hT1))
    (⟨0, le_rfl, hT⟩ : Icc 0 T) (projIcc 0 T hT t)
  change LipschitzWith _ (sourcePath hF hell hlo hup x hr hT hT1 t) at h
  apply h.weaken
  change Real.exp ((‖r‖ * (r * ell)) * |sourceTime hT t - 0|) ≤ _
  rw [Real.norm_eq_abs, abs_of_pos hr, sub_zero, abs_of_nonneg (sourceTime_mem hT t).1]
  apply Real.exp_le_exp.mpr
  have hle := mul_le_mul_of_nonneg_left (sourceTime_mem hT t).2 (mul_nonneg (sq_nonneg r) hell)
  nlinarith

theorem centeredReply_eq_conditionalMean (t : ℝ) (p) :
    centeredReply hF hell hlo hup x hr hT hT1 t p =
      Conditional.conditionalMean F x r (sourceTime hT t)
        (sourcePath hF hell hlo hup x hr hT hT1 t p) - Gibbs.primitiveMean F x r := by
  rw [centeredReply, AffineFlowIdentities.conditionalMean_eq_primitiveMean hF hell hlo hup x hr
    (by linarith [(sourceTime_mem hT t).1]) ((sourceTime_mem hT t).2.trans_lt hT1)]

theorem continuous_centeredReply :
    Continuous (Function.uncurry (centeredReply hF hell hlo hup x hr hT hT1)) := by
  have hc := (Conditional.continuousOn_conditionalMean hF hlo hup x r (by norm_num : (-1:ℝ)<0) hT1).comp_continuous
    (((continuous_sourceTime hT).comp continuous_fst).prodMk
      (continuous_sourcePath hF hell hlo hup x hr hT hT1))
    (fun q => ⟨sourceTime_mem hT q.1, mem_univ _⟩)
  have heq : Function.uncurry (centeredReply hF hell hlo hup x hr hT hT1) =
      fun q => Conditional.conditionalMean F x r (sourceTime hT q.1)
        (sourcePath hF hell hlo hup x hr hT hT1 q.1 q.2) - Gibbs.primitiveMean F x r := by
    funext q
    exact centeredReply_eq_conditionalMean hF hell hlo hup x hr hT hT1 q.1 q.2
  rw [heq]
  exact hc.sub continuous_const

/-- Uniform affine envelopes are derived from actual drift Lipschitz estimates and compactness. -/
theorem uniform_affine_envelopes :
    ∃ D A B : ℝ, 0 ≤ D ∧ 0 ≤ A ∧ 0 ≤ B ∧
      (∀ t ∈ Icc 0 T, ∀ p, ‖Conditional.probabilityVelocity F x r t p‖ ≤
        (r^2 * ell) * ‖p‖ + D) ∧
      (∀ t p, ‖sourcePath hF hell hlo hup x hr hT hT1 t p‖ ≤
        Real.exp (r^2 * ell * T) * ‖p‖ + A) ∧
      (∀ t p, ‖centeredReply hF hell hlo hup x hr hT hT1 t p‖ ≤
        (r * ell * Real.exp (r^2 * ell * T)) * ‖p‖ + B) := by
  have hmc : ContinuousOn (fun t => Conditional.conditionalMean F x r t 0) (Icc 0 T) := by
    change ContinuousOn ((Function.uncurry (Conditional.conditionalMean F x r)) ∘
      (fun t : ℝ => (t, (0 : EuclideanSpace ℝ ι)))) (Icc 0 T)
    exact (Conditional.continuousOn_conditionalMean hF hlo hup x r (a := 0) (b := T) (by norm_num) hT1).comp
      (continuous_id.prodMk continuous_const).continuousOn (fun t ht => ⟨ht, mem_univ _⟩)
  obtain ⟨H, hH⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) T)).exists_bound_of_continuousOn hmc
  have hH0 : 0 ≤ H := (norm_nonneg _).trans (hH 0 ⟨le_rfl, hT⟩)
  obtain ⟨A, hA⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) T)).exists_bound_of_continuousOn
    (AffineFlowIdentities.convexProbabilityFlow_continuous hF hell hlo hup x hr hT
      (by norm_num) hT1 ⟨0, le_rfl, hT⟩ 0).continuousOn
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 ⟨le_rfl, hT⟩)
  have hpath (t p) : ‖sourcePath hF hell hlo hup x hr hT hT1 t p‖ ≤
      Real.exp (r^2 * ell * T) * ‖p‖ + A := by
    have hl := (lipschitzWith_sourcePath hF hell hlo hup x hr hT hT1 t).norm_sub_le p 0
    simp only [sub_zero] at hl
    have ha := hA (sourceTime hT t) (sourceTime_mem hT t)
    change ‖sourcePath hF hell hlo hup x hr hT hT1 t 0‖ ≤ A at ha
    exact (norm_le_norm_sub_add _ _).trans (add_le_add hl ha)
  refine ⟨r * H, A, r * ell * A + H + ‖Gibbs.primitiveMean F x r‖,
    mul_nonneg hr.le hH0, hA0,
    add_nonneg (add_nonneg (mul_nonneg (mul_nonneg hr.le hell) hA0) hH0) (norm_nonneg _),
    ?_, hpath, ?_⟩
  · intro t ht p
    have hl := (Conditional.lipschitzWith_probabilityVelocity hF hell hlo hup x hr
      (by linarith [ht.1]) (ht.2.trans_lt hT1)).norm_sub_le p 0
    simp only [sub_zero] at hl
    have hb : ‖Conditional.probabilityVelocity F x r t 0‖ ≤ r * H := by
      simpa only [Conditional.probabilityVelocity, norm_smul, Real.norm_eq_abs, abs_neg,
        abs_of_pos hr] using mul_le_mul_of_nonneg_left (hH t ht) hr.le
    exact (norm_le_norm_sub_add _ _).trans (add_le_add hl hb)
  · intro t p
    rw [centeredReply_eq_conditionalMean hF hell hlo hup x hr hT hT1]
    have hl := (Conditional.lipschitzWith_conditionalMean hF hell hlo hup x hr
      (by linarith [(sourceTime_mem hT t).1]) ((sourceTime_mem hT t).2.trans_lt hT1)).norm_sub_le
      (sourcePath hF hell hlo hup x hr hT hT1 t p) 0
    simp only [sub_zero] at hl
    change _ ≤ (r * ell) * ‖sourcePath hF hell hlo hup x hr hT hT1 t p‖ at hl
    have hp := mul_le_mul_of_nonneg_left (hpath t p) (mul_nonneg hr.le hell)
    have hb := hH (sourceTime hT t) (sourceTime_mem hT t)
    have hn := norm_le_norm_sub_add
      (Conditional.conditionalMean F x r (sourceTime hT t) (sourcePath hF hell hlo hup x hr hT hT1 t p))
      (Conditional.conditionalMean F x r (sourceTime hT t) 0)
    have hs := norm_sub_le
      (Conditional.conditionalMean F x r (sourceTime hT t) (sourcePath hF hell hlo hup x hr hT hT1 t p))
      (Gibbs.primitiveMean F x r)
    nlinarith

theorem samplingPath_memLp_two (t : ℝ) :
    MemLp (sourcePath hF hell hlo hup x hr hT hT1 t) 2
      (stdGaussian (EuclideanSpace ℝ ι)) := by
  obtain ⟨_, A, _, _, _, _, _, hp, _⟩ := uniform_affine_envelopes hF hell hlo hup x hr hT hT1
  have hc : Continuous (sourcePath hF hell hlo hup x hr hT hT1 t) := by
    change Continuous ((Function.uncurry (sourcePath hF hell hlo hup x hr hT hT1)) ∘
      (fun p => (t, p)))
    exact (continuous_sourcePath hF hell hlo hup x hr hT hT1).comp (continuous_const.prodMk continuous_id)
  exact Gibbs.memLp_two_stdGaussian_of_affine_bound hc _ A (hp t)

theorem samplingCenteredReply_memLp_two (t : ℝ) :
    MemLp (centeredReply hF hell hlo hup x hr hT hT1 t) 2
      (stdGaussian (EuclideanSpace ℝ ι)) := by
  obtain ⟨_, _, B, _, _, _, _, _, hu⟩ := uniform_affine_envelopes hF hell hlo hup x hr hT hT1
  have hc : Continuous (centeredReply hF hell hlo hup x hr hT hT1 t) := by
    change Continuous ((Function.uncurry (centeredReply hF hell hlo hup x hr hT hT1)) ∘
      (fun p => (t, p)))
    exact (continuous_centeredReply hF hell hlo hup x hr hT hT1).comp (continuous_const.prodMk continuous_id)
  exact Gibbs.memLp_two_stdGaussian_of_affine_bound hc _ B (hu t)

/-- Signed path identity for the same initial Gaussian seed, on any two slab times. -/
theorem sourcePath_eq_sub_integral (a b : ℝ) (ha : a ∈ Icc 0 T) (hb : b ∈ Icc 0 T) (p) :
    sourcePath hF hell hlo hup x hr hT hT1 b p =
      sourcePath hF hell hlo hup x hr hT hT1 a p -
        r • ((b-a) • Gibbs.primitiveMean F x r +
          ∫ t in a..b, centeredReply hF hell hlo hup x hr hT hT1 t p) := by
  let Y := Conditional.convexProbabilityFlow hF hell hlo hup x hr hT
    (by norm_num) hT1 ⟨0, le_rfl, hT⟩ p
  have hY : Continuous Y := AffineFlowIdentities.convexProbabilityFlow_continuous
    hF hell hlo hup x hr hT (by norm_num) hT1 _ _
  have hM : ContinuousOn (fun t => Conditional.conditionalMean F x r t (Y t)) (Icc 0 T) := by
    change ContinuousOn ((Function.uncurry (Conditional.conditionalMean F x r)) ∘
      (fun t : ℝ => (t, Y t))) (Icc 0 T)
    exact (Conditional.continuousOn_conditionalMean hF hlo hup x r (a := 0) (b := T) (by norm_num) hT1).comp
      (continuous_id.prodMk hY).continuousOn (fun t ht => ⟨ht, mem_univ _⟩)
  have hsub : uIcc a b ⊆ Icc 0 T := uIcc_subset_Icc ha hb
  have hI : IntervalIntegrable (fun t => (-r) • Conditional.conditionalMean F x r t (Y t))
      volume a b := ((continuousOn_const (c := (-r : ℝ))).smul (hM.mono hsub)).intervalIntegrable
  have hFTC : (∫ t in a..b, (-r) • Conditional.conditionalMean F x r t (Y t)) = Y b - Y a := by
    apply intervalIntegral.integral_eq_sub_of_hasDeriv_right hY.continuousOn _ hI
    intro t ht
    have ht0 : 0 < t := lt_of_le_of_lt (le_min ha.1 hb.1) ht.1
    have htT : t < T := lt_of_lt_of_le ht.2 (max_le ha.2 hb.2)
    exact ((Conditional.convexProbabilityFlow_deriv hF hell hlo hup x hr hT
      (by norm_num) hT1 ⟨0, le_rfl, hT⟩ p ⟨ht0.le, htT.le⟩).hasDerivAt
      (Icc_mem_nhds ht0 htT)).hasDerivWithinAt
  have hm : (∫ t in a..b, Conditional.conditionalMean F x r t (Y t)) =
      (b-a) • Gibbs.primitiveMean F x r +
        ∫ t in a..b, centeredReply hF hell hlo hup x hr hT hT1 t p := by
    calc
      _ = ∫ t in a..b, (Gibbs.primitiveMean F x r +
          centeredReply hF hell hlo hup x hr hT hT1 t p) := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only
        rw [centeredReply_eq_conditionalMean hF hell hlo hup x hr hT hT1,
          sourceTime_eq hT (hsub ht), sourcePath_eq hF hell hlo hup x hr hT hT1 (hsub ht)]
        dsimp only [Y]
        abel
      _ = _ := by
        have hc : Continuous (fun t => centeredReply hF hell hlo hup x hr hT hT1 t p) := by
          change Continuous ((Function.uncurry (centeredReply hF hell hlo hup x hr hT hT1)) ∘
            (fun t => (t, p)))
          exact (continuous_centeredReply hF hell hlo hup x hr hT hT1).comp
            (continuous_id.prodMk continuous_const)
        rw [intervalIntegral.integral_add intervalIntegrable_const
          (hc.intervalIntegrable a b), intervalIntegral.integral_const]
  rw [intervalIntegral.integral_smul, neg_smul, hm] at hFTC
  rw [sourcePath_eq hF hell hlo hup x hr hT hT1 hb,
    sourcePath_eq hF hell hlo hup x hr hT hT1 ha]
  change Y b = Y a - _
  exact (eq_sub_iff_add_eq.mp hFTC).symm.trans (by abel)

/-- Canonical L² path class. -/
def pathLp (t : ℝ) : Lp (EuclideanSpace ℝ ι) 2 (stdGaussian (EuclideanSpace ℝ ι)) :=
  (samplingPath_memLp_two hF hell hlo hup x hr hT hT1 t).toLp
    (sourcePath hF hell hlo hup x hr hT hT1 t)

/-- Canonical L² centered-reply class. -/
def replyLp (t : ℝ) : Lp (EuclideanSpace ℝ ι) 2 (stdGaussian (EuclideanSpace ℝ ι)) :=
  (samplingCenteredReply_memLp_two hF hell hlo hup x hr hT hT1 t).toLp
    (centeredReply hF hell hlo hup x hr hT hT1 t)

private theorem affineNorm_memLp (a b : ℝ) :
    MemLp (fun p : EuclideanSpace ℝ ι => a * ‖p‖ + b) 2
      (stdGaussian (EuclideanSpace ℝ ι)) :=
  ((IsGaussian.memLp_two_id (μ := stdGaussian (EuclideanSpace ℝ ι))).norm.const_mul a).add (memLp_const b)

theorem continuous_pathLp : Continuous (pathLp hF hell hlo hup x hr hT hT1) := by
  obtain ⟨_, A, _, _, _, _, _, hp, _⟩ := uniform_affine_envelopes hF hell hlo hup x hr hT hT1
  exact continuous_toLp_of_dominated _ (continuous_sourcePath hF hell hlo hup x hr hT hT1)
    _ (affineNorm_memLp _ A) hp _

theorem continuous_replyLp : Continuous (replyLp hF hell hlo hup x hr hT hT1) := by
  obtain ⟨_, _, B, _, _, _, _, _, hu⟩ := uniform_affine_envelopes hF hell hlo hup x hr hT hT1
  exact continuous_toLp_of_dominated _ (continuous_centeredReply hF hell hlo hup x hr hT hT1)
    _ (affineNorm_memLp _ B) hu _

theorem replyLp_integral (a b : ℝ) :
    ∃ hi : MemLp (fun p => ∫ t in a..b, centeredReply hF hell hlo hup x hr hT hT1 t p) 2
        (stdGaussian (EuclideanSpace ℝ ι)),
      hi.toLp (fun p => ∫ t in a..b, centeredReply hF hell hlo hup x hr hT hT1 t p) =
        ∫ t in a..b, replyLp hF hell hlo hup x hr hT hT1 t := by
  obtain ⟨_, _, B, _, _, _, _, _, hu⟩ := uniform_affine_envelopes hF hell hlo hup x hr hT hT1
  exact toLp_intervalIntegral_of_dominated _ (continuous_centeredReply hF hell hlo hup x hr hT hT1)
    _ (affineNorm_memLp _ B) hu _ a b

/-- The actual signed L² equation, with no regularity or integral conclusion assumed. -/
theorem pathLp_eq_sub_integral (a b : ℝ) (ha : a ∈ Icc 0 T) (hb : b ∈ Icc 0 T) :
    pathLp hF hell hlo hup x hr hT hT1 b = pathLp hF hell hlo hup x hr hT hT1 a -
      r • ((b-a) • (memLp_const (μ := stdGaussian (EuclideanSpace ℝ ι)) (p := 2)
        (Gibbs.primitiveMean F x r)).toLp (fun _ => Gibbs.primitiveMean F x r) +
        ∫ t in a..b, replyLp hF hell hlo hup x hr hT hT1 t) := by
  obtain ⟨hi, hiEq⟩ := replyLp_integral hF hell hlo hup x hr hT hT1 a b
  rw [← hiEq]
  unfold pathLp
  rw [← MemLp.toLp_const_smul, ← MemLp.toLp_add, ← MemLp.toLp_const_smul,
    ← MemLp.toLp_sub]
  apply MemLp.toLp_congr
  filter_upwards [] with p
  exact sourcePath_eq_sub_integral hF hell hlo hup x hr hT hT1 a b ha hb p

/-- Receiver-compatible per-time a.e. flow identity. No joint exceptional set is asserted. -/
theorem sourcePath_ae_eq_initial_sub_integral (a : ℝ) (ha : a ∈ Icc 0 T) :
    sourcePath hF hell hlo hup x hr hT hT1 a =ᵐ[stdGaussian (EuclideanSpace ℝ ι)]
      fun p => p - r • (a • Gibbs.primitiveMean F x r +
        ((∫ t in 0..a, replyLp hF hell hlo hup x hr hT hT1 t) :
          Lp (EuclideanSpace ℝ ι) 2 (stdGaussian (EuclideanSpace ℝ ι))) p) := by
  obtain ⟨hi, hiEq⟩ := replyLp_integral hF hell hlo hup x hr hT hT1 0 a
  rw [← hiEq]
  filter_upwards [hi.coeFn_toLp] with p hp
  rw [hp]
  have h := sourcePath_eq_sub_integral hF hell hlo hup x hr hT hT1 0 a ⟨le_rfl,hT⟩ ha p
  have hz : sourcePath hF hell hlo hup x hr hT hT1 0 p = p := by
    rw [sourcePath_eq hF hell hlo hup x hr hT hT1 ⟨le_rfl,hT⟩]
    exact Conditional.convexProbabilityFlow_initial hF hell hlo hup x hr hT (by norm_num) hT1 _ p
  simpa only [hz, sub_zero] using h

/-- Canonical strong L² suppliers for the actual fixed-center Gaussian-seed flow. -/
theorem exists_samplingFlowLp :
  ∃ (hpath : ∀ t : ℝ, MemLp (sourcePath hF hell hlo hup x hr hT hT1 t) 2
        (stdGaussian (EuclideanSpace ℝ ι)))
    (hreply : ∀ t : ℝ, MemLp (centeredReply hF hell hlo hup x hr hT hT1 t) 2
        (stdGaussian (EuclideanSpace ℝ ι))),
    let X : ℝ → Lp (EuclideanSpace ℝ ι) 2 (stdGaussian (EuclideanSpace ℝ ι)) :=
      fun t => (hpath t).toLp (sourcePath hF hell hlo hup x hr hT hT1 t)
    let U : ℝ → Lp (EuclideanSpace ℝ ι) 2 (stdGaussian (EuclideanSpace ℝ ι)) :=
      fun t => (hreply t).toLp (centeredReply hF hell hlo hup x hr hT hT1 t)
    let base : Lp (EuclideanSpace ℝ ι) 2 (stdGaussian (EuclideanSpace ℝ ι)) :=
      (memLp_const (Gibbs.primitiveMean F x r)).toLp (fun _ => Gibbs.primitiveMean F x r)
    Continuous X ∧ Continuous U ∧
    (∀ t : ℝ, centeredReply hF hell hlo hup x hr hT hT1 t =ᵐ[
      stdGaussian (EuclideanSpace ℝ ι)] (U t : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)) ∧
    (∀ a b : ℝ, IntervalIntegrable U volume a b) ∧
    (∀ a b : ℝ, a ∈ Icc 0 T → b ∈ Icc 0 T →
      X b = X a - r • ((b-a) • base + ∫ t in a..b, U t)) ∧
    (∀ a : ℝ, a ∈ Icc 0 T →
      sourcePath hF hell hlo hup x hr hT hT1 a =ᵐ[stdGaussian (EuclideanSpace ℝ ι)]
        (fun p => p - r • (a • Gibbs.primitiveMean F x r +
          ((∫ t in 0..a, U t) : Lp (EuclideanSpace ℝ ι) 2
            (stdGaussian (EuclideanSpace ℝ ι))) p))) ∧
    (∀ t : ℝ, t ∈ Icc 0 T → ∀ p,
      sourcePath hF hell hlo hup x hr hT hT1 t p =
        Conditional.convexProbabilityFlow hF hell hlo hup x hr hT
          (by norm_num) hT1 ⟨0, le_rfl, hT⟩ p t) := by
  refine ⟨samplingPath_memLp_two hF hell hlo hup x hr hT hT1,
    samplingCenteredReply_memLp_two hF hell hlo hup x hr hT hT1, ?_⟩
  dsimp only
  refine ⟨continuous_pathLp hF hell hlo hup x hr hT hT1,
    continuous_replyLp hF hell hlo hup x hr hT hT1, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    exact (samplingCenteredReply_memLp_two hF hell hlo hup x hr hT hT1 t).coeFn_toLp.symm
  · exact (continuous_replyLp hF hell hlo hup x hr hT hT1).intervalIntegrable
  · exact fun a b ha hb => pathLp_eq_sub_integral hF hell hlo hup x hr hT hT1 a b ha hb
  · exact fun a ha => sourcePath_ae_eq_initial_sub_integral hF hell hlo hup x hr hT hT1 a ha
  · exact fun t ht p => sourcePath_eq hF hell hlo hup x hr hT hT1 ht p

end ActualFlow
end AcceleratedLogConcave.Numerics.SamplingFlowLp
