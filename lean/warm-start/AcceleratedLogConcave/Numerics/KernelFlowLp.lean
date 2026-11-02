import AcceleratedLogConcave.Numerics.SamplingFlowLp

/-!
# Actual stationary transported-kernel L² suppliers

The clamped transported Stein integrand gives one explicit integral extension of
`(B_t - I) G` on the source slab. Its ordinary first derivative is valid at both
endpoints, including the vanishing derivative at zero. Canonical L² classes,
signed Bochner integral identities and dimension-sharp norm envelopes are
proved using the genuine stationary phase law. Its momentum marginal supplies
all needed moments; no position-moment assumption is imposed.

The same statements hold after any deterministic positive or negative centering
time, by the constructed source flow's actual measure preservation. The
potential is C², convex, with Hessian bounded by `ell`, and `r² * ell ≤ 1/2`.

Source: `sources/warm-start.tex`, transported kernel/centering at lines
1500–1575 and the singular-kernel quadrature at lines 2150–2171.
The clamped extension only claims a first derivative at the endpoints. Higher
material-derivative budgets, joint random-parameter choices and sampler laws
are separate obligations.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Numerics.KernelFlowLp
open AcceleratedLogConcave AcceleratedLogConcave.Conditional
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "P" => Centering.Phase E

structure Data (ι : Type*) [Fintype ι] where
  F : EuclideanSpace ℝ ι → ℝ
  hF : ContDiff ℝ 2 F
  ell : ℝ
  hell : 0 ≤ ell
  hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a
  hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2
  x : EuclideanSpace ℝ ι
  r : ℝ
  hr : 0 < r
  b : ℝ
  hb : 0 ≤ b
  hb1 : b < 1
  hsmall : r ^ 2 * ell ≤ 1 / 2

def seedMeasure (d : Data ι) : Measure P :=
  Kinetic.coupledPhaseMeasure (interpolationLaw d.F d.x d.r d.b)
def time (d : Data ι) (t : ℝ) : ℝ := (projIcc 0 d.b d.hb t : ℝ)
def integrand (d : Data ι) (t : ℝ) (z : P) : E :=
  transportedSteinIntegrand d.hF d.hell d.hlo d.hup d.x d.hr d.hb d.hb1
    (time d t) z.fst z.snd
def extension (d : Data ι) (t : ℝ) (z : P) : E :=
  d.r • ∫ q in d.b..t, q • integrand d q z
def kernel (d : Data ι) (z : P) : E :=
  transportedSteinKernelTranspose d.hF d.hell d.hlo d.hup d.x d.hr d.hb d.hb1
    z.fst z.snd
def centering [DecidableEq ι] (d : Data ι) (s : ℝ) (hs : 0 < s) (τ : ℝ) (z : P) : P :=
  Centering.sourceCenteringFlow d.hF d.hell d.hlo d.hup d.x d.hr d.hb d.hb1
    d.hsmall hs z τ

instance seedMeasure_probability (d : Data ι) : IsProbabilityMeasure (seedMeasure d) := by
  let := interpolationLaw_isProbabilityMeasure d.hF d.hlo d.x d.r d.b
  exact Kinetic.coupledPhaseMeasure_probability _

theorem momentum_preserving (d : Data ι) :
    MeasurePreserving (fun z : P => z.snd) (seedMeasure d) (stdGaussian E) := by
  let := interpolationLaw_isProbabilityMeasure d.hF d.hlo d.x d.r d.b
  refine ⟨(WithLp.prod_continuous_ofLp 2 E E).snd.measurable, ?_⟩
  rw [seedMeasure, Kinetic.coupledPhaseMeasure, Measure.map_map (by fun_prop) (by fun_prop)]
  change Measure.map Prod.snd ((interpolationLaw d.F d.x d.r d.b).prod (stdGaussian E)) = _
  simp

theorem momentum_memLp (d : Data ι) : MemLp (fun z : P => z.snd) 2 (seedMeasure d) :=
  (IsGaussian.memLp_two_id (μ := stdGaussian E)).comp_measurePreserving (momentum_preserving d)

theorem integral_momentum_norm_sq (d : Data ι) :
    (∫ z : P, ‖z.snd‖^2 ∂seedMeasure d) = (Module.finrank ℝ E : ℝ) := by
  have h := Gibbs.integral_norm_sq_stdGaussian («E» := E)
  rw [← (momentum_preserving d).map_eq,
    integral_map (momentum_preserving d).measurable.aemeasurable (by fun_prop)] at h
  exact h

theorem continuous_integrand (d : Data ι) : Continuous (Function.uncurry (integrand d)) := by
  have hp : Continuous (fun q : ℝ × P => (q.2.fst, projIcc 0 d.b d.hb q.1)) :=
    ((WithLp.prod_continuous_ofLp 2 E E).fst.comp continuous_snd).prodMk
      (continuous_projIcc.comp continuous_fst)
  exact ((continuous_transportedSteinIntegrand_joint d.hF d.hell d.hlo d.hup d.x
    d.hr d.hb d.hb1).comp hp).clm_apply
      ((WithLp.prod_continuous_ofLp 2 E E).snd.comp continuous_snd)

theorem norm_integrand_le (d : Data ι) (t : ℝ) (z : P) :
    ‖integrand d t z‖ ≤ (Real.exp 1 * (d.r*d.ell)) * ‖z.snd‖ := by
  exact ((transportedSteinIntegrand d.hF d.hell d.hlo d.hup d.x d.hr d.hb d.hb1
    (time d t) z.fst).le_opNorm z.snd).trans
    (mul_le_mul_of_nonneg_right (norm_transportedSteinIntegrand_le d.hF d.hell d.hlo
      d.hup d.x d.hr d.hb d.hb1 d.hsmall (projIcc 0 d.b d.hb t).property z.fst)
      (norm_nonneg _))

theorem integrand_memLp (d : Data ι) (t : ℝ) :
    MemLp (integrand d t) 2 (seedMeasure d) := by
  apply ((momentum_memLp d).norm.const_mul (Real.exp 1 * (d.r*d.ell))).mono'
    ((continuous_integrand d).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (norm_integrand_le d t)

theorem hasDerivAt_extension (d : Data ι) (t : ℝ) (z : P) :
    HasDerivAt (fun q => extension d q z) ((d.r*t) • integrand d t z) t := by
  have hh := (continuous_integrand d).comp
    (show Continuous (fun q : ℝ => (q,z)) from continuous_id.prodMk continuous_const)
  have hi : Continuous (fun q : ℝ => integrand d q z) := by
    simpa only [Function.comp_def, Function.uncurry_def] using hh
  have hc : Continuous (fun q : ℝ => q • integrand d q z) :=
    (continuous_id : Continuous (fun q : ℝ => q)).smul hi
  change HasDerivAt (fun q => d.r • ∫ v in d.b..q, v • integrand d v z)
    ((d.r*t) • integrand d t z) t
  have hd : HasDerivAt (fun q => ∫ v in d.b..q, v • integrand d v z)
      (t • integrand d t z) t :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable d.b t)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  convert! hd.const_smul d.r using 1
  simp only [smul_smul]

@[simp] theorem extension_terminal (d : Data ι) (z : P) : extension d d.b z = 0 := by
  simp [extension]
@[simp] theorem deriv_extension_zero (d : Data ι) (z : P) :
    deriv (fun q => extension d q z) 0 = 0 := by
  simpa using (hasDerivAt_extension d 0 z).deriv

theorem continuous_extension (d : Data ι) : Continuous (Function.uncurry (extension d)) := by
  have hswap : Continuous (fun p : P × ℝ => integrand d p.2 p.1) := by
    simpa only [Function.comp_def, Function.uncurry_def, Prod.swap] using
      (continuous_integrand d).comp continuous_swap
  have hJ : Continuous (fun p : P × ℝ => p.2 • integrand d p.2 p.1) :=
    continuous_snd.smul hswap
  convert! ((intervalIntegral.continuous_parametric_primitive_of_continuous
      (μ := (volume : Measure ℝ)) (a₀ := d.b) (f := fun z q => q • integrand d q z) hJ).comp continuous_swap).const_smul d.r using 1

theorem integrand_eq (d : Data ι) {t : ℝ} (ht : t ∈ Icc 0 d.b) (z : P) :
    integrand d t z = transportedSteinIntegrand d.hF d.hell d.hlo d.hup d.x
      d.hr d.hb d.hb1 t z.fst z.snd := by
  simp only [integrand, time, projIcc_of_mem d.hb ht]

theorem extension_eq_jacobian (d : Data ι) {t : ℝ} (ht : t ∈ Icc 0 d.b) (z : P) :
    extension d t z =
      (transportedJacobian d.hF d.hell d.hlo d.hup d.x d.hr d.hb d.hb1 t z.fst -
        ContinuousLinearMap.id ℝ E) z.snd := by
  have hBcont : ContinuousOn (fun q => transportedJacobian d.hF d.hell d.hlo d.hup
      d.x d.hr d.hb d.hb1 q z.fst z.snd) (Icc 0 d.b) :=
    (continuousOn_transportedJacobian d.hF d.hell d.hlo d.hup
    d.x d.hr d.hb d.hb1 z.fst).clm_apply continuousOn_const
  have hBder (q : ℝ) (hq : q ∈ Ioo t d.b) :
      HasDerivAt (fun v => transportedJacobian d.hF d.hell d.hlo d.hup
        d.x d.hr d.hb d.hb1 v z.fst z.snd) (d.r • (q • integrand d q z)) q := by
    have hq0 : 0 < q := ht.1.trans_lt hq.1
    have hqm : q ∈ Icc 0 d.b := ⟨hq0.le, hq.2.le⟩
    have hd := (transportedJacobian_deriv d.hF d.hell d.hlo d.hup d.x d.hr d.hb d.hb1
      hqm z.fst).hasDerivAt (Icc_mem_nhds hq0 hq.2)
    have hdg := hd.clm_apply (hasDerivAt_const q z.snd)
    simpa only [integrand_eq d hqm z, transportedSteinIntegrand,
      smul_apply, map_zero, add_zero, smul_smul] using hdg
  have hi : Continuous (fun q : ℝ => integrand d q z) := by
    simpa only [Function.comp_def, Function.uncurry_def] using
      (continuous_integrand d).comp (show Continuous (fun q : ℝ => (q,z)) from
        continuous_id.prodMk continuous_const)
  have hc : Continuous (fun q : ℝ => d.r • (q • integrand d q z)) :=
    ((continuous_id : Continuous (fun q : ℝ => q)).smul hi).const_smul d.r
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.2
    (hBcont.mono (Icc_subset_Icc ht.1 le_rfl)) hBder (hc.intervalIntegrable t d.b)
  dsimp only [extension]
  rw [← intervalIntegral.integral_smul, intervalIntegral.integral_symm, hftc]
  simp only [transportedJacobian_terminal, ContinuousLinearMap.id_apply,
    sub_apply, neg_sub]

theorem norm_extension_le (d : Data ι) {t : ℝ} (ht : t ∈ Icc 0 d.b) (z : P) :
    ‖extension d t z‖ ≤
      (Real.exp 1 * d.r^2 * d.ell / 2 * (d.b^2-t^2)) * ‖z.snd‖ := by
  let A := Real.exp 1 * (d.r*d.ell) * ‖z.snd‖
  have hB : ‖∫ q in t..d.b, q • integrand d q z‖ ≤ ∫ q in t..d.b, q * A := by
    apply intervalIntegral.norm_integral_le_of_norm_le ht.2
    · filter_upwards [] with q hq
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ht.1.trans hq.1.le)]
      exact mul_le_mul_of_nonneg_left (norm_integrand_le d q z) (ht.1.trans hq.1.le)
    · exact (continuous_id.mul continuous_const).intervalIntegrable t d.b
  have hi : (∫ q in t..d.b, q * A) = (d.b^2-t^2)/2 * A := by
    have hid : (∫ q in t..d.b, q) = d.b^2/2-t^2/2 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun q : ℝ => q^2/2) (f' := fun q : ℝ => q)
      · intro q _
        convert ((hasDerivAt_id q).pow 2).div_const 2 using 1 <;> simp
      · exact continuous_id.intervalIntegrable _ _
    rw [intervalIntegral.integral_mul_const, hid]
    ring
  rw [hi] at hB
  calc
    ‖extension d t z‖ = d.r * ‖∫ q in t..d.b, q • integrand d q z‖ := by
      rw [extension, intervalIntegral.integral_symm, norm_smul, norm_neg,
        Real.norm_eq_abs, abs_of_pos d.hr]
    _ ≤ d.r * ((d.b^2-t^2)/2 * A) := mul_le_mul_of_nonneg_left hB d.hr.le
    _ = _ := by dsimp [A]; ring

section LiftHelpers
variable {μ : Measure (Centering.Phase (EuclideanSpace ℝ ι))} [IsFiniteMeasure μ]
omit [IsFiniteMeasure μ] in
private theorem norm_sq_toLp {g : P → E}
    (hg : MemLp g 2 μ) :
    ‖hg.toLp g‖ ^ 2 = ∫ p, ‖g p‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with p hp
  rw [hp, real_inner_self_eq_norm_sq]

omit [IsFiniteMeasure μ] in
/-- Joint continuity and one genuine L² envelope give continuity of the canonical L² classes. -/
private theorem continuous_toLp_of_dominated
    (g : ℝ → P → E)
    (hg : Continuous (Function.uncurry g))
    (B : P → ℝ)
    (hB : MemLp B 2 μ)
    (hbound : ∀ t p, ‖g t p‖ ≤ B p)
    (hm : ∀ t, MemLp (g t) 2 μ) :
    Continuous (fun t => (hm t).toLp (g t)) := by
  rw [continuous_iff_continuousAt]
  intro s
  have hc : Continuous (fun t => ∫ p, ‖g t p - g s p‖ ^ 2
      ∂μ) := by
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
        Real.sqrt (∫ p, ‖g t p - g s p‖ ^ 2 ∂μ) := by
    rw [dist_eq_norm, ← MemLp.toLp_sub, ← norm_sq_toLp]
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  simp_rw [heq]
  simpa [Function.comp_def] using ((Real.continuous_sqrt.comp hc).continuousAt (x := s)).tendsto

/-- Signed pointwise integration commutes with the canonical L² lift under genuine
joint continuity and a common L² envelope. The proof uses scalar pairings and Fubini. -/
private theorem toLp_intervalIntegral_of_dominated
    (g : ℝ → P → E)
    (hg : Continuous (Function.uncurry g))
    (B : P → ℝ)
    (hB : MemLp B 2 μ)
    (hbound : ∀ t p, ‖g t p‖ ≤ B p)
    (hm : ∀ t, MemLp (g t) 2 μ)
    (a b : ℝ) :
    ∃ hi : MemLp (fun p => ∫ t in a..b, g t p) 2
        μ,
      hi.toLp (fun p => ∫ t in a..b, g t p) = ∫ t in a..b, (hm t).toLp (g t) := by
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
  have hprod : Integrable (fun q : ℝ × P =>
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

end LiftHelpers

/-- Canonical L² class of the actual clamped Stein integrand. -/
def integrandLp (d : Data ι) (t : ℝ) : Lp E 2 (seedMeasure d) :=
  (integrand_memLp d t).toLp (integrand d t)

theorem continuous_integrandLp (d : Data ι) : Continuous (integrandLp d) := by
  exact continuous_toLp_of_dominated (integrand d) (continuous_integrand d)
    (fun z => (Real.exp 1 * (d.r*d.ell)) * ‖z.snd‖)
    ((momentum_memLp d).norm.const_mul _) (norm_integrand_le d) (integrand_memLp d)

private theorem norm_lift_le (d : Data ι) {g : P → E}
    (hg : MemLp g 2 (seedMeasure d)) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z, ‖g z‖ ≤ C * ‖z.snd‖) :
    ‖hg.toLp g‖ ≤ C * Real.sqrt (Module.finrank ℝ E) := by
  have hb (z : P) : ‖g z‖^2 ≤ C^2 * ‖z.snd‖^2 := by
    have hh := pow_le_pow_left₀ (norm_nonneg (g z)) (hbound z) 2
    simpa only [mul_pow] using hh
  have hi := integral_mono
    ((memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg)
    (((momentum_memLp d).norm.integrable_sq).const_mul (C^2)) hb
  rw [integral_const_mul, integral_momentum_norm_sq, ← norm_sq_toLp hg] at hi
  have hs := Real.sq_sqrt (show 0 ≤ (Module.finrank ℝ E : ℝ) from Nat.cast_nonneg _)
  have hn : 0 ≤ C * Real.sqrt (Module.finrank ℝ E) := mul_nonneg hC (Real.sqrt_nonneg _)
  nlinarith [norm_nonneg (hg.toLp g)]

theorem norm_integrandLp_le (d : Data ι) (t : ℝ) :
    ‖integrandLp d t‖ ≤ Real.exp 1 * (d.r*d.ell) * Real.sqrt (Module.finrank ℝ E) :=
  norm_lift_le d (integrand_memLp d t) (mul_nonneg (Real.exp_pos 1).le (mul_nonneg d.hr.le d.hell)) (norm_integrand_le d t)

/-- Canonical integral-based L² extension; equality to the raw canonical lift is proved below. -/
def extensionLp (d : Data ι) (t : ℝ) : Lp E 2 (seedMeasure d) :=
  d.r • ∫ q in d.b..t, q • integrandLp d q

theorem hasDerivAt_extensionLp (d : Data ι) (t : ℝ) :
    HasDerivAt (extensionLp d) ((d.r*t) • integrandLp d t) t := by
  have hc : Continuous (fun q : ℝ => q • integrandLp d q) :=
    continuous_id.smul (continuous_integrandLp d)
  have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable d.b t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  convert! hd.const_smul d.r using 1
  simp only [smul_smul]

theorem continuous_extensionLp (d : Data ι) : Continuous (extensionLp d) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_extensionLp d t).continuousAt

@[simp] theorem extensionLp_terminal (d : Data ι) : extensionLp d d.b = 0 := by
  simp [extensionLp]
@[simp] theorem deriv_extensionLp_zero (d : Data ι) : deriv (extensionLp d) 0 = 0 := by
  simpa using (hasDerivAt_extensionLp d 0).deriv

theorem extensionLp_sub (d : Data ι) (a b : ℝ) :
    extensionLp d b - extensionLp d a = d.r • ∫ t in a..b, t • integrandLp d t := by
  have hc : Continuous (fun q : ℝ => (d.r*q) • integrandLp d q) :=
    (continuous_const.mul continuous_id).smul (continuous_integrandLp d)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_extensionLp d t) (hc.intervalIntegrable a b)
  rw [← h, ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [smul_smul]

private theorem lift_time_integral (d : Data ι) (a b : ℝ) :
    ∃ hi : MemLp (fun z => ∫ t in a..b, t • integrand d t z) 2 (seedMeasure d),
      hi.toLp (fun z => ∫ t in a..b, t • integrand d t z) =
        ∫ t in a..b, t • integrandLp d t := by
  let c : ℝ → ℝ := fun t => (projIcc (min a b) (max a b) min_le_max t : ℝ)
  let M := |a| + |b|
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hcb (t : ℝ) : |c t| ≤ M := by
    have h := (projIcc (min a b) (max a b) min_le_max t).property
    apply abs_le.mpr
    constructor
    · exact (le_min (by dsimp [M]; linarith [neg_abs_le a,abs_nonneg b])
        (by dsimp [M]; linarith [neg_abs_le b,abs_nonneg a])).trans h.1
    · exact h.2.trans (max_le (by dsimp [M]; linarith [le_abs_self a,abs_nonneg b])
        (by dsimp [M]; linarith [le_abs_self b,abs_nonneg a]))
  have hc : Continuous c := continuous_subtype_val.comp continuous_projIcc
  let g : ℝ → P → E := fun t z => c t • integrand d t z
  have hg : Continuous (Function.uncurry g) :=
    (hc.comp continuous_fst).smul (continuous_integrand d)
  have hm (t : ℝ) : MemLp (g t) 2 (seedMeasure d) := (integrand_memLp d t).const_smul (c t)
  let B : P → ℝ := fun z => M * (Real.exp 1 * (d.r*d.ell) * ‖z.snd‖)
  have hB : MemLp B 2 (seedMeasure d) := ((momentum_memLp d).norm.const_mul _).const_mul _
  have hbnd (t : ℝ) (z : P) : ‖g t z‖ ≤ B z := by
    dsimp only [g]
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul (hcb t) (norm_integrand_le d t z) (norm_nonneg _) hM
  obtain ⟨hi,hie⟩ := toLp_intervalIntegral_of_dominated g hg B hB hbnd hm a b
  have hce (t : ℝ) (ht : t ∈ uIcc a b) : c t = t := by
    exact congrArg Subtype.val (projIcc_of_mem min_le_max ht)
  have heq : (fun z => ∫ t in a..b, g t z) = (fun z => ∫ t in a..b, t • integrand d t z) := by
    funext z
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only [g]
    rw [hce t ht]
  have hi' : MemLp (fun z => ∫ t in a..b, t • integrand d t z) 2 (seedMeasure d) := heq ▸ hi
  refine ⟨hi', ?_⟩
  calc
    hi'.toLp _ = hi.toLp _ := MemLp.toLp_congr hi' hi (Filter.Eventually.of_forall fun z => congrFun heq.symm z)
    _ = _ := hie
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t ht
      change (hm t).toLp (g t) = t • integrandLp d t
      have hco : (hm t).toLp (g t) = c t • integrandLp d t :=
        MemLp.toLp_const_smul (c t) (integrand_memLp d t)
      simpa only [hce t ht] using hco

theorem extension_memLp (d : Data ι) (t : ℝ) : MemLp (extension d t) 2 (seedMeasure d) :=
  (lift_time_integral d d.b t).choose.const_smul d.r

theorem extension_toLp (d : Data ι) (t : ℝ) :
    (extension_memLp d t).toLp (extension d t) = extensionLp d t := by
  change d.r • (lift_time_integral d d.b t).choose.toLp
    (fun z => ∫ q in d.b..t, q • integrand d q z) = _
  exact congrArg (fun f => d.r • f) (lift_time_integral d d.b t).choose_spec

theorem norm_extensionLp_le (d : Data ι) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    ‖extensionLp d t‖ ≤
      (Real.exp 1 * d.r^2 * d.ell / 2 * (d.b^2-t^2)) * Real.sqrt (Module.finrank ℝ E) := by
  rw [← extension_toLp]
  apply norm_lift_le d (extension_memLp d t) _ (norm_extension_le d ht)
  have hsq : t^2 ≤ d.b^2 := pow_le_pow_left₀ ht.1 ht.2 2
  exact mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos 1).le (sq_nonneg d.r)) d.hell)
    (by norm_num)) (sub_nonneg.mpr hsq)

theorem kernel_eq_integral (d : Data ι) (z : P) :
    kernel d z = ∫ t in 0..d.b, integrand d t z := by
  rw [kernel, transportedSteinKernelTranspose,
    ContinuousLinearMap.intervalIntegral_apply
      (intervalIntegrable_transportedSteinIntegrand d.hF d.hell d.hlo d.hup
        d.x d.hr d.hb d.hb1 z.fst)]
  apply intervalIntegral.integral_congr
  intro t ht
  exact (integrand_eq d (by simpa only [uIcc_of_le d.hb] using ht) z).symm

theorem kernel_memLp (d : Data ι) : MemLp (kernel d) 2 (seedMeasure d) := by
  obtain ⟨hi,_⟩ := toLp_intervalIntegral_of_dominated (integrand d) (continuous_integrand d)
    (fun z => Real.exp 1 * (d.r*d.ell) * ‖z.snd‖)
    ((momentum_memLp d).norm.const_mul _) (norm_integrand_le d) (integrand_memLp d) 0 d.b
  exact MemLp.ae_eq (Filter.Eventually.of_forall fun z => (kernel_eq_integral d z).symm) hi

def kernelLp (d : Data ι) : Lp E 2 (seedMeasure d) := (kernel_memLp d).toLp (kernel d)

theorem kernelLp_eq_integral (d : Data ι) :
    kernelLp d = ∫ t in 0..d.b, integrandLp d t := by
  obtain ⟨hi,hie⟩ := toLp_intervalIntegral_of_dominated (integrand d) (continuous_integrand d)
    (fun z => Real.exp 1 * (d.r*d.ell) * ‖z.snd‖)
    ((momentum_memLp d).norm.const_mul _) (norm_integrand_le d) (integrand_memLp d) 0 d.b
  exact (MemLp.toLp_congr (kernel_memLp d) hi
    (Filter.Eventually.of_forall (kernel_eq_integral d))).trans hie

theorem norm_kernelLp_le (d : Data ι) :
    ‖kernelLp d‖ ≤ Real.exp 1 * (d.r*d.ell) * d.b * Real.sqrt (Module.finrank ℝ E) := by
  apply norm_lift_le d (kernel_memLp d)
    (mul_nonneg (mul_nonneg (Real.exp_pos 1).le (mul_nonneg d.hr.le d.hell)) d.hb)
  intro z
  exact ((transportedSteinKernelTranspose d.hF d.hell d.hlo d.hup d.x d.hr d.hb d.hb1
    z.fst).le_opNorm z.snd).trans
    (mul_le_mul_of_nonneg_right (norm_transportedSteinKernelTranspose_le_terminal
      d.hF d.hell d.hlo d.hup d.x d.hr d.hb d.hb1 d.hsmall z.fst) (norm_nonneg _))

/-- All canonical L² conclusions for a literal reparameterization of the seed. -/
def Lift (d : Data ι) (θ : P → P) : Prop :=
  ∃ hH : ∀ t, MemLp (fun z => integrand d t (θ z)) 2 (seedMeasure d),
  ∃ hf : ∀ t, MemLp (fun z => extension d t (θ z)) 2 (seedMeasure d),
  ∃ hK : MemLp (fun z => kernel d (θ z)) 2 (seedMeasure d),
  let H := fun t => (hH t).toLp (fun z => integrand d t (θ z))
  let f := fun t => (hf t).toLp (fun z => extension d t (θ z))
  let K := hK.toLp (fun z => kernel d (θ z))
  Continuous H ∧ Continuous f ∧
  (∀ t, HasDerivAt f ((d.r*t) • H t) t) ∧
  (∀ a b, f b - f a = d.r • ∫ t in a..b, t • H t) ∧
  K = ∫ t in 0..d.b, H t ∧
  f d.b = 0 ∧ deriv f 0 = 0 ∧
  (∀ t, ‖H t‖ ≤ Real.exp 1 * (d.r*d.ell) * Real.sqrt (Module.finrank ℝ E)) ∧
  (∀ t ∈ Icc 0 d.b,
    ‖f t‖ ≤ (Real.exp 1 * d.r^2 * d.ell / 2 * (d.b^2-t^2)) *
      Real.sqrt (Module.finrank ℝ E)) ∧
  ‖K‖ ≤ Real.exp 1 * (d.r*d.ell) * d.b * Real.sqrt (Module.finrank ℝ E)

/-- The actual conclusions survive any genuinely measure-preserving seed pullback. -/
theorem lift_of_measurePreserving (d : Data ι) (θ : P → P)
    (hθ : MeasurePreserving θ (seedMeasure d) (seedMeasure d)) : Lift d θ := by
  let L : Lp E 2 (seedMeasure d) →L[ℝ] Lp E 2 (seedMeasure d) :=
    (Lp.compMeasurePreservingₗᵢ (p := 2) ℝ θ hθ).toContinuousLinearMap
  have hH (t : ℝ) : MemLp (fun z => integrand d t (θ z)) 2 (seedMeasure d) :=
    (integrand_memLp d t).comp_measurePreserving hθ
  have hf (t : ℝ) : MemLp (fun z => extension d t (θ z)) 2 (seedMeasure d) :=
    (extension_memLp d t).comp_measurePreserving hθ
  have hK : MemLp (fun z => kernel d (θ z)) 2 (seedMeasure d) :=
    (kernel_memLp d).comp_measurePreserving hθ
  have hHe (t : ℝ) : (hH t).toLp _ = L (integrandLp d t) := rfl
  have hfe (t : ℝ) : (hf t).toLp _ = L (extensionLp d t) := by
    rw [← extension_toLp]
    rfl
  have hKe : hK.toLp _ = L (kernelLp d) := rfl
  refine ⟨hH,hf,hK,?_⟩
  dsimp only
  simp only [hHe,hfe,hKe]
  have hn (v : Lp E 2 (seedMeasure d)) : ‖L v‖ = ‖v‖ := Lp.norm_compMeasurePreserving v hθ
  have hd (t : ℝ) : HasDerivAt (fun q => L (extensionLp d q))
      ((d.r*t) • L (integrandLp d t)) t := by
    convert! L.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_extensionLp d t) using 1
  refine ⟨L.continuous.comp (continuous_integrandLp d),
    L.continuous.comp (continuous_extensionLp d), hd, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    rw [← map_sub, extensionLp_sub, map_smul]
    congr 1
    simpa only [map_smul] using (L.intervalIntegral_comp_comm
      (f := fun t => t • integrandLp d t)
      ((continuous_id.smul (continuous_integrandLp d)).intervalIntegrable a b)).symm
  · rw [kernelLp_eq_integral,
      ← L.intervalIntegral_comp_comm ((continuous_integrandLp d).intervalIntegrable 0 d.b)]
  · simp only [extensionLp_terminal,map_zero]
  · simpa using (hd 0).deriv
  · intro t
    rw [hn]
    exact norm_integrandLp_le d t
  · intro t ht
    rw [hn]
    exact norm_extensionLp_le d ht
  · rw [hn]
    exact norm_kernelLp_le d

theorem initial_lift (d : Data ι) : Lift d id :=
  lift_of_measurePreserving d id (MeasurePreserving.id _)

theorem centering_measurePreserving [DecidableEq ι] (d : Data ι) (s : ℝ) (hs : 0 < s) (τ : ℝ) :
    MeasurePreserving (centering d s hs τ) (seedMeasure d) (seedMeasure d) := by
  exact Centering.sourceCenteringHomeomorph_measurePreserving d.hF d.hell d.hlo d.hup
    d.x d.hr d.hb d.hb1 d.hsmall hs τ

/-- Every deterministic positive or negative centering time has the same genuine
kernel L² supplier and constants, by actual stationary measure preservation. -/
theorem centering_lift [DecidableEq ι] (d : Data ι) (s : ℝ) (hs : 0 < s) (τ : ℝ) :
    Lift d (centering d s hs τ) :=
  lift_of_measurePreserving d _ (centering_measurePreserving d s hs τ)

end AcceleratedLogConcave.Numerics.KernelFlowLp
