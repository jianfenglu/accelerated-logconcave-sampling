import AcceleratedLogConcave.Numerics.KernelFlowLp
/-!
# Actual centering-time L² calculus

The literal complete source centering flow is lifted to one stationary phase
probability space. Initial second moments are derived from the actual Gaussian
probability transport. Its two-sided Grönwall bound supplies compact-time L²
domination; scalar pairings and Fubini then justify signed integral interchange.
The canonical position and momentum curves have ordinary L² derivatives, with
stationary dimension-sharp kernel and centered-mean bounds.

All times and source data here are deterministic. Representative agreement is
per time. No higher material derivatives, joint random-parameter selection,
remaining mean-equation suppliers, or compiler/coupling closure is asserted.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open AcceleratedLogConcave AcceleratedLogConcave.Conditional
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Numerics.CenteringFlowLp
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "P" => Centering.Phase E
abbrev Data := Numerics.KernelFlowLp.Data
abbrev seedMeasure (d : Data ι) := Numerics.KernelFlowLp.seedMeasure d
def phase (d : Data ι) (s : ℝ) (hs : 0 < s) (t : ℝ) (z : P) : P :=
  Numerics.KernelFlowLp.centering d s hs t z
def position (d : Data ι) (s : ℝ) (hs : 0 < s) (t : ℝ) (z : P) : E :=
  (phase d s hs t z).fst
def momentum (d : Data ι) (s : ℝ) (hs : 0 < s) (t : ℝ) (z : P) : E :=
  (phase d s hs t z).snd
def kernel (d : Data ι) (s : ℝ) (hs : 0 < s) (t : ℝ) (z : P) : E :=
  Numerics.KernelFlowLp.kernel d (phase d s hs t z)
def meanOffset (d : Data ι) : E := conditionalMean d.F d.x d.r 0 0
def centeredMean (d : Data ι) (s : ℝ) (hs : 0 < s) (t : ℝ) (z : P) : E :=
  conditionalMean d.F d.x d.r d.b (position d s hs t z) - meanOffset d
def alpha (d : Data ι) : ℝ := Real.exp 1 * (d.r*d.ell)
def growthC (d : Data ι) (s : ℝ) : ℝ := s⁻¹ * (2*alpha d + d.r*d.ell)
def growthD (d : Data ι) (s : ℝ) : ℝ :=
  s⁻¹ * ‖conditionalMean d.F d.x d.r d.b 0 - meanOffset d‖
def envelope (d : Data ι) (s T : ℝ) (z : P) : ℝ :=
  (‖z‖ + growthD d s*T) * Real.exp (growthC d s*T)

omit [DecidableEq ι] in
theorem position_preserving (d : Data ι) :
    MeasurePreserving (fun z : P => z.fst) (seedMeasure d)
      (interpolationLaw d.F d.x d.r d.b) := by
  refine ⟨(WithLp.prod_continuous_ofLp 2 E E).fst.measurable, ?_⟩
  rw [seedMeasure, Numerics.KernelFlowLp.seedMeasure, Kinetic.coupledPhaseMeasure,
    Measure.map_map (by fun_prop) (by fun_prop)]
  change Measure.map Prod.fst ((interpolationLaw d.F d.x d.r d.b).prod (stdGaussian E)) = _
  simp

theorem position_initial_memLp (d : Data ι) :
    MemLp (fun z : P => z.fst) 2 (seedMeasure d) := by
  let T := forwardProbabilityTransport d.hF d.hell d.hlo d.hup d.x d.hr d.hb d.hb1 0
  have hT : LipschitzWith ⟨Real.exp 1, (Real.exp_pos _).le⟩ T :=
    lipschitzWith_convexProbabilityFlow_exp_one d.hF d.hell d.hlo d.hup d.x d.hr d.hb
      d.hb1 d.hsmall (projIcc 0 d.b d.hb 0) ⟨d.b,d.hb,le_rfl⟩
  have hm := memLp_two_stdGaussian_of_lipschitz hT
  have hmp := forwardProbabilityTransport_measurePreserving d.hF d.hell d.hlo d.hup d.x
    d.hr d.hb d.hb1 (ρ := 0) ⟨le_rfl,d.hb⟩
  rw [interpolationLaw_zero d.hF d.hlo d.x d.r] at hmp
  have hi : MemLp (fun y : E => y) 2 (interpolationLaw d.F d.x d.r d.b) := by
    rw [← hmp.map_eq]
    exact T.measurableEmbedding.memLp_map_measure_iff.mpr hm
  exact hi.comp_measurePreserving (position_preserving d)

theorem phase_initial_memLp (d : Data ι) : MemLp (fun z : P => z) 2 (seedMeasure d) := by
  apply ((position_initial_memLp d).norm.add (Numerics.KernelFlowLp.momentum_memLp d).norm).mono'
    continuous_id.aestronglyMeasurable
  filter_upwards [] with z
  change ‖z‖ ≤ ‖z.fst‖ + ‖z.snd‖
  have h := WithLp.prod_norm_sq_eq_of_L2 z
  nlinarith [norm_nonneg z,norm_nonneg z.fst,norm_nonneg z.snd]

theorem phase_preserving (d : Data ι) (s : ℝ) (hs : 0 < s) (t : ℝ) :
    MeasurePreserving (phase d s hs t) (seedMeasure d) (seedMeasure d) :=
  Numerics.KernelFlowLp.centering_measurePreserving d s hs t

theorem position_memLp (d : Data ι) (s : ℝ) (hs : 0 < s) (t : ℝ) :
    MemLp (position d s hs t) 2 (seedMeasure d) :=
  (position_initial_memLp d).comp_measurePreserving (phase_preserving d s hs t)

theorem momentum_memLp (d : Data ι) (s : ℝ) (hs : 0 < s) (t : ℝ) :
    MemLp (momentum d s hs t) 2 (seedMeasure d) :=
  (Numerics.KernelFlowLp.momentum_memLp d).comp_measurePreserving (phase_preserving d s hs t)

theorem kernel_memLp (d : Data ι) (s : ℝ) (hs : 0 < s) (t : ℝ) :
    MemLp (kernel d s hs t) 2 (seedMeasure d) :=
  (Numerics.KernelFlowLp.kernel_memLp d).comp_measurePreserving (phase_preserving d s hs t)

theorem centeredMean_memLp (d : Data ι) (s : ℝ) (hs : 0 < s) (t : ℝ) :
    MemLp (centeredMean d s hs t) 2 (seedMeasure d) := by
  have hm := (memLp_two_conditionalMean d.hF d.hell d.hlo d.hup d.x d.hr d.hb d.hb1 d.hsmall).comp_measurePreserving (position_preserving d)
  exact (hm.sub (memLp_const (meanOffset d))).comp_measurePreserving (phase_preserving d s hs t)

theorem continuous_phase (d : Data ι) (s : ℝ) (hs : 0 < s) :
    Continuous (Function.uncurry (phase d s hs)) := by
  unfold phase Numerics.KernelFlowLp.centering Centering.sourceCenteringFlow Centering.centeringFlow
  exact Centering.completeCurve_joint_continuous _ _ _ _

theorem norm_phase_le_gronwall (d : Data ι) (s : ℝ) (hs : 0 < s) {T t : ℝ}
    (hT : 0 ≤ T) (ht : |t| ≤ T) (z : P) :
    ‖phase d s hs t z‖ ≤ gronwallBound ‖z‖ (growthC d s) (growthD d s) T := by
  unfold phase Numerics.KernelFlowLp.centering Centering.sourceCenteringFlow Centering.centeringFlow
    growthC growthD alpha meanOffset
  convert! Centering.completeCurve_norm_bound _ _ _ _ (norm_nonneg z) le_rfl hT ht using 1
  congr 2
  change 2*(Real.exp 1*(d.r*d.ell))+d.r*d.ell = 2*Real.exp 1*(d.r*d.ell)+d.r*d.ell
  ring

private theorem gronwall_le_exp {δ C D T : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) :
    gronwallBound δ C D T ≤ (δ+D*T)*Real.exp (C*T) := by
  by_cases h : C=0
  · simp [gronwallBound,h]
  · have hpos : 0 < C := lt_of_le_of_ne hC (Ne.symm h)
    rw [gronwallBound_of_K_ne_0 h]
    have he := Real.add_one_le_exp (-(C*T))
    have hh := mul_le_mul_of_nonneg_right he (Real.exp_pos (C*T)).le
    rw [← Real.exp_add] at hh
    have hzero : -(C*T)+(C*T)=0 := by ring
    rw [hzero,Real.exp_zero] at hh
    have he' : Real.exp (C*T)-1 ≤ C*T*Real.exp (C*T) := by nlinarith
    have hm := mul_le_mul_of_nonneg_left he' (div_nonneg hD hC)
    have hc : D/C*(C*T*Real.exp (C*T)) = D*T*Real.exp (C*T) := by field_simp
    rw [hc] at hm
    nlinarith

omit [DecidableEq ι] in
theorem growthC_nonneg (d : Data ι) {s : ℝ} (hs : 0 < s) : 0 ≤ growthC d s := by
  unfold growthC alpha
  have := d.hr
  have := d.hell
  positivity

omit [DecidableEq ι] in
theorem growthD_nonneg (d : Data ι) {s : ℝ} (hs : 0 < s) : 0 ≤ growthD d s := by
  unfold growthD
  positivity

theorem norm_phase_le_envelope (d : Data ι) (s : ℝ) (hs : 0 < s) {T t : ℝ}
    (hT : 0 ≤ T) (ht : |t| ≤ T) (z : P) :
    ‖phase d s hs t z‖ ≤ envelope d s T z :=
  (norm_phase_le_gronwall d s hs hT ht z).trans
    (gronwall_le_exp (growthC_nonneg d hs) (growthD_nonneg d hs))

theorem envelope_memLp (d : Data ι) (s T : ℝ) :
    MemLp (envelope d s T) 2 (seedMeasure d) := by
  change MemLp (fun z => (‖z‖+growthD d s*T)*Real.exp (growthC d s*T)) 2 _
  convert! (((phase_initial_memLp d).norm.add (memLp_const (growthD d s*T))).const_mul
      (Real.exp (growthC d s*T))) using 1
  funext z
  simp only [Pi.add_apply]
  ring

omit [DecidableEq ι] in
theorem norm_literal_kernel_le (d : Data ι) (z : P) :
    ‖Numerics.KernelFlowLp.kernel d z‖ ≤ alpha d*d.b*‖z.snd‖ := by
  rw [Numerics.KernelFlowLp.kernel_eq_integral]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := d.b) (C := alpha d*‖z.snd‖)
    (fun t _ => Numerics.KernelFlowLp.norm_integrand_le d t z)
  simpa only [sub_zero,abs_of_nonneg d.hb,alpha,mul_comm,mul_left_comm,mul_assoc] using h

theorem norm_kernel_le_envelope (d : Data ι) (s : ℝ) (hs : 0 < s) {T t : ℝ}
    (hT : 0 ≤ T) (ht : |t| ≤ T) (z : P) :
    ‖kernel d s hs t z‖ ≤ alpha d*d.b*envelope d s T z := by
  have ha : 0 ≤ alpha d*d.b := by
    unfold alpha
    have := d.hr; have := d.hell; have := d.hb; positivity
  exact (norm_literal_kernel_le d _).trans (mul_le_mul_of_nonneg_left
    ((WithLp.norm_snd_le E _).trans (norm_phase_le_envelope d s hs hT ht z)) ha)

omit [DecidableEq ι] in
theorem norm_centeredMean_le (d : Data ι) (y : E) :
    ‖conditionalMean d.F d.x d.r d.b y-meanOffset d‖ ≤
      d.r*d.ell*‖y‖ + ‖conditionalMean d.F d.x d.r d.b 0-meanOffset d‖ := by
  have h := (lipschitzWith_conditionalMean d.hF d.hell d.hlo d.hup d.x d.hr
    (by linarith [d.hb]) d.hb1).dist_le_mul y (0:E)
  simp only [dist_eq_norm,sub_zero] at h
  change ‖conditionalMean d.F d.x d.r d.b y - conditionalMean d.F d.x d.r d.b 0‖ ≤ d.r*d.ell*‖y‖ at h
  have hb := norm_sub_le_norm_sub_add_norm_sub (conditionalMean d.F d.x d.r d.b y)
    (conditionalMean d.F d.x d.r d.b 0) (meanOffset d)
  linarith

theorem norm_centeredMean_le_envelope (d : Data ι) (s : ℝ) (hs : 0 < s) {T t : ℝ}
    (hT : 0 ≤ T) (ht : |t| ≤ T) (z : P) :
    ‖centeredMean d s hs t z‖ ≤ d.r*d.ell*envelope d s T z +
      ‖conditionalMean d.F d.x d.r d.b 0-meanOffset d‖ := by
  have hf := (WithLp.norm_fst_le E (phase d s hs t z)).trans
    (norm_phase_le_envelope d s hs hT ht z)
  have hh := mul_le_mul_of_nonneg_left hf (mul_nonneg d.hr.le d.hell)
  have hm := norm_centeredMean_le d (position d s hs t z)
  change ‖centeredMean d s hs t z‖ ≤ _ at hm
  change d.r*d.ell*‖position d s hs t z‖ ≤ _ at hh
  linarith

theorem continuous_position (d : Data ι) (s : ℝ) (hs : 0 < s) :
    Continuous (Function.uncurry (position d s hs)) :=
  (WithLp.prod_continuous_ofLp 2 E E).fst.comp (continuous_phase d s hs)
theorem continuous_momentum (d : Data ι) (s : ℝ) (hs : 0 < s) :
    Continuous (Function.uncurry (momentum d s hs)) :=
  (WithLp.prod_continuous_ofLp 2 E E).snd.comp (continuous_phase d s hs)
theorem continuous_kernel (d : Data ι) (s : ℝ) (hs : 0 < s) :
    Continuous (Function.uncurry (kernel d s hs)) :=
  (((Centering.sourceKernel_contDiff_one d.hF d.hell d.hlo d.hup d.x d.hr d.hb d.hb1
    d.hsmall).continuous).comp (continuous_position d s hs)).clm_apply (continuous_momentum d s hs)
theorem continuous_centeredMean (d : Data ι) (s : ℝ) (hs : 0 < s) :
    Continuous (Function.uncurry (centeredMean d s hs)) :=
  ((contDiff_one_conditionalMean d.hF d.hlo d.hup d.x d.r
    (by linarith [d.hb]) d.hb1).continuous.comp (continuous_position d s hs)).sub continuous_const

theorem hasDerivAt_position (d : Data ι) (s : ℝ) (hs : 0 < s) (t : ℝ) (z : P) :
    HasDerivAt (fun q => position d s hs q z) (-s⁻¹ • kernel d s hs t z) t := by
  have h := Centering.sourceCenteringFlow_deriv d.hF d.hell d.hlo d.hup d.x d.hr d.hb
    d.hb1 d.hsmall hs z t
  convert! (WithLp.fstL 2 ℝ E E).hasFDerivAt.comp_hasDerivAt t h using 1
  simp [phase,kernel,Numerics.KernelFlowLp.centering,Numerics.KernelFlowLp.kernel,
    Centering.velocity,WithLp.fstL,neg_smul]

theorem hasDerivAt_momentum (d : Data ι) (s : ℝ) (hs : 0 < s) (t : ℝ) (z : P) :
    HasDerivAt (fun q => momentum d s hs q z) (s⁻¹ • centeredMean d s hs t z) t := by
  have h := Centering.sourceCenteringFlow_deriv d.hF d.hell d.hlo d.hup d.x d.hr d.hb
    d.hb1 d.hsmall hs z t
  convert! (WithLp.sndL 2 ℝ E E).hasFDerivAt.comp_hasDerivAt t h using 1

theorem position_sub (d : Data ι) (s : ℝ) (hs : 0 < s) (a b : ℝ) (z : P) :
    position d s hs b z-position d s hs a z = -s⁻¹ • ∫ t in a..b, kernel d s hs t z := by
  have hc : Continuous (fun t => kernel d s hs t z) := by
    simpa only [Function.comp_def,Function.uncurry_def,id_eq] using
      (continuous_kernel d s hs).comp (continuous_id.prodMk continuous_const)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_position d s hs t z) ((hc.const_smul (-s⁻¹)).intervalIntegrable a b)
  simpa only [intervalIntegral.integral_smul] using hi.symm

theorem momentum_sub (d : Data ι) (s : ℝ) (hs : 0 < s) (a b : ℝ) (z : P) :
    momentum d s hs b z-momentum d s hs a z = s⁻¹ • ∫ t in a..b, centeredMean d s hs t z := by
  have hc : Continuous (fun t => centeredMean d s hs t z) := by
    simpa only [Function.comp_def,Function.uncurry_def,id_eq] using
      (continuous_centeredMean d s hs).comp (continuous_id.prodMk continuous_const)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_momentum d s hs t z) ((hc.const_smul (s⁻¹)).intervalIntegrable a b)
  simpa only [intervalIntegral.integral_smul] using hi.symm

section LiftHelpers
variable {μ : Measure (Centering.Phase (EuclideanSpace ℝ ι))} [IsFiniteMeasure μ]
omit [DecidableEq ι] [IsFiniteMeasure μ] in
private theorem norm_sq_toLp {g : P → E}
    (hg : MemLp g 2 μ) :
    ‖hg.toLp g‖ ^ 2 = ∫ p, ‖g p‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with p hp
  rw [hp, real_inner_self_eq_norm_sq]

omit [DecidableEq ι] [IsFiniteMeasure μ] in
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

omit [DecidableEq ι] in
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

section LocalLifts
variable {μ : Measure (Centering.Phase (EuclideanSpace ℝ ι))} [IsFiniteMeasure μ]
omit [DecidableEq ι] [IsFiniteMeasure μ] in
private theorem continuous_toLp_of_compact_domination
    (g : ℝ → P → E) (hg : Continuous (Function.uncurry g))
    (B : ℝ → P → ℝ) (hB : ∀ T, 0 ≤ T → MemLp (B T) 2 μ)
    (hbound : ∀ T, 0 ≤ T → ∀ t, |t| ≤ T → ∀ z, ‖g t z‖ ≤ B T z)
    (hm : ∀ t, MemLp (g t) 2 μ) : Continuous (fun t => (hm t).toLp (g t)) := by
  rw [continuous_iff_continuousAt]
  intro τ
  let T := |τ|+1
  have hT : 0 ≤ T := by dsimp [T]; positivity
  let clip (t : ℝ) : ℝ := (projIcc (-T) T (by linarith) t : ℝ)
  have hclip (t : ℝ) : |clip t| ≤ T := abs_le.mpr (projIcc (-T) T (by linarith) t).property
  have hceq (t : ℝ) (ht : t ∈ Icc (-T) T) : clip t = t := by
    simp only [clip,projIcc_of_mem (by linarith) ht]
  let gbar (t : ℝ) (z : P) := g (clip t) z
  have hclipc : Continuous clip := continuous_subtype_val.comp (continuous_projIcc (h := by linarith))
  have hc : Continuous (Function.uncurry gbar) :=
    hg.comp ((hclipc.comp continuous_fst).prodMk continuous_snd)
  have hh := continuous_toLp_of_dominated gbar hc (B T) (hB T hT)
    (fun t z => hbound T hT (clip t) (hclip t) z) (fun t => hm (clip t))
  apply hh.continuousAt.congr
  have hτ : τ ∈ Ioo (-T) T := by
    dsimp [T]; constructor <;> linarith [le_abs_self τ,neg_abs_le τ]
  filter_upwards [isOpen_Ioo.mem_nhds hτ] with t ht
  simp only [gbar,hceq t ⟨ht.1.le,ht.2.le⟩]

omit [DecidableEq ι] in
private theorem toLp_intervalIntegral_of_compact_domination
    (g : ℝ → P → E) (hg : Continuous (Function.uncurry g))
    (B : ℝ → P → ℝ) (hB : ∀ T, 0 ≤ T → MemLp (B T) 2 μ)
    (hbound : ∀ T, 0 ≤ T → ∀ t, |t| ≤ T → ∀ z, ‖g t z‖ ≤ B T z)
    (hm : ∀ t, MemLp (g t) 2 μ) (a b : ℝ) :
    ∃ hi : MemLp (fun z => ∫ t in a..b, g t z) 2 μ,
      hi.toLp _ = ∫ t in a..b, (hm t).toLp (g t) := by
  let T := |a|+|b|
  have hT : 0 ≤ T := add_nonneg (abs_nonneg _) (abs_nonneg _)
  let clip (t : ℝ) : ℝ := (projIcc (-T) T (by linarith) t : ℝ)
  have hclip (t : ℝ) : |clip t| ≤ T := abs_le.mpr (projIcc (-T) T (by linarith) t).property
  have hceq (t : ℝ) (ht : t ∈ uIcc a b) : clip t = t := by
    have hmin : -T ≤ min a b := by dsimp [T]; exact le_min (by linarith [neg_abs_le a,abs_nonneg b]) (by linarith [neg_abs_le b,abs_nonneg a])
    have hmax : max a b ≤ T := by dsimp [T]; exact max_le (by linarith [le_abs_self a,abs_nonneg b]) (by linarith [le_abs_self b,abs_nonneg a])
    simp only [clip,projIcc_of_mem (by linarith) ⟨hmin.trans ht.1,ht.2.trans hmax⟩]
  let gbar (t : ℝ) (z : P) := g (clip t) z
  have hclipc : Continuous clip := continuous_subtype_val.comp (continuous_projIcc (h := by linarith))
  have hc : Continuous (Function.uncurry gbar) :=
    hg.comp ((hclipc.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨hi,heq⟩ := toLp_intervalIntegral_of_dominated gbar hc (B T) (hB T hT)
    (fun t z => hbound T hT (clip t) (hclip t) z) (fun t => hm (clip t)) a b
  have he (z : P) : (∫ t in a..b, gbar t z) = ∫ t in a..b, g t z := by
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [gbar,hceq t ht]
  have hfun : (fun z => ∫ t in a..b, gbar t z) = (fun z => ∫ t in a..b, g t z) := funext he
  have hi2 : MemLp (fun z => ∫ t in a..b, g t z) 2 μ := hfun ▸ hi
  refine ⟨hi2, (MemLp.toLp_congr hi2 hi (Filter.Eventually.of_forall (fun z => (he z).symm))).trans (heq.trans ?_)⟩
  apply intervalIntegral.integral_congr
  intro t ht
  simp only [gbar,hceq t ht]
end LocalLifts

def positionLp (d : Data ι) (s : ℝ) (hs : 0 < s) (t : ℝ) : Lp E 2 (seedMeasure d) :=
  (position_memLp d s hs t).toLp _
def momentumLp (d : Data ι) (s : ℝ) (hs : 0 < s) (t : ℝ) : Lp E 2 (seedMeasure d) :=
  (momentum_memLp d s hs t).toLp _
def kernelLp (d : Data ι) (s : ℝ) (hs : 0 < s) (t : ℝ) : Lp E 2 (seedMeasure d) :=
  (kernel_memLp d s hs t).toLp _
def centeredMeanLp (d : Data ι) (s : ℝ) (hs : 0 < s) (t : ℝ) : Lp E 2 (seedMeasure d) :=
  (centeredMean_memLp d s hs t).toLp _

theorem continuous_positionLp (d : Data ι) (s : ℝ) (hs : 0 < s) :
    Continuous (positionLp d s hs) := by
  apply continuous_toLp_of_compact_domination _ (continuous_position d s hs) (envelope d s)
    (fun T _ => envelope_memLp d s T) _ (position_memLp d s hs)
  intro T hT t ht z
  exact (WithLp.norm_fst_le E _).trans (norm_phase_le_envelope d s hs hT ht z)

theorem continuous_momentumLp (d : Data ι) (s : ℝ) (hs : 0 < s) :
    Continuous (momentumLp d s hs) := by
  apply continuous_toLp_of_compact_domination _ (continuous_momentum d s hs) (envelope d s)
    (fun T _ => envelope_memLp d s T) _ (momentum_memLp d s hs)
  intro T hT t ht z
  exact (WithLp.norm_snd_le E _).trans (norm_phase_le_envelope d s hs hT ht z)

theorem continuous_kernelLp (d : Data ι) (s : ℝ) (hs : 0 < s) :
    Continuous (kernelLp d s hs) :=
  continuous_toLp_of_compact_domination _ (continuous_kernel d s hs)
    (fun T z => alpha d*d.b*envelope d s T z)
    (fun T _ => (envelope_memLp d s T).const_mul _) (fun _ hT _ ht => norm_kernel_le_envelope d s hs hT ht)
    (kernel_memLp d s hs)

theorem continuous_centeredMeanLp (d : Data ι) (s : ℝ) (hs : 0 < s) :
    Continuous (centeredMeanLp d s hs) :=
  continuous_toLp_of_compact_domination _ (continuous_centeredMean d s hs)
    (fun T z => d.r*d.ell*envelope d s T z +
      ‖conditionalMean d.F d.x d.r d.b 0-meanOffset d‖)
    (fun T _ => ((envelope_memLp d s T).const_mul _).add (memLp_const _))
    (fun _ hT _ ht => norm_centeredMean_le_envelope d s hs hT ht) (centeredMean_memLp d s hs)

private theorem kernel_integral_lift (d : Data ι) (s : ℝ) (hs : 0 < s) (a b : ℝ) :
    ∃ hi : MemLp (fun z => ∫ t in a..b, kernel d s hs t z) 2 (seedMeasure d),
      hi.toLp _ = ∫ t in a..b, kernelLp d s hs t :=
  toLp_intervalIntegral_of_compact_domination _ (continuous_kernel d s hs)
    (fun T z => alpha d*d.b*envelope d s T z)
    (fun T _ => (envelope_memLp d s T).const_mul _) (fun _ hT _ ht => norm_kernel_le_envelope d s hs hT ht)
    (kernel_memLp d s hs) a b

private theorem centeredMean_integral_lift (d : Data ι) (s : ℝ) (hs : 0 < s) (a b : ℝ) :
    ∃ hi : MemLp (fun z => ∫ t in a..b, centeredMean d s hs t z) 2 (seedMeasure d),
      hi.toLp _ = ∫ t in a..b, centeredMeanLp d s hs t :=
  toLp_intervalIntegral_of_compact_domination _ (continuous_centeredMean d s hs)
    (fun T z => d.r*d.ell*envelope d s T z +
      ‖conditionalMean d.F d.x d.r d.b 0-meanOffset d‖)
    (fun T _ => ((envelope_memLp d s T).const_mul _).add (memLp_const _))
    (fun _ hT _ ht => norm_centeredMean_le_envelope d s hs hT ht) (centeredMean_memLp d s hs) a b

theorem positionLp_sub (d : Data ι) (s : ℝ) (hs : 0 < s) (a b : ℝ) :
    positionLp d s hs b-positionLp d s hs a = -s⁻¹ • ∫ t in a..b, kernelLp d s hs t := by
  obtain ⟨hi,he⟩ := kernel_integral_lift d s hs a b
  rw [← he]
  change (position_memLp d s hs b).toLp _-(position_memLp d s hs a).toLp _ = _
  rw [← MemLp.toLp_sub, ← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  filter_upwards [] with z
  exact position_sub d s hs a b z

theorem momentumLp_sub (d : Data ι) (s : ℝ) (hs : 0 < s) (a b : ℝ) :
    momentumLp d s hs b-momentumLp d s hs a = s⁻¹ • ∫ t in a..b, centeredMeanLp d s hs t := by
  obtain ⟨hi,he⟩ := centeredMean_integral_lift d s hs a b
  rw [← he]
  change (momentum_memLp d s hs b).toLp _-(momentum_memLp d s hs a).toLp _ = _
  rw [← MemLp.toLp_sub, ← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  filter_upwards [] with z
  exact momentum_sub d s hs a b z

theorem hasDerivAt_positionLp (d : Data ι) (s : ℝ) (hs : 0 < s) (t : ℝ) :
    HasDerivAt (positionLp d s hs) (-s⁻¹ • kernelLp d s hs t) t := by
  have he : positionLp d s hs = fun q => positionLp d s hs 0 +
      -s⁻¹ • ∫ u in 0..q, kernelLp d s hs u := by
    funext q
    have hh := positionLp_sub d s hs 0 q
    exact (sub_eq_iff_eq_add.mp hh).trans (add_comm _ _)
  rw [he]
  have hc := continuous_kernelLp d s hs
  have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  convert! (hd.const_smul (-s⁻¹)).const_add (positionLp d s hs 0) using 1

theorem hasDerivAt_momentumLp (d : Data ι) (s : ℝ) (hs : 0 < s) (t : ℝ) :
    HasDerivAt (momentumLp d s hs) (s⁻¹ • centeredMeanLp d s hs t) t := by
  have he : momentumLp d s hs = fun q => momentumLp d s hs 0 +
      s⁻¹ • ∫ u in 0..q, centeredMeanLp d s hs u := by
    funext q
    have hh := momentumLp_sub d s hs 0 q
    exact (sub_eq_iff_eq_add.mp hh).trans (add_comm _ _)
  rw [he]
  have hc := continuous_centeredMeanLp d s hs
  have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  convert! (hd.const_smul s⁻¹).const_add (momentumLp d s hs 0) using 1

theorem norm_kernelLp_le (d : Data ι) (s : ℝ) (hs : 0 < s) (t : ℝ) :
    ‖kernelLp d s hs t‖ ≤ alpha d*d.b*Real.sqrt (Module.finrank ℝ E) := by
  change ‖Lp.compMeasurePreserving (phase d s hs t) (phase_preserving d s hs t)
    (Numerics.KernelFlowLp.kernelLp d)‖ ≤ _
  rw [Lp.norm_compMeasurePreserving]
  exact Numerics.KernelFlowLp.norm_kernelLp_le d

theorem norm_centeredMeanLp_le (d : Data ι) (s : ℝ) (hs : 0 < s) (t : ℝ) :
    ‖centeredMeanLp d s hs t‖ ≤ alpha d*Real.sqrt (Module.finrank ℝ E) := by
  let := interpolationLaw_isProbabilityMeasure d.hF d.hlo d.x d.r d.b
  let m (y : E) := conditionalMean d.F d.x d.r d.b y - meanOffset d
  have hm : MemLp m 2 (interpolationLaw d.F d.x d.r d.b) :=
    (memLp_two_conditionalMean d.hF d.hell d.hlo d.hup d.x d.hr d.hb d.hb1 d.hsmall).sub
      (memLp_const _)
  have hmp := (position_preserving d).comp (phase_preserving d s hs t)
  have hn : ‖centeredMeanLp d s hs t‖ = ‖hm.toLp m‖ :=
    Lp.norm_compMeasurePreserving (hm.toLp m) hmp
  rw [hn]
  have hsq : ‖hm.toLp m‖^2 = ∫ y, ‖m y‖^2 ∂interpolationLaw d.F d.x d.r d.b := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hm.coeFn_toLp] with y hy
    rw [hy, real_inner_self_eq_norm_sq]
  have hb : (∫ y, ‖m y‖^2 ∂interpolationLaw d.F d.x d.r d.b) ≤
      (alpha d)^2*(Module.finrank ℝ E : ℝ) := by
    simpa only [m,meanOffset,conditionalMean_zero,alpha] using
      integral_conditionalMean_centered_norm_sq_le d.hF d.hell d.hlo d.hup
        d.x d.hr d.hb d.hb1 d.hsmall
  have hdim := Real.sq_sqrt (Nat.cast_nonneg (Module.finrank ℝ E))
  have ha : 0 ≤ alpha d := by unfold alpha; have := d.hr; have := d.hell; positivity
  have hr : 0 ≤ alpha d*Real.sqrt (Module.finrank ℝ E) := mul_nonneg ha (Real.sqrt_nonneg _)
  nlinarith [norm_nonneg (hm.toLp m)]

theorem norm_positionLp_sub_le (d : Data ι) (s : ℝ) (hs : 0 < s) (a b : ℝ) :
    ‖positionLp d s hs b-positionLp d s hs a‖ ≤
      |b-a| *(s⁻¹*alpha d*d.b*Real.sqrt (Module.finrank ℝ E)) := by
  rw [positionLp_sub,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos (inv_pos.mpr hs)]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (fun t _ => norm_kernelLp_le d s hs t)
  have hi := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hs.le)
  nlinarith

theorem norm_momentumLp_sub_le (d : Data ι) (s : ℝ) (hs : 0 < s) (a b : ℝ) :
    ‖momentumLp d s hs b-momentumLp d s hs a‖ ≤
      |b-a| *(s⁻¹*alpha d*Real.sqrt (Module.finrank ℝ E)) := by
  rw [momentumLp_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs)]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (fun t _ => norm_centeredMeanLp_le d s hs t)
  have hi := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hs.le)
  nlinarith

/-- Initial phase moments are consequences of the Gaussian probability transport. -/
theorem initial_moments (d : Data ι) :
    MemLp (fun z : P => z) 2 (seedMeasure d) ∧
    MemLp (fun z : P => z.fst) 2 (seedMeasure d) ∧
    MemLp (fun z : P => z.snd) 2 (seedMeasure d) :=
  ⟨phase_initial_memLp d,position_initial_memLp d,Numerics.KernelFlowLp.momentum_memLp d⟩

/-- Literal ordinary-time L² calculus, all on the same stationary seed space. -/
def Lift (d : Data ι) (s : ℝ) (hs : 0 < s) : Prop :=
  Continuous (positionLp d s hs) ∧ Continuous (momentumLp d s hs) ∧
  Continuous (kernelLp d s hs) ∧ Continuous (centeredMeanLp d s hs) ∧
  (∀ t, HasDerivAt (positionLp d s hs) (-s⁻¹ • kernelLp d s hs t) t) ∧
  (∀ t, HasDerivAt (momentumLp d s hs) (s⁻¹ • centeredMeanLp d s hs t) t) ∧
  (∀ a b, positionLp d s hs b-positionLp d s hs a =
    -s⁻¹ • ∫ t in a..b, kernelLp d s hs t) ∧
  (∀ a b, momentumLp d s hs b-momentumLp d s hs a =
    s⁻¹ • ∫ t in a..b, centeredMeanLp d s hs t) ∧
  (∀ t, ‖kernelLp d s hs t‖ ≤ alpha d*d.b*Real.sqrt (Module.finrank ℝ E)) ∧
  (∀ t, ‖centeredMeanLp d s hs t‖ ≤ alpha d*Real.sqrt (Module.finrank ℝ E)) ∧
  (∀ a b, ‖positionLp d s hs b-positionLp d s hs a‖ ≤
    |b-a| *(s⁻¹*alpha d*d.b*Real.sqrt (Module.finrank ℝ E))) ∧
  (∀ a b, ‖momentumLp d s hs b-momentumLp d s hs a‖ ≤
    |b-a| *(s⁻¹*alpha d*Real.sqrt (Module.finrank ℝ E)))

theorem lift (d : Data ι) (s : ℝ) (hs : 0 < s) : Lift d s hs :=
  ⟨continuous_positionLp d s hs,continuous_momentumLp d s hs,
    continuous_kernelLp d s hs,continuous_centeredMeanLp d s hs,
    hasDerivAt_positionLp d s hs,hasDerivAt_momentumLp d s hs,
    positionLp_sub d s hs,momentumLp_sub d s hs,
    norm_kernelLp_le d s hs,norm_centeredMeanLp_le d s hs,
    norm_positionLp_sub_le d s hs,norm_momentumLp_sub_le d s hs⟩

/-- Canonical representatives agree with the literal curve at each deterministic time. -/
theorem representatives (d : Data ι) (s : ℝ) (hs : 0 < s) (t : ℝ) :
    (positionLp d s hs t : P → E) =ᵐ[seedMeasure d] position d s hs t ∧
    (momentumLp d s hs t : P → E) =ᵐ[seedMeasure d] momentum d s hs t ∧
    (kernelLp d s hs t : P → E) =ᵐ[seedMeasure d] kernel d s hs t ∧
    (centeredMeanLp d s hs t : P → E) =ᵐ[seedMeasure d] centeredMean d s hs t :=
  ⟨(position_memLp d s hs t).coeFn_toLp,(momentum_memLp d s hs t).coeFn_toLp,
    (kernel_memLp d s hs t).coeFn_toLp,(centeredMean_memLp d s hs t).coeFn_toLp⟩

@[simp] theorem phase_initial (d : Data ι) (s : ℝ) (hs : 0 < s) (z : P) :
    phase d s hs 0 z = z :=
  Centering.sourceCenteringFlow_initial d.hF d.hell d.hlo d.hup d.x d.hr d.hb d.hb1 d.hsmall hs z
@[simp] theorem position_initial (d : Data ι) (s : ℝ) (hs : 0 < s) (z : P) :
    position d s hs 0 z = z.fst := by simp [position]
@[simp] theorem momentum_initial (d : Data ι) (s : ℝ) (hs : 0 < s) (z : P) :
    momentum d s hs 0 z = z.snd := by simp [momentum]


end AcceleratedLogConcave.Numerics.CenteringFlowLp
