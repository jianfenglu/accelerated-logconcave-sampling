import AcceleratedLogConcave.Numerics.SmoothConditional

/-! Fixed-angle forward smoothing of the literal original-data receiver.
The actual arbitrary-start flow is rewound to zero before using the enlarged
slab jet supplier. No independence or additional moment hypothesis is used. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Numerics.MeanResidualBridge
open MeanFlowLp AffineGraph AffineGraph.MeanGeometry ConditionalSmoothing
open Analysis.PositiveVarianceSlab
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

private theorem forward_moment_affine
    {Ω X Y : Type*} [MeasurableSpace Ω] [NormedAddCommGroup X] [NormedAddCommGroup Y]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → X} {g : Ω → Y}
    (hf : AEStronglyMeasurable f μ) (n : ℕ)
    (hg : Integrable (fun w => ‖g w‖^n) μ)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hb : ∀ w, ‖f w‖ ≤ A+B*‖g w‖) :
    Integrable (fun w => ‖f w‖^n) μ := by
  apply (((integrable_const (A^n)).add (hg.const_mul (B^n))).const_mul (2^(n-1))).mono'
    (hf.norm.pow n)
  filter_upwards [] with w
  simp only [Pi.pow_apply, Pi.add_apply, Real.norm_eq_abs]
  rw [abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  calc
    _ ≤ (A+B*‖g w‖)^n := pow_le_pow_left₀ (norm_nonneg _) (hb w) n
    _ ≤ 2^(n-1)*(A^n+(B*‖g w‖)^n) :=
      add_pow_le hA (mul_nonneg hB (norm_nonneg _)) n
    _ = _ := by simp only [mul_pow]

omit [DecidableEq ι] in
private theorem forward_moment_add {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f g : Ω → E} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (n : ℕ)
    (hfn : Integrable (fun w => ‖f w‖^n) μ)
    (hgn : Integrable (fun w => ‖g w‖^n) μ) :
    Integrable (fun w => ‖f w+g w‖^n) μ := by
  apply ((hfn.add hgn).const_mul (2^(n-1))).mono' ((hf.add hg).norm.pow n)
  filter_upwards [] with w
  simp only [Pi.pow_apply, Pi.add_apply, Real.norm_eq_abs]
  rw [abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) n).trans
    (add_pow_le (norm_nonneg _) (norm_nonneg _) n)

omit [DecidableEq ι] in
private theorem forward_moment_smul {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → E} (a : ℝ) (n : ℕ)
    (hf : Integrable (fun w => ‖f w‖^n) μ) :
    Integrable (fun w => ‖a • f w‖^n) μ := by
  simpa only [norm_smul, Real.norm_eq_abs, mul_pow] using hf.const_mul (|a|^n)

variable (d : Data ι m)

theorem smoothForward_seedScore_continuous (t : ℝ) : Continuous (score d t) :=
  (WithLp.prod_continuous_ofLp 2 E E).snd.comp
    ((CenteringFlowLp.continuous_phase (kernelData d) _ _).comp
      (continuous_const.prodMk continuous_fst))

theorem smoothForward_seedScore_moment (t : ℝ) (n : ℕ) :
    Integrable (fun w => ‖score d t w‖^n) (seedMeasure d) := by
  have h : Integrable (fun y : E => ‖y‖^n) (stdGaussian E) := by
    simpa only [id_eq] using
      (IsGaussian.memLp_id (stdGaussian E) n (by simp)).integrable_norm_pow'
  exact ((KernelFlowLp.momentum_preserving (kernelData d)).comp
    (kernel_phase_preserving d t)).integrable_comp_of_integrable h

theorem smoothForward_seedConditional_continuous (j : Fin m) (k : d.G.Kernel) (t : ℝ) :
    Continuous (conditional d j k t) := by
  change Continuous (fun w : Seed d => SamplingCenterLp.path (conditionalData d k)
    (conditionalCenter d j k w) t (w.2 j k))
  exact (SamplingCenterLp.continuous_path (conditionalData d k)).comp
    (f := fun w : Seed d => (t, conditionalInput d j k w))
    (continuous_const.prodMk (continuous_conditionalInput d j k))

theorem smoothForward_seedConditional_moment (j : Fin m) (k : d.G.Kernel) (n : ℕ) :
    Integrable (fun w => ‖conditional d j k conditionalEnd w‖^n) (seedMeasure d) := by
  obtain ⟨C,hC,h⟩ := exists_jointPath_linear_bound (conditionalData d k)
  apply forward_moment_affine (smoothForward_seedConditional_continuous d j k _).aestronglyMeasurable n
    (conditionalInput_integrable_norm_pow d j k n) hC hC
  intro w
  have he := jointPath_snd_eq_source (conditionalData d k)
    (conditionalCenter d j k w) (w.2 j k) ⟨conditionalEnd_pos.le,le_rfl⟩
  change ‖SamplingCenterLp.path (conditionalData d k) (conditionalCenter d j k w)
    conditionalEnd (w.2 j k)‖ ≤ _
  rw [← he]
  exact (norm_snd_le _).trans ((h conditionalEnd (conditionalInput d j k w)).trans_eq (by ring))

theorem smoothForward_seedRotation_continuous (j : Fin m) (k : d.G.Kernel) (z : ℝ) :
    Continuous (rotation d j k z) := by
  let B := backward d j (d.G.rho k)
  let H := fun w => d.G.rho k • B w +
    (Real.sqrt (d.G.variance k)/conditionalEnd) • conditional d j k conditionalEnd w
  let mid := fun w => (d.G.rho k/(1+(d.G.rho k)^2)) • (H w+d.G.rho k • B w)
  have cB : Continuous B := continuous_seedBackward d j _
  have cH : Continuous H := (cB.const_smul (d.G.rho k)).add
    ((smoothForward_seedConditional_continuous d j k conditionalEnd).const_smul
      (Real.sqrt (d.G.variance k)/conditionalEnd))
  have cm : Continuous mid := (cH.add (cB.const_smul (d.G.rho k))).const_smul
    (d.G.rho k/(1+(d.G.rho k)^2))
  exact (cm.add ((cB.sub cm).const_smul (Real.cos (z/d.G.rotationScale k)))).add
    ((smoothForward_seedScore_continuous d (centerNode j)).const_smul
      (d.G.rotationScale k*Real.sin (z/d.G.rotationScale k)))

theorem smoothForward_seedRotation_moment (j : Fin m) (k : d.G.Kernel) (z : ℝ) (n : ℕ) :
    Integrable (fun w => ‖rotation d j k z w‖^n) (seedMeasure d) := by
  let B := backward d j (d.G.rho k)
  let H := fun w => d.G.rho k • B w +
    (Real.sqrt (d.G.variance k)/conditionalEnd) • conditional d j k conditionalEnd w
  let mid := fun w => (d.G.rho k/(1+(d.G.rho k)^2)) • (H w+d.G.rho k • B w)
  have cB : Continuous B := continuous_seedBackward d j _
  have cH : Continuous H := (cB.const_smul (d.G.rho k)).add
    ((smoothForward_seedConditional_continuous d j k conditionalEnd).const_smul
      (Real.sqrt (d.G.variance k)/conditionalEnd))
  have cm : Continuous mid := (cH.add (cB.const_smul (d.G.rho k))).const_smul
    (d.G.rho k/(1+(d.G.rho k)^2))
  have hB : Integrable (fun w => ‖B w‖^n) (seedMeasure d) :=
    seedBackward_integrable_norm_pow d j (d.G.rho k) n
  have hH : Integrable (fun w => ‖H w‖^n) (seedMeasure d) :=
    forward_moment_add (cB.const_smul (d.G.rho k)).aestronglyMeasurable
      ((smoothForward_seedConditional_continuous d j k conditionalEnd).const_smul
        (Real.sqrt (d.G.variance k)/conditionalEnd)).aestronglyMeasurable n
      (forward_moment_smul (d.G.rho k) n hB)
      (forward_moment_smul (Real.sqrt (d.G.variance k)/conditionalEnd) n
        (smoothForward_seedConditional_moment d j k n))
  have hm : Integrable (fun w => ‖mid w‖^n) (seedMeasure d) :=
    forward_moment_smul (d.G.rho k/(1+(d.G.rho k)^2)) n
      (forward_moment_add cH.aestronglyMeasurable
        (cB.const_smul (d.G.rho k)).aestronglyMeasurable n hH
        (forward_moment_smul (d.G.rho k) n hB))
  have hsub : Integrable (fun w => ‖B w-mid w‖^n) (seedMeasure d) := by
    simpa only [neg_one_smul, sub_eq_add_neg, Pi.neg_apply] using
      forward_moment_add cB.aestronglyMeasurable (cm.const_smul (-1 : ℝ)).aestronglyMeasurable n
        hB (forward_moment_smul (-1) n hm)
  have hfirst : Integrable
      (fun w => ‖mid w + Real.cos (z/d.G.rotationScale k) • (B w-mid w)‖^n)
      (seedMeasure d) :=
    forward_moment_add cm.aestronglyMeasurable
      ((cB.sub cm).const_smul (Real.cos (z/d.G.rotationScale k))).aestronglyMeasurable n
      hm (forward_moment_smul (Real.cos (z/d.G.rotationScale k)) n hsub)
  exact forward_moment_add
    (cm.add ((cB.sub cm).const_smul (Real.cos (z/d.G.rotationScale k)))).aestronglyMeasurable
    ((smoothForward_seedScore_continuous d (centerNode j)).const_smul
      (d.G.rotationScale k*Real.sin (z/d.G.rotationScale k))).aestronglyMeasurable n
    hfirst (forward_moment_smul (d.G.rotationScale k*Real.sin (z/d.G.rotationScale k)) n
      (smoothForward_seedScore_moment d (centerNode j) n))

def forwardInput (j : Fin m) (k : d.G.Kernel) (z : ℝ) (w : Seed d) : E × E :=
  (d.x, forward d j k z 0 w)

theorem continuous_forwardInput (j : Fin m) (k : d.G.Kernel) (z : ℝ) :
    Continuous (forwardInput d j k z) :=
  continuous_const.prodMk ((TransportFlowLp.continuous_flow (transportData d) d.x _).comp
    (continuous_const.prodMk (smoothForward_seedRotation_continuous d j k z)))

theorem forwardInput_integrable_norm_pow (j : Fin m) (k : d.G.Kernel) (z : ℝ) (n : ℕ) :
    Integrable (fun w => ‖forwardInput d j k z w‖^n) (seedMeasure d) := by
  obtain ⟨A,B,hA,_,h⟩ := TransportFlowLp.uniform_affine_envelopes (transportData d) d.x
    ⟨d.G.rho k,(d.G.rho_mem k).1,(d.G.rho_mem k).2.le⟩
  apply forward_moment_affine (B := SamplingCenterLp.amplification (transportData d))
    (continuous_forwardInput d j k z).aestronglyMeasurable n
    (smoothForward_seedRotation_moment d j k z n) (add_nonneg (norm_nonneg d.x) hA)
    (Real.exp_pos _).le
  intro w
  change max ‖d.x‖ ‖forward d j k z 0 w‖ ≤ _
  apply max_le
  · have hp : 0 ≤ SamplingCenterLp.amplification (transportData d) * ‖rotation d j k z w‖ :=
      mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
    linarith
  · have hh := (h 0 (rotation d j k z w)).1
    change ‖forward d j k z 0 w‖ ≤ _ at hh
    linarith [norm_nonneg d.x]

theorem forwardInput_polynomial_memLp (j : Fin m) (k : d.G.Kernel) (z : ℝ) (N : ℕ) :
    MemLp (fun w => (1+‖forwardInput d j k z w‖)^N) 2 (seedMeasure d) := by
  have hc := continuous_forwardInput d j k z
  have hm : Integrable (fun p : E × E => ‖p‖^(2*N))
      ((seedMeasure d).map (forwardInput d j k z)) :=
    (integrable_map_measure (by fun_prop) hc.aemeasurable).mpr
      (forwardInput_integrable_norm_pow d j k z (2*N))
  exact (memLp_map_measure_iff (by fun_prop) hc.aemeasurable).mp
    (Analysis.PolynomialLp.memLp_two_one_add_norm_pow N hm)

variable (j : Fin m) (k : d.G.Kernel) (z : ℝ)

def forwardJet (q : ℕ) (t : ℝ) (w : Seed d) : E :=
  (jet (transportData d) q t (forwardInput d j k z w)).2

theorem continuous_forwardJet (q : ℕ) : Continuous (Function.uncurry (forwardJet d j k z q)) :=
  ((continuous_jet (transportData d) q).comp
    (continuous_fst.prodMk ((continuous_forwardInput d j k z).comp continuous_snd))).snd

theorem exists_forwardJet_envelope (q : ℕ) :
    ∃ B : Seed d → ℝ, MemLp B 2 (seedMeasure d) ∧
      ∀ t w, ‖forwardJet d j k z q t w‖ ≤ B w := by
  obtain ⟨C,hC,N,h⟩ := exists_jet_polynomial_bound (transportData d) q
  exact ⟨fun w => C*(1+‖forwardInput d j k z w‖)^N,
    (forwardInput_polynomial_memLp d j k z N).const_mul C,
    fun t w => (norm_snd_le _).trans (h t (forwardInput d j k z w))⟩

theorem forwardJet_memLp (q : ℕ) (t : ℝ) :
    MemLp (forwardJet d j k z q t) 2 (seedMeasure d) := by
  obtain ⟨B,hB,h⟩ := exists_forwardJet_envelope d j k z q
  exact hB.mono'
    ((continuous_forwardJet d j k z q).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall (h t))

theorem hasDerivAt_forwardJet (q : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (left (backwardEnd d.G.R)) (right (backwardEnd d.G.R))) (w : Seed d) :
    HasDerivAt (fun u => forwardJet d j k z q u w) (forwardJet d j k z (q+1) t w) t :=
  (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_jet (transportData d) q ht (forwardInput d j k z w))

def forwardJetLp (q : ℕ) (t : ℝ) : H d :=
  (forwardJet_memLp d j k z q t).toLp (forwardJet d j k z q t)

theorem contDiffOn_forwardJetLp (q n : ℕ) :
    ContDiffOn ℝ n (forwardJetLp d j k z q)
      (Ioo (left (backwardEnd d.G.R)) (right (backwardEnd d.G.R))) := by
  choose B hB hb using (fun i : ℕ => exists_forwardJet_envelope d j k z i)
  have h := Analysis.DominatedLp.contDiffOn_toLp_of_finite_ladder n
    (fun i => forwardJet d j k z (q+i))
    (fun i _ t => forwardJet_memLp d j k z (q+i) t)
    (fun i _ => continuous_forwardJet d j k z (q+i))
    (fun i => B (q+i)) (fun i _ => hB (q+i)) (fun i _ => hb (q+i))
    (fun i _ t ht w => by
      simpa only [Nat.add_assoc] using hasDerivAt_forwardJet d j k z (q+i) ht w)
  change ContDiffOn ℝ n
    (fun t => (forwardJet_memLp d j k z q t).toLp (forwardJet d j k z q t)) _
  simpa only [Nat.add_zero] using h

def smoothForward (t : ℝ) : H d := forwardJetLp d j k z 0 t

theorem smoothForward_eq {t : ℝ} (ht : t ∈ Icc 0 (backwardEnd d.G.R)) :
    smoothForward d j k z t = forwardLp d j k z t := by
  unfold smoothForward forwardJetLp forwardLp
  apply Lp.ext
  filter_upwards [(forwardJet_memLp d j k z 0 t).coeFn_toLp,
    (forward_memLp d j k z t).coeFn_toLp] with w h1 h2
  rw [h1,h2]
  change (jointPath (transportData d) t (d.x,forward d j k z 0 w)).2 = _
  rw [jointPath_snd_eq_source (transportData d) d.x _ ht]
  exact (TransportFlowLp.flow_eq_path (transportData d) d.x _ t
    (rotation d j k z w)).symm

theorem contDiffOn_smoothForward (n : ℕ) :
    ContDiffOn ℝ n (smoothForward d j k z)
      (Ioo (left (backwardEnd d.G.R)) (right (backwardEnd d.G.R))) :=
  contDiffOn_forwardJetLp d j k z 0 n

def smoothForwardMean (t : ℝ) : H d := (-d.r)⁻¹ • forwardJetLp d j k z 1 t

theorem contDiffOn_smoothForwardMean (n : ℕ) :
    ContDiffOn ℝ n (smoothForwardMean d j k z)
      (Ioo (left (backwardEnd d.G.R)) (right (backwardEnd d.G.R))) :=
  (contDiffOn_forwardJetLp d j k z 1 n).const_smul _

end AcceleratedLogConcave.Numerics.MeanResidualBridge
