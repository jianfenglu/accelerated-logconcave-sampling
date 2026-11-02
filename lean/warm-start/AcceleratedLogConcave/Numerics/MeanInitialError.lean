import AcceleratedLogConcave.Numerics.MeanCollocationLp
noncomputable section
open Set MeasureTheory ProbabilityTheory AcceleratedLogConcave Conditional
open Numerics Numerics.MeanFlowLp Numerics.MeanResidualBridge Numerics.AffineGraph
open Numerics.AffineGraph.MeanGeometry
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Numerics.MeanCollocationLp
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

omit [DecidableEq ι] in
/-- Explicit size and resolution assumptions, not mesh conditions alone, give contraction. -/
theorem contraction_le_half_of_resolution (d : Data ι m) (h₀ : ℝ)
    (h : MeshConditions d h₀) {δ b t w S : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ w) (hwt : w ≤ t)
    (ht : t ≤ (1 : ℝ)/60) (hb : (1 : ℝ)/2 ≤ b) (hS : 1 ≤ S)
    (hpsi : d.G.psi = δ ^ (4*t)) (hstep : h₀ = δ ^ w)
    (hsizeR : d.ell*d.r^2 ≤ S*δ^b) (hsizeS : d.ell*d.r/d.sigma ≤ S*δ^b)
    (hres : δ ≤ (520*(m:ℝ)^5*S)^(-12:ℝ)) : contraction d h₀ ≤ 1/2 := by
  have he := affine_mean_envelope_le_rpow_third h.order hδ hδ1 hw hwt ht hb hS
    d.hsigma hsizeR hsizeS hres
  have hp : δ ^ ((1:ℝ)/3) ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by norm_num)
  dsimp [contraction,rowMass]
  rw [hpsi,hstep]
  nlinarith

omit [DecidableEq ι] in
private theorem norm_sq_toLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {g : Ω → E} (hg : MemLp g 2 μ) :
    ‖hg.toLp g‖^2 = ∫ z, ‖g z‖^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with z hz
  rw [hz,real_inner_self_eq_norm_sq]

omit [DecidableEq ι] in
private theorem norm_toLp_gaussian {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (g : Ω → E) (hmp : MeasurePreserving g μ (stdGaussian E)) :
    ‖((IsGaussian.memLp_two_id (μ := stdGaussian E)).comp_measurePreserving hmp).toLp g‖ =
      Real.sqrt (Module.finrank ℝ E) := by
  have he := norm_sq_toLp ((IsGaussian.memLp_two_id (μ := stdGaussian E)).comp_measurePreserving hmp)
  have hi : (∫ z, ‖g z‖^2 ∂μ) = (Module.finrank ℝ E : ℝ) := by
    rw [← Gibbs.integral_norm_sq_stdGaussian («E» := E), ← hmp.map_eq,
      integral_map hmp.measurable.aemeasurable (by fun_prop)]
  change ‖((IsGaussian.memLp_two_id (μ := stdGaussian E)).comp_measurePreserving hmp).toLp g‖^2 = ∫ z, ‖g z‖^2 ∂μ at he
  rw [hi] at he
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg (Module.finrank ℝ E)), norm_nonneg
    (((IsGaussian.memLp_two_id (μ := stdGaussian E)).comp_measurePreserving hmp).toLp g),
    Real.sqrt_nonneg (Module.finrank ℝ E : ℝ)]

omit [DecidableEq ι] in
theorem norm_initialScore (d : Data ι m) :
    ‖initialScore d‖ = Real.sqrt (Module.finrank ℝ E) :=
  norm_toLp_gaussian (fun ω : Seed d => ω.1.snd)
    ((KernelFlowLp.momentum_preserving (kernelData d)).comp (phase_projection_preserving d))

omit [DecidableEq ι] in
theorem norm_initialNoise (d : Data ι m) (j : Fin m) (k : d.G.Kernel) :
    ‖initialNoise d j k‖ = Real.sqrt (Module.finrank ℝ E) :=
  norm_toLp_gaussian _ (noise_projection_preserving d j k)

/-- Initial position is an interpolation of a primitive posterior and a Gaussian,
not itself a Gaussian. This bound retains the gradient at the supplied center. -/
theorem norm_initialPosition_le (d : Data ι m) :
    ‖initialPosition d‖ ≤ 2*Real.sqrt (Module.finrank ℝ E)+d.r*‖gradient d.F d.x‖ := by
  let ν := Gibbs.primitiveLaw d.F d.x d.r
  let γ := stdGaussian E
  let μ := ν.prod γ
  let := Gibbs.primitiveLaw_isProbabilityMeasure d.hF d.hlo d.x d.r
  have hν : MemLp (id : E → E) 2 ν := Gibbs.primitive_memLp_two_id d.hF d.hlo d.x d.r
  have hγ := IsGaussian.memLp_two_id (μ := γ)
  have hfst : MeasurePreserving (Prod.fst : E × E → E) μ ν := measurePreserving_fst
  have hsnd : MeasurePreserving (Prod.snd : E × E → E) μ γ := measurePreserving_snd
  let b := backwardEnd d.G.R
  have hνnorm : ‖hν.toLp id‖ ≤ Real.sqrt (Module.finrank ℝ E)+d.r*‖gradient d.F d.x‖ := by
    have he := norm_sq_toLp hν
    simp only [id_eq] at he
    have hr : ‖hν.toLp id‖ = Real.sqrt (∫ z, ‖z‖^2 ∂ν) := by
      rw [← he,Real.sqrt_sq (norm_nonneg _)]
    rw [hr]
    exact Gibbs.primitive_second_moment_le d.hF d.hell d.hlo d.hup d.hr d.x
  have hz := hν.comp_measurePreserving hfst
  have hg := hγ.comp_measurePreserving hsnd
  have hz_norm : ‖hz.toLp (id ∘ Prod.fst)‖ = ‖hν.toLp id‖ :=
    Lp.norm_compMeasurePreserving (hν.toLp id) hfst
  have hg_norm : ‖hg.toLp (id ∘ Prod.snd)‖ = Real.sqrt (Module.finrank ℝ E) :=
    norm_toLp_gaussian _ hsnd
  have hI := (hz.const_smul b).add (hg.const_smul (Real.sqrt (conditionalVariance b)))
  have hI_norm : ‖hI.toLp (interpolationMap b)‖ ≤
      2*Real.sqrt (Module.finrank ℝ E)+d.r*‖gradient d.F d.x‖ := by
    change ‖hI.toLp (b • (id ∘ Prod.fst) + Real.sqrt (conditionalVariance b) • (id ∘ Prod.snd))‖ ≤ _
    rw [MemLp.toLp_add (hz.const_smul b) (hg.const_smul _),
      MemLp.toLp_const_smul _ hz,MemLp.toLp_const_smul _ hg]
    have hb0 : 0 ≤ b := d.G.backwardEnd_pos.le
    have hb1 : b ≤ 1 := d.G.backwardEnd_lt_one.le
    have hv : Real.sqrt (conditionalVariance b) ≤ 1 := by
      apply (Real.sqrt_le_one).mpr
      dsimp [conditionalVariance]
      nlinarith [sq_nonneg b]
    calc
      _ ≤ ‖b • hz.toLp _‖ + ‖Real.sqrt (conditionalVariance b) • hg.toLp _‖ := norm_add_le _ _
      _ = b*‖hν.toLp id‖ + Real.sqrt (conditionalVariance b)*Real.sqrt (Module.finrank ℝ E) := by
        rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hb0,
          abs_of_nonneg (Real.sqrt_nonneg _),hz_norm,hg_norm]
      _ ≤ ‖hν.toLp id‖ + Real.sqrt (Module.finrank ℝ E) := by
        exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) hb1)
          (mul_le_of_le_one_left (Real.sqrt_nonneg _) hv)
      _ ≤ _ := by linarith
  have hmap : MeasurePreserving (interpolationMap b) μ (interpolationLaw d.F d.x d.r b) := by
    refine ⟨by unfold interpolationMap; fun_prop, ?_⟩
    rfl
  have hid : MemLp (id : E → E) 2 (interpolationLaw d.F d.x d.r b) := by
    rw [← hmap.map_eq]
    exact (memLp_map_measure_iff (by fun_prop) hmap.measurable.aemeasurable).mpr hI
  have hp := (CenteringFlowLp.position_preserving (kernelData d)).comp (phase_projection_preserving d)
  have hn : ‖initialPosition d‖ = ‖hid.toLp id‖ := Lp.norm_compMeasurePreserving (hid.toLp id) hp
  rw [hn]
  have hn' : ‖hI.toLp (interpolationMap b)‖ = ‖hid.toLp id‖ :=
    Lp.norm_compMeasurePreserving (hid.toLp id) hmap
  rw [← hn']
  exact hI_norm

/-- A finite coefficient expression depending only on the specified geometry and scales. -/
def anchorMass (d : Data ι m) : ℝ :=
  ‖fun i : d.G.MeanNode => ∑ a : d.G.Anchor, |d.G.centerForm d.r d.sigma i (.inl a)|‖
def seedBudget (d : Data ι m) : ℝ :=
  2*Real.sqrt (Module.finrank ℝ E)+d.r*‖gradient d.F d.x‖
def radiusBudget (d : Data ι m) : ℝ := d.r
def meanBudget (d : Data ι m) : ℝ :=
  ‖gradient d.F d.x‖ + (d.ell*radiusBudget d)*
    (Real.sqrt (Module.finrank ℝ E)+radiusBudget d*‖gradient d.F d.x‖)
def coefficientBudget (d : Data ι m) : ℝ := anchorMass d*seedBudget d
def directBudget (d : Data ι m) : ℝ := 8*d.r*seedBudget d

omit [DecidableEq ι] in
theorem seedBudget_nonneg (d : Data ι m) : 0 ≤ seedBudget d := by
  unfold seedBudget
  exact add_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    (mul_nonneg d.hr.le (norm_nonneg _))

theorem norm_direct_le_coeff (d : Data ι m) : ‖(lpGraph d).direct‖ ≤ coefficientBudget d := by
  have ha (a : d.G.Anchor) :
      ‖d.G.anchorValues (initialPosition d) (initialScore d) (initialNoise d) a‖ ≤ seedBudget d := by
    rcases a with a | a | ⟨j,k⟩
    · exact norm_initialPosition_le d
    · change ‖initialScore d‖ ≤ _
      rw [norm_initialScore]
      dsimp [seedBudget]
      have := mul_nonneg d.hr.le (norm_nonneg (gradient d.F d.x))
      nlinarith [Real.sqrt_nonneg (Module.finrank ℝ E : ℝ)]
    · change ‖initialNoise d j k‖ ≤ _
      rw [norm_initialNoise]
      dsimp [seedBudget]
      have := mul_nonneg d.hr.le (norm_nonneg (gradient d.F d.x))
      nlinarith [Real.sqrt_nonneg (Module.finrank ℝ E : ℝ)]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _) (seedBudget_nonneg d))).mpr
  intro i
  change ‖0+∑ a, d.G.centerForm d.r d.sigma i (.inl a) •
    d.G.anchorValues (initialPosition d) (initialScore d) (initialNoise d) a‖ ≤ _
  rw [zero_add]
  calc
    _ ≤ ∑ a, ‖d.G.centerForm d.r d.sigma i (.inl a) •
        d.G.anchorValues (initialPosition d) (initialScore d) (initialNoise d) a‖ := norm_sum_le _ _
    _ ≤ ∑ a, |d.G.centerForm d.r d.sigma i (.inl a)| *seedBudget d := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (ha a) (abs_nonneg _)
    _ = (∑ a, |d.G.centerForm d.r d.sigma i (.inl a)|)*seedBudget d := by rw [Finset.sum_mul]
    _ ≤ coefficientBudget d := by
      apply mul_le_mul_of_nonneg_right _ (seedBudget_nonneg d)
      exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs,anchorMass] using (norm_le_pi_norm (fun i : d.G.MeanNode => ∑ a : d.G.Anchor, |d.G.centerForm d.r d.sigma i (.inl a)|) i))

/-- A scalar envelope for the actual direct vector, uniform over all mesh nodes. -/
theorem norm_direct_le (d : Data ι m) : ‖(lpGraph d).direct‖ ≤ directBudget d := by
  let S := seedBudget d
  have hS : 0 ≤ S := seedBudget_nonneg d
  have hy : ‖initialPosition d‖ ≤ S := norm_initialPosition_le d
  have hg : ‖initialScore d‖ ≤ S := by
    rw [norm_initialScore]
    dsimp [S,seedBudget]
    have := mul_nonneg d.hr.le (norm_nonneg (gradient d.F d.x))
    nlinarith [Real.sqrt_nonneg (Module.finrank ℝ E : ℝ)]
  have hz (b : Fin m) (k : d.G.Kernel) : ‖initialNoise d b k‖ ≤ S := by
    rw [norm_initialNoise,← norm_initialScore d]
    exact hg
  have hs (a : ℝ) (ha : |a| ≤ 1) (X : H d) (hX : ‖X‖ ≤ S) : ‖a • X‖ ≤ S := by
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right ha (norm_nonneg _)).trans (by simpa using hX)
  have hscale (a : ℝ) (ha : |a| ≤ 1) (X : H d) (hX : ‖X‖ ≤ 8*S) :
      ‖(d.r*a) • X‖ ≤ directBudget d := by
    rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_pos d.hr]
    change _ ≤ 8*d.r*S
    nlinarith [mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_right ha (norm_nonneg X)).trans (by simpa using hX)) d.hr.le]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) d.hr.le) hS)).mpr
  intro i
  change ‖d.G.direct d.r d.sigma 0 (initialPosition d) (initialScore d) (initialNoise d) i‖ ≤ _
  rcases i with _ | b | ⟨b,j⟩ | ⟨b,k,j⟩ | ⟨b,k,z,j⟩
  · rw [← MeanNode.base,MeanGeometry.direct_base,norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) d.hr.le) hS
  · rw [← MeanNode.center,d.G.direct_center,zero_add]
    apply hscale
    · rw [abs_of_nonneg d.G.backwardEnd_pos.le]
      exact d.G.backwardEnd_lt_one.le
    · linarith
  · rw [← MeanNode.backward,d.G.direct_backward,zero_add]
    apply hscale
    · have hj := d.G.backward.location_mem_interval m j
      rw [abs_of_nonneg hj.1.le]
      exact hj.2.le.trans d.G.backwardEnd_lt_one.le
    · linarith
  · rw [← MeanNode.conditional,d.G.direct_conditional,zero_add]
    have hk0 := (d.G.rho_mem k).1
    have hk1 := (d.G.rho_mem k).2.trans d.G.backwardEnd_lt_one
    have hv0 := Real.sqrt_nonneg (d.G.variance k)
    have hv1 : Real.sqrt (d.G.variance k) ≤ 1 := by
      apply Real.sqrt_le_one.mpr
      dsimp [MeanGeometry.variance]
      nlinarith [sq_nonneg (d.G.rho k)]
    have hj := (d.G.conditional k).location_mem_interval m j
    have hy' := hs (d.G.rho k) (by rw [abs_of_nonneg hk0]; exact hk1.le) (initialPosition d) hy
    have hz' := hs (Real.sqrt (d.G.variance k)*(d.G.conditional k).location m j)
      (by rw [abs_of_nonneg (mul_nonneg hv0 hj.1.le)];
          exact (mul_le_mul_of_nonneg_right hv1 hj.1.le).trans (by simpa using hj.2.le.trans conditionalEnd_lt_one.le))
      (initialNoise d b k) (hz b k)
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos d.hr]
    have hsum := norm_add_le (d.G.rho k • initialPosition d)
      ((Real.sqrt (d.G.variance k)*(d.G.conditional k).location m j) • initialNoise d b k)
    change _ ≤ 8*d.r*S
    nlinarith [mul_le_mul_of_nonneg_left (hsum.trans (add_le_add hy' hz')) d.hr.le, mul_nonneg d.hr.le hS]
  · rw [← MeanNode.forward,d.G.direct_forward,zero_add]
    apply hscale
    · have hj := (d.G.forward k).location_mem_interval m j
      rw [abs_of_nonneg ((d.G.rho_mem k).1.trans hj.1.le)]
      exact hj.2.le.trans d.G.backwardEnd_lt_one.le
    · let q := d.G.rotationScale k
      let θ := d.G.angleNode z/q
      have hq0 : 0 ≤ q := (d.G.rotationScale_pos k).le
      have hq1 : q ≤ 1 := by
        apply Real.sqrt_le_one.mpr
        apply (div_le_one (by positivity : 0 < 1+(d.G.rho k)^2)).mpr
        dsimp [MeanGeometry.variance]
        nlinarith [sq_nonneg (d.G.rho k)]
      have hc0 : 0 ≤ 1-Real.cos θ := sub_nonneg.mpr (Real.cos_le_one _)
      have hc2 : 1-Real.cos θ ≤ 2 := by linarith [Real.neg_one_le_cos θ]
      have ha : |1-q^2*(1-Real.cos θ)| ≤ 3 := by
        apply abs_le.mpr
        have hq2 : q^2 ≤ 1 := by nlinarith
        have hp := mul_le_mul hq2 hc2 hc0 (by norm_num : (0:ℝ)≤1)
        constructor <;> nlinarith [mul_nonneg (sq_nonneg q) hc0]
      have hb : |q*Real.sin θ| ≤ 1 := by
        rw [abs_mul,abs_of_nonneg hq0]
        exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) hq0).trans (by simpa using hq1)
      have hk0 := (d.G.rho_mem k).1
      have hk1 : d.G.rho k ≤ 1 := ((d.G.rho_mem k).2.trans d.G.backwardEnd_lt_one).le
      have hv : Real.sqrt (2*d.G.variance k) ≤ 2 := by
        apply (Real.sqrt_le_iff).mpr
        refine ⟨by norm_num,?_⟩
        dsimp [MeanGeometry.variance]
        nlinarith [sq_nonneg (d.G.rho k)]
      have hc : |d.G.rho k*Real.sqrt (2*d.G.variance k)*(1-Real.cos θ)/(1+(d.G.rho k)^2)| ≤ 4 := by
        rw [abs_of_nonneg (by positivity)]
        apply (div_le_iff₀ (by positivity : 0 < 1+(d.G.rho k)^2)).mpr
        have hp : d.G.rho k*Real.sqrt (2*d.G.variance k) ≤ 2 :=
          (mul_le_mul_of_nonneg_right hk1 (Real.sqrt_nonneg _)).trans (by simpa using hv)
        have hprod := mul_le_mul hp hc2 hc0 (by norm_num : (0:ℝ)≤2)
        nlinarith [sq_nonneg (d.G.rho k)]
      have hA := mul_le_mul ha hy (norm_nonneg _) (by norm_num : (0:ℝ)≤3)
      have hB := mul_le_mul hb hg (norm_nonneg _) (by norm_num : (0:ℝ)≤1)
      have hC := mul_le_mul hc (hz b k) (norm_nonneg _) (by norm_num : (0:ℝ)≤4)
      have ht := norm_add_le
        ((1-q^2*(1-Real.cos θ)) • initialPosition d + (q*Real.sin θ) • initialScore d)
        ((d.G.rho k*Real.sqrt (2*d.G.variance k)*(1-Real.cos θ)/(1+(d.G.rho k)^2)) • initialNoise d b k)
      have ht' := norm_add_le ((1-q^2*(1-Real.cos θ)) • initialPosition d) ((q*Real.sin θ) • initialScore d)
      simp only [norm_smul,Real.norm_eq_abs] at ht ht'
      change ‖((1-q^2*(1-Real.cos θ)) • initialPosition d + (q*Real.sin θ) • initialScore d)+
        ((d.G.rho k*Real.sqrt (2*d.G.variance k)*(1-Real.cos θ)/(1+(d.G.rho k)^2)) • initialNoise d b k)‖ ≤ _
      linarith

omit [DecidableEq ι] in
/-- Every literal primitive query radius is at most the public base radius. -/
theorem query_radius_le (d : Data ι m) (i : d.G.MeanNode) : d.G.radius d.r i ≤ d.r := by
  have hs (x : ℝ) : Real.sqrt (1-x^2) ≤ 1 :=
    Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg x])
  rcases i with _ | b | ⟨b,j⟩ | ⟨b,k,j⟩ | ⟨b,k,z,j⟩
  · exact le_rfl
  · change d.r*d.G.R ≤ d.r
    exact mul_le_of_le_one_right d.hr.le (d.G.R_le_half.trans (by norm_num))
  · change d.r*Real.sqrt (1-(d.G.backward.location m j)^2) ≤ d.r
    exact mul_le_of_le_one_right d.hr.le (hs _)
  · change d.r*Real.sqrt (d.G.variance k)*Real.sqrt (1-((d.G.conditional k).location m j)^2) ≤ d.r
    have hv : Real.sqrt (d.G.variance k) ≤ 1 := hs (d.G.rho k)
    exact (mul_le_of_le_one_right (mul_nonneg d.hr.le (Real.sqrt_nonneg _)) (hs _)).trans
      (mul_le_of_le_one_right d.hr.le hv)
  · change d.r*Real.sqrt (1-((d.G.forward k).location m j)^2) ≤ d.r
    exact mul_le_of_le_one_right d.hr.le (hs _)

omit [DecidableEq ι] in
theorem norm_operator_zero_le (d : Data ι m) (i : d.G.MeanNode) :
    ‖operator d 0 (d.G.radius d.r i)‖ ≤ meanBudget d := by
  have hq := d.G.radius_pos d.r d.hr i
  have hb := Gibbs.norm_primitiveMean_sub_gradient_le_rms d.hF d.hell d.hlo d.hup hq.le d.x
  have hm := Gibbs.primitive_second_moment_le d.hF d.hell d.hlo d.hup hq d.x
  have hqr : d.G.radius d.r i ≤ radiusBudget d :=
    query_radius_le d i
  change ‖primitiveLp (primitiveData d) (seedMeasure d) 0 (d.G.radius d.r i)‖ ≤ _
  rw [primitiveLp_zero _ _ hq]
  have hc := Lp.norm_const («E» := E) (μ := seedMeasure d) (p := 2)
    (c := Gibbs.primitiveMean d.F d.x (d.G.radius d.r i)) (by norm_num)
  change ‖Lp.const 2 (seedMeasure d) (Gibbs.primitiveMean d.F d.x (d.G.radius d.r i))‖ ≤ _
  rw [hc]
  simp only [probReal_univ,Real.one_rpow,mul_one]
  have htri := norm_add_le (Gibbs.primitiveMean d.F d.x (d.G.radius d.r i)-gradient d.F d.x)
    (gradient d.F d.x)
  simp only [sub_add_cancel] at htri
  change ‖Gibbs.primitiveMean d.F d.x (d.G.radius d.r i)‖ ≤ _
  calc
    _ ≤ ‖gradient d.F d.x‖ + (d.ell*d.G.radius d.r i)*
        (Real.sqrt (Module.finrank ℝ E)+d.G.radius d.r i*‖gradient d.F d.x‖) := by
      have hmul := mul_le_mul_of_nonneg_left hm (mul_nonneg d.hell hq.le)
      linarith
    _ ≤ meanBudget d := by
      dsimp [meanBudget]
      gcongr
      · exact mul_nonneg d.hell d.hr.le
      · exact d.hell

/-- The initializer defect is priced using only coefficients, seed moments, and
one gradient norm at the supplied center, not a hidden reference norm. -/
theorem direct_defect_le (d : Data ι m) (h₀ : ℝ) (h : MeshConditions d h₀) :
    ‖(lpGraph d).step (operator d) (lpGraph d).direct-(lpGraph d).direct‖ ≤
      rowMass d h₀*(d.ell*directBudget d+meanBudget d) := by
  have hA : 0 ≤ directBudget d := mul_nonneg (mul_nonneg (by norm_num) d.hr.le) (seedBudget_nonneg d)
  have hM : 0 ≤ meanBudget d := by
    unfold meanBudget radiusBudget
    exact add_nonneg (norm_nonneg _) (mul_nonneg (mul_nonneg d.hell d.hr.le)
      (add_nonneg (Real.sqrt_nonneg _) (mul_nonneg d.hr.le (norm_nonneg _))))
  have hB : 0 ≤ d.ell*directBudget d+meanBudget d :=
    add_nonneg (mul_nonneg d.hell hA) hM
  have hop (j : d.G.MeanNode) :
      ‖operator d ((lpGraph d).direct j) (d.G.radius d.r j)‖ ≤ d.ell*directBudget d+meanBudget d := by
    have hl := (primitiveLp_lipschitz (primitiveData d) (seedMeasure d)
      (d.G.radius_pos d.r d.hr j)).norm_sub_le ((lpGraph d).direct j) 0
    have hn := (norm_le_pi_norm (lpGraph d).direct j).trans (norm_direct_le d)
    have hz := norm_operator_zero_le d j
    have ht := norm_add_le
      (operator d ((lpGraph d).direct j) (d.G.radius d.r j)-operator d 0 (d.G.radius d.r j))
      (operator d 0 (d.G.radius d.r j))
    simp only [sub_add_cancel] at ht
    simp only [sub_zero] at hl
    have hm := mul_le_mul_of_nonneg_left hn d.hell
    exact ht.trans (add_le_add (hl.trans hm) hz)
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (rowMass_nonneg d h₀ h) hB)).mpr
  intro i
  change ‖(lpGraph d).step (operator d) (lpGraph d).direct i-(lpGraph d).direct i‖ ≤ _
  rw [FiniteGraph.step_eq,add_sub_cancel_left]
  calc
    _ ≤ ∑ j, ‖d.G.matrix d.r d.sigma i j •
      operator d ((lpGraph d).direct j) (d.G.radius d.r j)‖ := norm_sum_le _ _
    _ ≤ ∑ j, |d.G.matrix d.r d.sigma i j| *(d.ell*directBudget d+meanBudget d) := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hop j) (abs_nonneg _)
    _ = (∑ j, |d.G.matrix d.r d.sigma i j|)*(d.ell*directBudget d+meanBudget d) := by
      rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (actual_row_bound d h₀ h i) hB

theorem initialError_absorption (d : Data ι m) (h₀ : ℝ) (h : MeshConditions d h₀)
    (K : Fin m → ℝ → H d) (l v : ℝ) (D : AffineResidual.Mean.DerivativeBudget d.G)
    (hreg : Regularity d K l v D) :
    (1-contraction d h₀)*initialError d ≤
      rowMass d h₀*(d.ell*directBudget d+meanBudget d)+residualBudget d h₀ D := by
  let A := (lpGraph d).direct
  let P := (lpGraph d).step (operator d)
  let R := reference d
  have hC : ‖P A-P R‖ ≤ contraction d h₀*initialError d := by
    apply (pi_norm_le_iff_of_nonneg
      (mul_nonneg (contraction_nonneg d h₀ h) (norm_nonneg _))).mpr
    exact contraction_target d h₀ h A R
  have hR : ‖P R-R‖ ≤ residualBudget d h₀ D := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    exact residual_bound d h₀ h K l v D hreg
  have hA := direct_defect_le d h₀ h
  have h1 : ‖A-R‖ ≤ ‖A-P A‖+‖P A-R‖ := norm_sub_le_norm_sub_add_norm_sub A (P A) R
  have h2 : ‖P A-R‖ ≤ ‖P A-P R‖+‖P R-R‖ := norm_sub_le_norm_sub_add_norm_sub (P A) (P R) R
  have hsym : ‖A-P A‖ = ‖P A-A‖ := norm_sub_rev _ _
  change ‖P A-A‖ ≤ _ at hA
  change (1-contraction d h₀)*‖A-R‖ ≤ _
  change ‖P A-P R‖ ≤ contraction d h₀*‖A-R‖ at hC
  nlinarith

/-- Quantitative initial error, conditional on the already explicit regularity
supplier and a true contraction bound. No reference error appears on the RHS. -/
theorem initialError_le_of_half (d : Data ι m) (h₀ : ℝ) (h : MeshConditions d h₀)
    (K : Fin m → ℝ → H d) (l v : ℝ) (D : AffineResidual.Mean.DerivativeBudget d.G)
    (hreg : Regularity d K l v D) (hq : contraction d h₀ ≤ 1/2) :
    initialError d ≤ 2*(rowMass d h₀*(d.ell*directBudget d+meanBudget d)+residualBudget d h₀ D) := by
  have ha := initialError_absorption d h₀ h K l v D hreg
  have hn : 0 ≤ initialError d := norm_nonneg _
  nlinarith


/-- Scalar public-data initial-error supplier. All radius, moment and affine
initializer bounds are conclusions; only the original regularity and explicit
size/resolution hypotheses remain. The seed score is G0, not original momentum. -/
theorem initialError_le_of_resolution (d : Data ι m) (h₀ : ℝ)
    (h : MeshConditions d h₀) (K : Fin m → ℝ → H d) (l v : ℝ)
    (D : AffineResidual.Mean.DerivativeBudget d.G) (hreg : Regularity d K l v D)
    {δ b t w S : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ w) (hwt : w ≤ t)
    (ht : t ≤ (1 : ℝ)/60) (hb : (1 : ℝ)/2 ≤ b) (hS : 1 ≤ S)
    (hpsi : d.G.psi = δ ^ (4*t)) (hstep : h₀ = δ ^ w)
    (hsizeR : d.ell*d.r^2 ≤ S*δ^b) (hsizeS : d.ell*d.r/d.sigma ≤ S*δ^b)
    (hres : δ ≤ (520*(m:ℝ)^5*S)^(-12:ℝ)) :
    initialError d ≤ 2*(rowMass d h₀*
      (d.ell*(8*d.r*(2*Real.sqrt (Module.finrank ℝ E)+d.r*‖gradient d.F d.x‖))+
       (‖gradient d.F d.x‖+(d.ell*d.r)*(Real.sqrt (Module.finrank ℝ E)+d.r*‖gradient d.F d.x‖)))+
      residualBudget d h₀ D) := by
  exact initialError_le_of_half d h₀ h K l v D hreg
    (contraction_le_half_of_resolution d h₀ h hδ hδ1 hw hwt ht hb hS hpsi hstep hsizeR hsizeS hres)

end AcceleratedLogConcave.Numerics.MeanCollocationLp
