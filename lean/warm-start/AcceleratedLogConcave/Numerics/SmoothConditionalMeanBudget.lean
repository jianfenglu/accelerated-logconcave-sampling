import AcceleratedLogConcave.Numerics.SmoothReferenceDisplacement

/-!
# The random-center conditional mean from the actual seed law

The conditional seed is a fresh Gaussian. We couple its response at the
random center with the same response at the original center, then transfer
the fixed-center covariance estimate through the proved marginal law.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory AcceleratedLogConcave
open Numerics Numerics.MeanFlowLp Numerics.MeanResidualBridge Numerics.MeanCollocationLp
open Numerics.AffineGraph Numerics.AffineGraph.MeanGeometry
open Numerics.SmoothReferenceDisplacement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace AcceleratedLogConcave.Numerics.SmoothConditionalMeanBudget
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

def fixedMean (d : Data ι m) (j : Fin m) (ρ : d.G.Kernel)
    (t : ℝ) (ω : Seed d) : E :=
  Conditional.conditionalMean d.F d.x (conditionalData d ρ).r t
    (SamplingCenterLp.path (conditionalData d ρ) d.x t (ω.2 j ρ))

omit [DecidableEq ι] in
/-- The fixed-center comparison variable inherits the exact conditional
interpolation marginal from the fresh Gaussian coordinate. -/
theorem fixed_path_preserving (d : Data ι m) (j : Fin m)
    (ρ : d.G.Kernel) (t : ℝ) (ht : t ∈ Icc 0 conditionalEnd) :
    MeasurePreserving
      (fun ω : Seed d => SamplingCenterLp.path (conditionalData d ρ)
        d.x t (ω.2 j ρ)) (seedMeasure d)
      (Conditional.interpolationLaw d.F d.x (conditionalData d ρ).r t) :=
  (SamplingCenterLp.path_preserving (conditionalData d ρ) d.x ht).comp
    (noise_projection_preserving d j ρ)

/-- The fixed-center conditional mean fluctuation has the sharp covariance
budget, after composition with the actual common seed coordinate. -/
theorem fixedMean_centered_le (d : Data ι m) (j : Fin m)
    (ρ : d.G.Kernel) (t : ℝ) (ht : t ∈ Icc 0 conditionalEnd) :
    ∃ hg : MemLp (fun ω => fixedMean d j ρ t ω -
        Gibbs.primitiveMean d.F d.x (conditionalData d ρ).r) 2 (seedMeasure d),
      ‖hg.toLp (fun ω => fixedMean d j ρ t ω -
        Gibbs.primitiveMean d.F d.x (conditionalData d ρ).r)‖ ≤
        Real.exp 1 * ((conditionalData d ρ).r * d.ell) *
          Real.sqrt (Module.finrank ℝ E) := by
  obtain ⟨hg,hgBound⟩ := norm_conditionalMean_centered_law_le_at d
    d.x (conditionalData d ρ).r (conditionalData d ρ).hr
    (conditional_radius_small d ρ) t ht.1
    (ht.2.trans_lt conditionalEnd_lt_one)
  let hp := fixed_path_preserving d j ρ t ht
  let hc := hg.comp_measurePreserving hp
  refine ⟨hc, ?_⟩
  change ‖hc.toLp ((fun y => Conditional.conditionalMean d.F d.x
    (conditionalData d ρ).r t y - Gibbs.primitiveMean d.F d.x
    (conditionalData d ρ).r) ∘
    (fun ω : Seed d => SamplingCenterLp.path (conditionalData d ρ)
      d.x t (ω.2 j ρ)))‖ ≤ _
  exact (Lp.norm_compMeasurePreserving (hg.toLp _) hp).trans_le hgBound

omit [DecidableEq ι] in
/-- The fixed-center comparison uses the same Gaussian seed and the same
conditional probability flow as the actual random-center receiver. -/
theorem fixedMean_eq_reply (d : Data ι m) (j : Fin m)
    (ρ : d.G.Kernel) (t : ℝ) (ht : t ∈ Icc 0 conditionalEnd)
    (ω : Seed d) :
    fixedMean d j ρ t ω =
      SamplingCenterLp.reply (conditionalData d ρ) d.x t (ω.2 j ρ) +
        SamplingCenterLp.initialMean (conditionalData d ρ) d.x := by
  unfold fixedMean
  rw [AffineFlowIdentities.conditionalMean_eq_primitiveMean
    d.hF d.hell d.hlo d.hup d.x (conditionalData d ρ).hr
    (by linarith [ht.1]) (ht.2.trans_lt conditionalEnd_lt_one)]
  change _ = (_ - Gibbs.primitiveMean d.F d.x (conditionalData d ρ).r) +
    Gibbs.primitiveMean d.F d.x (conditionalData d ρ).r
  rw [sub_add_cancel]
  rw [SamplingFlowLp.sourceTime_eq conditionalEnd_pos.le ht]
  rfl

/-- Coupling the two conditional flows through their common fresh Gaussian
coordinate reduces the random-center effect to the backward center movement. -/
theorem conditionalMean_sub_fixed_le (d : Data ι m) (j : Fin m)
    (ρ : d.G.Kernel) (t : ℝ) (ht : t ∈ Icc 0 conditionalEnd)
    (ω : Seed d) :
    ‖conditionalMean d j ρ t ω - fixedMean d j ρ t ω‖ ≤
      (3 * d.ell +
        (conditionalData d ρ).r * conditionalEnd * d.ell *
          SamplingCenterLp.amplification (conditionalData d ρ) *
          ((conditionalData d ρ).r * d.ell * conditionalEnd)) *
        ‖conditionalCenter d j ρ ω - d.x‖ := by
  rw [MeanFlowLp.conditionalMean_eq d j ρ t ω,
    fixedMean_eq_reply d j ρ t ht ω]
  let q := (conditionalData d ρ).r
  let b := conditionalEnd
  let A := SamplingCenterLp.amplification (conditionalData d ρ)
  let X := conditionalCenter d j ρ ω
  let P := ω.2 j ρ
  let R := SamplingCenterLp.reply (conditionalData d ρ)
  let M := SamplingCenterLp.initialMean (conditionalData d ρ)
  have hrep := SamplingCenterLp.reply_stability
    (conditionalData d ρ) X d.x P P t
  simp only [sub_self, norm_zero, zero_add] at hrep
  have hmean := (Gibbs.primitive_mean_lipschitz d.hF d.hell d.hlo d.hup
    (conditionalData d ρ).hr).dist_le_mul X d.x
  change ‖M X - M d.x‖ ≤ d.ell * ‖X - d.x‖ at hmean
  have htri := norm_add_le (R X t P - R d.x t P) (M X - M d.x)
  have he : (R X t P + M X) - (R d.x t P + M d.x) =
      (R X t P - R d.x t P) + (M X - M d.x) := by abel
  rw [he]
  change ‖R X t P - R d.x t P‖ ≤
    2 * d.ell * ‖X - d.x‖ +
      q * b * d.ell * A * (q * d.ell * b * ‖X - d.x‖) at hrep
  nlinarith

/-- The coupling estimate transfers to the canonical common-seed L² space.
The only random-center input is the actual backward state. -/
theorem norm_conditionalMeanLp_sub_fixed_le (d : Data ι m) (j : Fin m)
    (ρ : d.G.Kernel) (t : ℝ) (ht : t ∈ Icc 0 conditionalEnd) :
    ∃ hf : MemLp (fixedMean d j ρ t) 2 (seedMeasure d),
      ‖conditionalMeanLp d j ρ t - hf.toLp (fixedMean d j ρ t)‖ ≤
        (3 * d.ell +
          (conditionalData d ρ).r * conditionalEnd * d.ell *
            SamplingCenterLp.amplification (conditionalData d ρ) *
            ((conditionalData d ρ).r * d.ell * conditionalEnd)) *
          (d.r * d.G.rho ρ) * ‖backwardLp d j (d.G.rho ρ)‖ := by
  obtain ⟨hc,_⟩ := fixedMean_centered_le d j ρ t ht
  let hf : MemLp (fixedMean d j ρ t) 2 (seedMeasure d) := by
    have h := hc.add (memLp_const
      (Gibbs.primitiveMean d.F d.x (conditionalData d ρ).r))
    have he : (fun ω => fixedMean d j ρ t ω -
        Gibbs.primitiveMean d.F d.x (conditionalData d ρ).r) +
        (fun _ : Seed d => Gibbs.primitiveMean d.F d.x (conditionalData d ρ).r) =
        fixedMean d j ρ t := by
      funext ω
      simp only [Pi.add_apply, sub_add_cancel]
    rw [he] at h
    exact h
  refine ⟨hf, ?_⟩
  let hd := (MeanFlowLp.conditionalMean_memLp d j ρ t).sub hf
  have he : conditionalMeanLp d j ρ t - hf.toLp (fixedMean d j ρ t) =
      hd.toLp (fun ω => conditionalMean d j ρ t ω - fixedMean d j ρ t ω) := by
    unfold hd conditionalMeanLp
    rw [← MemLp.toLp_sub]
    rfl
  rw [he]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hd.coeFn_toLp,
    (MeanFlowLp.backward_memLp d j (d.G.rho ρ)).coeFn_toLp] with ω hdiff hback
  have hdiff' : (hd.toLp (fun ω => conditionalMean d j ρ t ω -
      fixedMean d j ρ t ω)) ω =
      conditionalMean d j ρ t ω - fixedMean d j ρ t ω := hdiff
  have hback' : (backwardLp d j (d.G.rho ρ)) ω =
      backward d j (d.G.rho ρ) ω := hback
  rw [hdiff', hback']
  have hc := conditionalMean_sub_fixed_le d j ρ t ht ω
  have hcenter : conditionalCenter d j ρ ω - d.x =
      (d.r * d.G.rho ρ) • backward d j (d.G.rho ρ) ω := by
    unfold conditionalCenter
    module
  rw [hcenter, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg d.hr.le (d.G.rho_mem ρ).1)] at hc
  simpa only [mul_assoc] using hc

/-- The comparison mean itself is paid by one original-center primitive mean
and the fixed-center covariance fluctuation. -/
theorem norm_fixedMean_le (d : Data ι m) (j : Fin m)
    (ρ : d.G.Kernel) (t : ℝ) (ht : t ∈ Icc 0 conditionalEnd) :
    ∃ hf : MemLp (fixedMean d j ρ t) 2 (seedMeasure d),
      ‖hf.toLp (fixedMean d j ρ t)‖ ≤
        ‖Gibbs.primitiveMean d.F d.x (conditionalData d ρ).r‖ +
          Real.exp 1 * ((conditionalData d ρ).r * d.ell) *
            Real.sqrt (Module.finrank ℝ E) := by
  obtain ⟨hc,hcb⟩ := fixedMean_centered_le d j ρ t ht
  let c := Gibbs.primitiveMean d.F d.x (conditionalData d ρ).r
  let hb : MemLp (fun _ : Seed d => c) 2 (seedMeasure d) := memLp_const c
  have he : (fun ω => fixedMean d j ρ t ω - c) +
      (fun _ : Seed d => c) = fixedMean d j ρ t := by
    funext ω
    simp only [Pi.add_apply, sub_add_cancel]
  let hf : MemLp (fixedMean d j ρ t) 2 (seedMeasure d) := he ▸ hc.add hb
  refine ⟨hf, ?_⟩
  have heLp : hf.toLp (fixedMean d j ρ t) =
      hc.toLp (fun ω => fixedMean d j ρ t ω - c) + hb.toLp (fun _ => c) := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    filter_upwards [] with ω
    simp only [Pi.add_apply, sub_add_cancel]
  rw [heLp]
  have htri := norm_add_le
    (hc.toLp (fun ω => fixedMean d j ρ t ω - c)) (hb.toLp (fun _ => c))
  have hconst := Lp.norm_const («E» := E) (μ := seedMeasure d) (p := 2)
    (c := c) (by norm_num)
  have hbLp : hb.toLp (fun _ => c) = Lp.const 2 (seedMeasure d) c := rfl
  rw [hbLp, hconst] at htri
  simp only [probReal_univ, Real.one_rpow, mul_one] at htri
  rw [hbLp]
  linarith

/-- The actual random-center conditional mean has a finite, explicit L²
budget from the proved seed coupling and fixed-center covariance estimate. -/
theorem norm_conditionalMeanLp_le (d : Data ι m) (j : Fin m)
    (ρ : d.G.Kernel) (t : ℝ) (ht : t ∈ Icc 0 conditionalEnd) :
    ‖conditionalMeanLp d j ρ t‖ ≤
      ‖Gibbs.primitiveMean d.F d.x (conditionalData d ρ).r‖ +
        Real.exp 1 * ((conditionalData d ρ).r * d.ell) *
          Real.sqrt (Module.finrank ℝ E) +
        (3 * d.ell +
          (conditionalData d ρ).r * conditionalEnd * d.ell *
            SamplingCenterLp.amplification (conditionalData d ρ) *
            ((conditionalData d ρ).r * d.ell * conditionalEnd)) *
          (d.r * d.G.rho ρ) * ‖backwardLp d j (d.G.rho ρ)‖ := by
  obtain ⟨hf,hfixed⟩ := norm_fixedMean_le d j ρ t ht
  obtain ⟨hf',hdiff⟩ := norm_conditionalMeanLp_sub_fixed_le d j ρ t ht
  have he : hf' = hf := Subsingleton.elim _ _
  rw [he] at hdiff
  have htri := norm_add_le
    (conditionalMeanLp d j ρ t - hf.toLp (fixedMean d j ρ t))
    (hf.toLp (fixedMean d j ρ t))
  rw [sub_add_cancel] at htri
  linarith

omit [DecidableEq ι] in
/-- The conditional fiber's base primitive mean is bounded by the original
center gradient through the same source moment estimate as other queries. -/
theorem norm_conditional_primitiveMean_le (d : Data ι m) (ρ : d.G.Kernel) :
    ‖Gibbs.primitiveMean d.F d.x (conditionalData d ρ).r‖ ≤ meanBudget d := by
  let q := (conditionalData d ρ).r
  have hq : 0 < q := (conditionalData d ρ).hr
  have hv : 0 ≤ d.G.variance ρ := (d.G.variance_pos ρ).le
  have hv1 : d.G.variance ρ ≤ 1 := by
    unfold MeanGeometry.variance
    nlinarith [sq_nonneg (d.G.rho ρ)]
  have hqr : q ≤ d.r := by
    change d.r * Real.sqrt (d.G.variance ρ) ≤ d.r
    exact mul_le_of_le_one_right d.hr.le (Real.sqrt_le_one.mpr hv1)
  have hb := Gibbs.norm_primitiveMean_sub_gradient_le_rms
    d.hF d.hell d.hlo d.hup hq.le d.x
  have hm := Gibbs.primitive_second_moment_le
    d.hF d.hell d.hlo d.hup hq d.x
  have htri := norm_add_le
    (Gibbs.primitiveMean d.F d.x q - gradient d.F d.x)
    (gradient d.F d.x)
  rw [sub_add_cancel] at htri
  have hmul := mul_le_mul_of_nonneg_left hm
    (mul_nonneg d.hell hq.le)
  calc
    _ ≤ ‖gradient d.F d.x‖ + (d.ell * q) *
        (Real.sqrt (Module.finrank ℝ E) + q * ‖gradient d.F d.x‖) := by
      linarith
    _ ≤ meanBudget d := by
      dsimp [meanBudget, radiusBudget]
      gcongr
      · exact mul_nonneg d.hell d.hr.le
      · exact d.hell

/-- A uniform original-data size bound for the actual backward state at a
conditional kernel time. -/
theorem norm_backwardLp_at_rho_le (d : Data ι m) (j : Fin m)
    (ρ : d.G.Kernel) :
    ‖backwardLp d j (d.G.rho ρ)‖ ≤
      seedBudget d +
      |centerNode j| * ((d.sigma / 2)⁻¹ *
        CenteringFlowLp.alpha (kernelData d) * backwardEnd d.G.R *
        Real.sqrt (Module.finrank ℝ E)) +
      d.r * |d.G.rho ρ - backwardEnd d.G.R| *
        (meanBudget d + Real.exp 1 * (d.r * d.ell) *
          Real.sqrt (Module.finrank ℝ E)) := by
  have hmove := norm_backwardLp_sub_initial_le_data d j (d.G.rho ρ)
    ⟨(d.G.rho_mem ρ).1, (d.G.rho_mem ρ).2.le⟩
  have hseed := norm_initialPosition_le d
  have htri := norm_add_le
    (backwardLp d j (d.G.rho ρ) - initialPosition d) (initialPosition d)
  rw [sub_add_cancel] at htri
  change ‖initialPosition d‖ ≤ seedBudget d at hseed
  linarith

/-- Entirely original-data conditional mean envelope. The coefficients retain
the physical conditional radius and the backward center's factor `r rho`. -/
def conditionalMeanBudget (d : Data ι m) (j : Fin m)
    (ρ : d.G.Kernel) : ℝ :=
  meanBudget d +
    Real.exp 1 * ((conditionalData d ρ).r * d.ell) *
      Real.sqrt (Module.finrank ℝ E) +
    (3 * d.ell +
      (conditionalData d ρ).r * conditionalEnd * d.ell *
        SamplingCenterLp.amplification (conditionalData d ρ) *
        ((conditionalData d ρ).r * d.ell * conditionalEnd)) *
      (d.r * d.G.rho ρ) *
      (seedBudget d +
        |centerNode j| * ((d.sigma / 2)⁻¹ *
          CenteringFlowLp.alpha (kernelData d) * backwardEnd d.G.R *
          Real.sqrt (Module.finrank ℝ E)) +
        d.r * |d.G.rho ρ - backwardEnd d.G.R| *
          (meanBudget d + Real.exp 1 * (d.r * d.ell) *
            Real.sqrt (Module.finrank ℝ E)))

/-- The actual conditional mean is uniformly L²-bounded at every local time
by its original-data envelope, with no supplied mean or reference norm. -/
theorem norm_conditionalMeanLp_le_data (d : Data ι m) (j : Fin m)
    (ρ : d.G.Kernel) (t : ℝ) (ht : t ∈ Icc 0 conditionalEnd) :
    ‖conditionalMeanLp d j ρ t‖ ≤ conditionalMeanBudget d j ρ := by
  have hm := norm_conditionalMeanLp_le d j ρ t ht
  have hp := norm_conditional_primitiveMean_le d ρ
  have hb := norm_backwardLp_at_rho_le d j ρ
  have hC : 0 ≤ 3 * d.ell +
      (conditionalData d ρ).r * conditionalEnd * d.ell *
        SamplingCenterLp.amplification (conditionalData d ρ) *
        ((conditionalData d ρ).r * d.ell * conditionalEnd) := by
    have hq : 0 ≤ (conditionalData d ρ).r := (conditionalData d ρ).hr.le
    have hA : 0 ≤ SamplingCenterLp.amplification (conditionalData d ρ) :=
      (Real.exp_pos _).le
    have hEnd : 0 ≤ conditionalEnd := conditionalEnd_pos.le
    have hL : 0 ≤ d.ell := d.hell
    positivity
  have hcoef : 0 ≤ (3 * d.ell +
      (conditionalData d ρ).r * conditionalEnd * d.ell *
        SamplingCenterLp.amplification (conditionalData d ρ) *
        ((conditionalData d ρ).r * d.ell * conditionalEnd)) *
        (d.r * d.G.rho ρ) :=
    mul_nonneg hC (mul_nonneg d.hr.le (d.G.rho_mem ρ).1)
  have hprod := mul_le_mul_of_nonneg_left hb hcoef
  dsimp only [conditionalMeanBudget]
  nlinarith

/-- The conditional flow integral pays its actual time span and a single
uniform data budget, independently of quadrature mesh size. -/
theorem norm_conditionalMean_integral_le (d : Data ι m) (j : Fin m)
    (ρ : d.G.Kernel) (a : ℝ) (ha : a ∈ Icc 0 conditionalEnd) :
    ‖∫ t in 0..a, conditionalMeanLp d j ρ t‖ ≤
      |a| * conditionalMeanBudget d j ρ := by
  have hs : ∀ t ∈ uIoc 0 a,
      ‖conditionalMeanLp d j ρ t‖ ≤ conditionalMeanBudget d j ρ := by
    intro t ht
    have ht' : t ∈ Ioc 0 a := by
      simpa [uIoc_of_le ha.1] using ht
    exact norm_conditionalMeanLp_le_data d j ρ t
      ⟨ht'.1.le, ht'.2.trans ha.2⟩
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hs
  simpa only [sub_zero, mul_comm] using h

/-- Fully priced conditional observation row: both state displacements retain
their physical `r` factors, and every mean term is from original data. -/
theorem norm_conditional_sub_direct_le_data (d : Data ι m) (j : Fin m)
    (ρ : d.G.Kernel) (i : (d.G.conditional ρ).Source m) :
    ‖reference d (.conditional d.G j ρ i) -
      (lpGraph d).direct (.conditional d.G j ρ i)‖ ≤
      (d.r * d.G.rho ρ) *
        (|centerNode j| * ((d.sigma / 2)⁻¹ *
          CenteringFlowLp.alpha (kernelData d) * backwardEnd d.G.R *
          Real.sqrt (Module.finrank ℝ E)) +
          d.r * |d.G.rho ρ - backwardEnd d.G.R| *
            (meanBudget d + Real.exp 1 * (d.r * d.ell) *
              Real.sqrt (Module.finrank ℝ E))) +
      (d.r * Real.sqrt (d.G.variance ρ) *
        (d.G.conditional ρ).location m i) *
        ((d.r * Real.sqrt (d.G.variance ρ)) *
          |(d.G.conditional ρ).location m i| * conditionalMeanBudget d j ρ) := by
  have hrow := norm_conditional_sub_direct_le d j ρ i
  have hb := norm_backwardLp_sub_initial_le_data d j (d.G.rho ρ)
    ⟨(d.G.rho_mem ρ).1, (d.G.rho_mem ρ).2.le⟩
  have hi := (d.G.conditional ρ).location_mem_interval m i
  have hc := norm_conditionalMean_integral_le d j ρ
    ((d.G.conditional ρ).location m i) ⟨hi.1.le, hi.2.le⟩
  have hρ : 0 ≤ d.r * d.G.rho ρ :=
    mul_nonneg d.hr.le (d.G.rho_mem ρ).1
  have hq : 0 ≤ d.r * Real.sqrt (d.G.variance ρ) :=
    mul_nonneg d.hr.le (Real.sqrt_nonneg _)
  have hη : 0 ≤ d.r * Real.sqrt (d.G.variance ρ) *
      (d.G.conditional ρ).location m i :=
    mul_nonneg hq hi.1.le
  have hback := mul_le_mul_of_nonneg_left hb hρ
  have hcond := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hc hq) hη
  nlinarith

/-- The forward observation row is now priced entirely by original data and
the exact conditional covariance budget. No row mass or mesh inverse appears. -/
theorem norm_forward_sub_direct_le_data (d : Data ι m) (j : Fin m)
    (ρ : d.G.Kernel) (z : Fin m) (i : (d.G.forward ρ).Source m) :
    ‖reference d (.forward d.G j ρ z i) -
      (lpGraph d).direct (.forward d.G j ρ z i)‖ ≤
      (d.r * (d.G.forward ρ).location m i) *
        (|centerNode j| * ((d.sigma / 2)⁻¹ *
          CenteringFlowLp.alpha (kernelData d) * backwardEnd d.G.R *
          Real.sqrt (Module.finrank ℝ E)) +
          d.r * |d.G.rho ρ - backwardEnd d.G.R| *
            (meanBudget d + Real.exp 1 * (d.r * d.ell) *
              Real.sqrt (Module.finrank ℝ E)) +
          d.G.angleNode z *
            (|centerNode j| * ((d.sigma / 2)⁻¹ *
              CenteringFlowLp.alpha (kernelData d) *
              Real.sqrt (Module.finrank ℝ E))) +
          d.G.seedRot ρ (d.G.angleNode z) *
            ((d.r * Real.sqrt (d.G.variance ρ)) *
              (|conditionalEnd| * conditionalMeanBudget d j ρ)) +
          d.r * |(d.G.forward ρ).location m i - d.G.rho ρ| *
            (meanBudget d + Real.exp 1 * (d.r * d.ell) *
              Real.sqrt (Module.finrank ℝ E))) := by
  have hrow := norm_forward_sub_direct_le d j ρ z i
  have hb := norm_backwardLp_sub_initial_le_data d j (d.G.rho ρ)
    ⟨(d.G.rho_mem ρ).1, (d.G.rho_mem ρ).2.le⟩
  have hs := norm_score_increment_le d 0 (centerNode j)
  rw [scoreLp_initial] at hs
  change ‖scoreLp d (centerNode j) - initialScore d‖ ≤ _ at hs
  simp only [sub_zero] at hs
  have hc := norm_conditionalMean_integral_le d j ρ conditionalEnd
    ⟨conditionalEnd_pos.le, le_rfl⟩
  have hq : 0 ≤ d.r * Real.sqrt (d.G.variance ρ) :=
    mul_nonneg d.hr.le (Real.sqrt_nonneg _)
  have hangle : 0 ≤ d.G.angleNode z := (d.G.angleNode_bounds z).1
  have hseed : 0 ≤ d.G.seedRot ρ (d.G.angleNode z) :=
    d.G.seedRot_nonneg ρ _
  have hforward : 0 ≤ d.r * (d.G.forward ρ).location m i :=
    mul_nonneg d.hr.le ((d.G.rho_mem ρ).1.trans
      ((d.G.forward ρ).location_mem_interval m i).1.le)
  have hs' := mul_le_mul_of_nonneg_left hs hangle
  have hc' := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hc hq) hseed
  have hsum := add_le_add (add_le_add hb hs') hc'
  have hsum' := add_le_add_left hsum
    (d.r * |(d.G.forward ρ).location m i - d.G.rho ρ| *
      (meanBudget d + Real.exp 1 * (d.r * d.ell) *
        Real.sqrt (Module.finrank ℝ E)))
  have htotal := mul_le_mul_of_nonneg_left hsum' hforward
  exact hrow.trans htotal

end AcceleratedLogConcave.Numerics.SmoothConditionalMeanBudget
