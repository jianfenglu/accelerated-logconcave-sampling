import AcceleratedLogConcave.Numerics.MeanInitialError
import AcceleratedLogConcave.Numerics.CenterMeanSourceModulus
import AcceleratedLogConcave.Numerics.RotatedMarginalLaw
import AcceleratedLogConcave.Conditional.RecursiveReferenceCovariance

/-!
# Physical displacement of exact mean centers from their direct anchors

These identities compare the original common-seed reference with the literal
direct graph vector. They preserve the outer physical scale `r`; no row-mass
or quadrature estimate enters the comparison.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory AcceleratedLogConcave
open Numerics Numerics.MeanFlowLp Numerics.MeanResidualBridge Numerics.AffineGraph
open Numerics.AffineGraph.MeanGeometry Numerics.MeanCollocationLp
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace AcceleratedLogConcave.Numerics.SmoothReferenceDisplacement
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

/-- Each exact backward state retains its interpolation marginal on the
original product seed, at every time in the physical backward interval. -/
theorem backward_preserving (d : Data ι m) (j : Fin m) (t : ℝ)
    (ht : t ∈ Icc 0 (backwardEnd d.G.R)) :
    MeasurePreserving (backward d j t) (seedMeasure d)
      (Conditional.interpolationLaw d.F d.x d.r t) := by
  have hp : MeasurePreserving (position d (centerNode j)) (seedMeasure d)
      (Conditional.interpolationLaw d.F d.x d.r (backwardEnd d.G.R)) :=
    (CenteringFlowLp.position_preserving (kernelData d)).comp
      (kernel_phase_preserving d (centerNode j))
  have hf := TransportFlowLp.flow_preserving (transportData d) d.x
    ⟨backwardEnd d.G.R, d.G.backwardEnd_pos.le, le_rfl⟩ ht
  exact hf.comp hp

/-- A dimension-explicit posterior-mean budget at any interpolation time.
The input is the actual interpolation law, not an arbitrary curve. -/
theorem norm_conditionalMean_centered_law_le (d : Data ι m) (t : ℝ)
    (ht : t ∈ Icc 0 (backwardEnd d.G.R)) :
    ∃ hg : MemLp (fun y => Conditional.conditionalMean d.F d.x d.r t y -
        Gibbs.primitiveMean d.F d.x d.r) 2
        (Conditional.interpolationLaw d.F d.x d.r t),
      ‖hg.toLp (fun y => Conditional.conditionalMean d.F d.x d.r t y -
        Gibbs.primitiveMean d.F d.x d.r)‖ ≤
        (Real.exp 1 * (d.r * d.ell)) *
          Real.sqrt (Module.finrank ℝ E) := by
  let ν := Conditional.interpolationLaw d.F d.x d.r t
  let : IsProbabilityMeasure ν :=
    Conditional.interpolationLaw_isProbabilityMeasure d.hF d.hlo d.x d.r t
  let g : E → E := fun y => Conditional.conditionalMean d.F d.x d.r t y -
    Gibbs.primitiveMean d.F d.x d.r
  let hg : MemLp g 2 ν :=
    (Conditional.RecursiveReferenceCovariance.conditionalMean_memLp
      d.hF d.hell d.hlo d.hup d.x d.hr ht.1
      (ht.2.trans_lt d.G.backwardEnd_lt_one)).sub (memLp_const _)
  have hs := Analysis.DominatedLp.norm_sq_toLp hg
  have hb : (∫ y, ‖g y‖ ^ 2 ∂ν) ≤
      (Real.exp 1 * (d.r * d.ell)) ^ 2 * (Module.finrank ℝ E : ℝ) := by
    have hbase : (∫ z, Conditional.primitiveObservable d.F d.x d.r z
        ∂Conditional.baseLaw d.F d.x d.r) =
        Gibbs.primitiveMean d.F d.x d.r := rfl
    simpa only [g, ν, hbase] using
      Conditional.integral_conditionalMean_centered_norm_sq_le
        d.hF d.hell d.hlo d.hup d.x d.hr ht.1
        (ht.2.trans_lt d.G.backwardEnd_lt_one) d.hsmall
  have hdim := Real.sq_sqrt (Nat.cast_nonneg (Module.finrank ℝ E))
  have ha : 0 ≤ Real.exp 1 * (d.r * d.ell) :=
    mul_nonneg (Real.exp_pos _).le (mul_nonneg d.hr.le d.hell)
  have hr : 0 ≤ Real.exp 1 * (d.r * d.ell) *
      Real.sqrt (Module.finrank ℝ E) := mul_nonneg ha (Real.sqrt_nonneg _)
  refine ⟨hg, ?_⟩
  change ‖hg.toLp g‖ ≤ _
  nlinarith [norm_nonneg (hg.toLp g)]

/-- The same covariance estimate at an arbitrary fixed conditional center and
physical radius. This form can be integrated over the actual random center. -/
theorem norm_conditionalMean_centered_law_le_at (d : Data ι m)
    (x : E) (q : ℝ) (hq : 0 < q) (hsmall : q^2 * d.ell ≤ 1 / 2)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t < 1) :
    ∃ hg : MemLp (fun y => Conditional.conditionalMean d.F x q t y -
        Gibbs.primitiveMean d.F x q) 2
        (Conditional.interpolationLaw d.F x q t),
      ‖hg.toLp (fun y => Conditional.conditionalMean d.F x q t y -
        Gibbs.primitiveMean d.F x q)‖ ≤
        (Real.exp 1 * (q * d.ell)) * Real.sqrt (Module.finrank ℝ E) := by
  let ν := Conditional.interpolationLaw d.F x q t
  let : IsProbabilityMeasure ν :=
    Conditional.interpolationLaw_isProbabilityMeasure d.hF d.hlo x q t
  let g : E → E := fun y => Conditional.conditionalMean d.F x q t y -
    Gibbs.primitiveMean d.F x q
  let hg : MemLp g 2 ν :=
    (Conditional.RecursiveReferenceCovariance.conditionalMean_memLp
      d.hF d.hell d.hlo d.hup x hq ht ht1).sub (memLp_const _)
  have hs := Analysis.DominatedLp.norm_sq_toLp hg
  have hb : (∫ y, ‖g y‖ ^ 2 ∂ν) ≤
      (Real.exp 1 * (q * d.ell)) ^ 2 * (Module.finrank ℝ E : ℝ) := by
    have hbase : (∫ z, Conditional.primitiveObservable d.F x q z
        ∂Conditional.baseLaw d.F x q) = Gibbs.primitiveMean d.F x q := rfl
    simpa only [g, ν, hbase] using
      Conditional.integral_conditionalMean_centered_norm_sq_le
        d.hF d.hell d.hlo d.hup x hq ht ht1 hsmall
  have hdim := Real.sq_sqrt (Nat.cast_nonneg (Module.finrank ℝ E))
  have ha : 0 ≤ Real.exp 1 * (q * d.ell) :=
    mul_nonneg (Real.exp_pos _).le (mul_nonneg hq.le d.hell)
  have hr : 0 ≤ Real.exp 1 * (q * d.ell) *
      Real.sqrt (Module.finrank ℝ E) := mul_nonneg ha (Real.sqrt_nonneg _)
  refine ⟨hg, ?_⟩
  change ‖hg.toLp g‖ ≤ _
  nlinarith [norm_nonneg (hg.toLp g)]

omit [DecidableEq ι] in
/-- Each conditional fiber inherits the original small-radius premise. -/
theorem conditional_radius_small (d : Data ι m) (ρ : d.G.Kernel) :
    ((conditionalData d ρ).r)^2 * d.ell ≤ 1 / 2 := by
  have hv : 0 ≤ d.G.variance ρ := (d.G.variance_pos ρ).le
  have hv1 : d.G.variance ρ ≤ 1 := by
    unfold MeanGeometry.variance
    nlinarith [sq_nonneg (d.G.rho ρ)]
  have hq : ((conditionalData d ρ).r)^2 = d.r^2 * d.G.variance ρ := by
    change (d.r * Real.sqrt (d.G.variance ρ))^2 = _
    rw [mul_pow, Real.sq_sqrt hv]
  rw [hq]
  have hbase : 0 ≤ d.r^2 * d.ell :=
    mul_nonneg (sq_nonneg _) d.hell
  nlinarith [mul_nonneg (sub_nonneg.mpr hv1) hbase, d.hsmall]

/-- The same stationary phase flow controls score movement from the actual
Gaussian seed, independently of the collocation mesh. -/
theorem norm_score_increment_le (d : Data ι m) (a b : ℝ) :
    ‖scoreLp d b - scoreLp d a‖ ≤
      |b - a| * ((d.sigma / 2)⁻¹ *
        CenteringFlowLp.alpha (kernelData d) *
        Real.sqrt (Module.finrank ℝ E)) := by
  rw [scoreLp_eq, scoreLp_eq, ← map_sub]
  have hn (z : Lp E 2 (KernelFlowLp.seedMeasure (kernelData d))) :
      ‖phasePullback d z‖ = ‖z‖ :=
    Lp.norm_compMeasurePreserving z (phase_projection_preserving d)
  rw [hn]
  exact CenteringFlowLp.norm_momentumLp_sub_le (kernelData d)
    (d.sigma / 2) (half_pos d.hsigma) a b

/-- The backward primitive mean, centered at the original base mean, has a
uniform L² bound from the proved interpolation marginal and original C² data. -/
theorem norm_backwardMeanLp_sub_offset_le (d : Data ι m) (j : Fin m) (t : ℝ)
    (ht : t ∈ Icc 0 (backwardEnd d.G.R)) :
    ‖backwardMeanLp d j t - offsetLp d‖ ≤
      (Real.exp 1 * (d.r * d.ell)) *
        Real.sqrt (Module.finrank ℝ E) := by
  let g : E → E := fun y => Conditional.conditionalMean d.F d.x d.r t y -
    Gibbs.primitiveMean d.F d.x d.r
  obtain ⟨hg, hnorm⟩ := norm_conditionalMean_centered_law_le d t ht
  have hmp := backward_preserving d j t ht
  let hcomp := hg.comp_measurePreserving hmp
  have he : backwardMeanLp d j t - offsetLp d =
      hcomp.toLp (g ∘ backward d j t) := by
    unfold backwardMeanLp offsetLp
    rw [← MemLp.toLp_sub]
    apply MemLp.toLp_congr
    filter_upwards [] with ω
    change backwardMean d j t ω - Gibbs.primitiveMean d.F d.x d.r =
      g (backward d j t ω)
    change Gibbs.primitiveMean d.F
      (d.x + (d.r * SamplingFlowLp.sourceTime d.G.backwardEnd_pos.le t) •
        backward d j t ω)
      (d.r * Real.sqrt (1 - (SamplingFlowLp.sourceTime d.G.backwardEnd_pos.le t)^2)) -
        Gibbs.primitiveMean d.F d.x d.r = _
    rw [SamplingFlowLp.sourceTime_eq d.G.backwardEnd_pos.le ht]
    exact congrArg (fun u => u - Gibbs.primitiveMean d.F d.x d.r)
      (AffineFlowIdentities.conditionalMean_eq_primitiveMean
        d.hF d.hell d.hlo d.hup d.x d.hr (by linarith [ht.1])
        (ht.2.trans_lt d.G.backwardEnd_lt_one) (backward d j t ω)).symm
  rw [he]
  exact (Lp.norm_compMeasurePreserving (hg.toLp g) hmp).trans_le hnorm

/-- The entire backward primitive mean is paid by the base primitive mean
and the actual interpolation-law fluctuation. -/
theorem norm_backwardMeanLp_le (d : Data ι m) (j : Fin m) (t : ℝ)
    (ht : t ∈ Icc 0 (backwardEnd d.G.R)) :
    ‖backwardMeanLp d j t‖ ≤
      ‖offsetLp d‖ + (Real.exp 1 * (d.r * d.ell)) *
        Real.sqrt (Module.finrank ℝ E) := by
  have htri := norm_add_le (backwardMeanLp d j t - offsetLp d) (offsetLp d)
  rw [sub_add_cancel] at htri
  have hb := norm_backwardMeanLp_sub_offset_le d j t ht
  linarith

omit [DecidableEq ι] in
/-- The base primitive mean itself has the explicit original-center gradient
bound already proved for the actual primitive operator. -/
theorem norm_offsetLp_le (d : Data ι m) : ‖offsetLp d‖ ≤ meanBudget d := by
  have h := norm_operator_zero_le d (.base d.G)
  change ‖operator d 0 d.r‖ ≤ meanBudget d at h
  rw [← MeanResidualBridge.offset_eq d _ (primitiveLp_spec _ _)]
  exact h

/-- A fully public-data mean envelope, uniform in backward time. -/
theorem norm_backwardMeanLp_le_data (d : Data ι m) (j : Fin m) (t : ℝ)
    (ht : t ∈ Icc 0 (backwardEnd d.G.R)) :
    ‖backwardMeanLp d j t‖ ≤
      meanBudget d + (Real.exp 1 * (d.r * d.ell)) *
        Real.sqrt (Module.finrank ℝ E) :=
  (norm_backwardMeanLp_le d j t ht).trans (add_le_add (norm_offsetLp_le d) le_rfl)

/-- The exact forward state has the same interpolation marginal as the
backward state, after the proved Gaussian rotation identity. -/
theorem forward_preserving_at (d : Data ι m) (j : Fin m) (ρ : d.G.Kernel)
    (z t : ℝ) (ht : t ∈ Icc 0 (backwardEnd d.G.R)) :
    MeasurePreserving (forward d j ρ z t) (seedMeasure d)
      (Conditional.interpolationLaw d.F d.x d.r t) := by
  have h := MeanFlowLp.forward_preserving d j ρ z t
  rw [SamplingFlowLp.sourceTime_eq d.G.backwardEnd_pos.le ht] at h
  exact h

/-- The forward primitive mean has the same original-data L² envelope,
uniformly in the angle and physical forward time. -/
theorem norm_forwardMeanLp_le_data (d : Data ι m) (j : Fin m)
    (ρ : d.G.Kernel) (z t : ℝ) (ht : t ∈ Icc 0 (backwardEnd d.G.R)) :
    ‖forwardMeanLp d j ρ z t‖ ≤
      meanBudget d + Real.exp 1 * (d.r * d.ell) *
        Real.sqrt (Module.finrank ℝ E) := by
  let g : E → E := fun y => Conditional.conditionalMean d.F d.x d.r t y -
    Gibbs.primitiveMean d.F d.x d.r
  obtain ⟨hg, hnorm⟩ := norm_conditionalMean_centered_law_le d t ht
  have hmp := forward_preserving_at d j ρ z t ht
  let hcomp := hg.comp_measurePreserving hmp
  have he : forwardMeanLp d j ρ z t - offsetLp d =
      hcomp.toLp (g ∘ forward d j ρ z t) := by
    unfold forwardMeanLp offsetLp
    rw [← MemLp.toLp_sub]
    apply MemLp.toLp_congr
    filter_upwards [] with ω
    change forwardMean d j ρ z t ω - Gibbs.primitiveMean d.F d.x d.r =
      g (forward d j ρ z t ω)
    change Gibbs.primitiveMean d.F
      (d.x + (d.r * SamplingFlowLp.sourceTime d.G.backwardEnd_pos.le t) •
        forward d j ρ z t ω)
      (d.r * Real.sqrt (1 - (SamplingFlowLp.sourceTime d.G.backwardEnd_pos.le t)^2)) -
        Gibbs.primitiveMean d.F d.x d.r = _
    rw [SamplingFlowLp.sourceTime_eq d.G.backwardEnd_pos.le ht]
    exact congrArg (fun u => u - Gibbs.primitiveMean d.F d.x d.r)
      (AffineFlowIdentities.conditionalMean_eq_primitiveMean
        d.hF d.hell d.hlo d.hup d.x d.hr (by linarith [ht.1])
        (ht.2.trans_lt d.G.backwardEnd_lt_one) (forward d j ρ z t ω)).symm
  have hcenter : ‖forwardMeanLp d j ρ z t - offsetLp d‖ ≤
      Real.exp 1 * (d.r * d.ell) * Real.sqrt (Module.finrank ℝ E) := by
    rw [he]
    exact (Lp.norm_compMeasurePreserving (hg.toLp g) hmp).trans_le hnorm
  have htri := norm_add_le (forwardMeanLp d j ρ z t - offsetLp d) (offsetLp d)
  rw [sub_add_cancel] at htri
  have hbase := norm_offsetLp_le d
  linarith

/-- The backward transport integral is bounded directly on its actual time
interval, with no inverse mesh width. -/
theorem norm_backwardMean_integral_le (d : Data ι m) (j : Fin m) (a : ℝ)
    (ha : a ∈ Icc 0 (backwardEnd d.G.R)) :
    ‖∫ t in backwardEnd d.G.R..a, backwardMeanLp d j t‖ ≤
      |a - backwardEnd d.G.R| *
        (meanBudget d + (Real.exp 1 * (d.r * d.ell)) *
          Real.sqrt (Module.finrank ℝ E)) := by
  have hs : ∀ t ∈ uIoc (backwardEnd d.G.R) a,
      ‖backwardMeanLp d j t‖ ≤
        meanBudget d + Real.exp 1 * (d.r * d.ell) *
          Real.sqrt (Module.finrank ℝ E) := by
    intro t ht
    apply norm_backwardMeanLp_le_data d j t
    have hb : a ≤ backwardEnd d.G.R := ha.2
    have ht' : t ∈ Ioc a (backwardEnd d.G.R) := by
      simpa [uIoc_comm, uIoc_of_le hb] using ht
    exact ⟨ha.1.trans ht'.1.le, ht'.2⟩
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hs
  simpa only [mul_comm] using h

/-- The forward transport integral has the same explicit uniform mean
envelope, independent of its angle and mesh discretization. -/
theorem norm_forwardMean_integral_le (d : Data ι m) (j : Fin m)
    (ρ : d.G.Kernel) (z a : ℝ)
    (ha : a ∈ Icc (d.G.rho ρ) (backwardEnd d.G.R)) :
    ‖∫ t in d.G.rho ρ..a, forwardMeanLp d j ρ z t‖ ≤
      |a - d.G.rho ρ| *
        (meanBudget d + Real.exp 1 * (d.r * d.ell) *
          Real.sqrt (Module.finrank ℝ E)) := by
  have hs : ∀ t ∈ uIoc (d.G.rho ρ) a,
      ‖forwardMeanLp d j ρ z t‖ ≤
        meanBudget d + Real.exp 1 * (d.r * d.ell) *
          Real.sqrt (Module.finrank ℝ E) := by
    intro t ht
    have ht' : t ∈ Ioc (d.G.rho ρ) a := by
      simpa [uIoc_of_le ha.1] using ht
    apply norm_forwardMeanLp_le_data d j ρ z t
    exact ⟨(d.G.rho_mem ρ).1.trans ht'.1.le, ht'.2.trans ha.2⟩
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hs
  simpa only [mul_comm] using h

/-- The base request carries no displacement. -/
theorem base_eq_direct (d : Data ι m) :
    reference d (.base d.G) = (lpGraph d).direct (.base d.G) := by
  change (curves d).reference d.G 0 d.r (.base d.G) =
    d.G.direct d.r d.sigma 0 (initialPosition d) (initialScore d)
      (initialNoise d) (.base d.G)
  rw [MeanGeometry.direct_base]
  rfl

/-- Exact cancellation of the direct center anchor. This is an identity in
the canonical common-seed `L²` space. -/
theorem center_sub_direct (d : Data ι m) (j : Fin m) :
    reference d (.center d.G j) - (lpGraph d).direct (.center d.G j) =
      (d.r * backwardEnd d.G.R) •
        (positionLp d (centerNode j) - initialPosition d) := by
  change (curves d).reference d.G 0 d.r (.center d.G j) -
    d.G.direct d.r d.sigma 0 (initialPosition d) (initialScore d)
      (initialNoise d) (.center d.G j) = _
  rw [MeanGeometry.direct_center]
  change (0 + (d.r * backwardEnd d.G.R) • positionLp d (centerNode j)) -
      (0 + (d.r * backwardEnd d.G.R) • initialPosition d) = _
  simp only [zero_add, smul_sub]

/-- The exact center displacement has the physical factor `r`; its bound uses
the proved stationary centering movement on the same seed. -/
theorem norm_center_sub_direct_le (d : Data ι m) (j : Fin m) :
    ‖reference d (.center d.G j) - (lpGraph d).direct (.center d.G j)‖ ≤
      (d.r * backwardEnd d.G.R) *
        (|centerNode j| * ((d.sigma / 2)⁻¹ *
          CenteringFlowLp.alpha (kernelData d) * backwardEnd d.G.R *
          Real.sqrt (Module.finrank ℝ (EuclideanSpace ℝ ι)))) := by
  rw [center_sub_direct, norm_smul, Real.norm_eq_abs]
  have hc : 0 ≤ d.r * backwardEnd d.G.R :=
    mul_nonneg d.hr.le d.G.backwardEnd_pos.le
  rw [abs_of_nonneg hc]
  have hpos := CenterMeanSourceModulus.norm_position_increment_le d 0 (centerNode j)
  rw [positionLp_initial] at hpos
  change ‖positionLp d (centerNode j) - initialPosition d‖ ≤ _ at hpos
  simpa only [sub_zero] using mul_le_mul_of_nonneg_left hpos hc

/-- The backward row differs from its direct anchor by exactly the transported
state displacement, still multiplied by its physical observation coefficient. -/
theorem backward_sub_direct (d : Data ι m) (j : Fin m)
    (i : d.G.backward.Source m) :
    reference d (.backward d.G j i) - (lpGraph d).direct (.backward d.G j i) =
      (d.r * d.G.backward.location m i) •
        (backwardLp d j (d.G.backward.location m i) - initialPosition d) := by
  change (curves d).reference d.G 0 d.r (.backward d.G j i) -
    d.G.direct d.r d.sigma 0 (initialPosition d) (initialScore d)
      (initialNoise d) (.backward d.G j i) = _
  rw [MeanGeometry.direct_backward]
  change (0 + (d.r * d.G.backward.location m i) •
      backwardLp d j (d.G.backward.location m i)) -
      (0 + (d.r * d.G.backward.location m i) • initialPosition d) = _
  simp only [zero_add, smul_sub]

/-- The exact backward transport equation exposes the second, physical `r`
inside its correction, without mesh-width or row-mass losses. -/
theorem backward_sub_direct_integral (d : Data ι m) (j : Fin m)
    (i : d.G.backward.Source m) :
    reference d (.backward d.G j i) - (lpGraph d).direct (.backward d.G j i) =
      (d.r * d.G.backward.location m i) •
        (positionLp d (centerNode j) - initialPosition d -
          d.r • ∫ t in backwardEnd d.G.R..d.G.backward.location m i,
            backwardMeanLp d j t) := by
  rw [backward_sub_direct]
  have hi := d.G.backward.location_mem_interval m i
  have he := backwardLp_equation d j (backwardEnd d.G.R)
    (d.G.backward.location m i)
    ⟨d.G.backwardEnd_pos.le, le_rfl⟩ ⟨hi.1.le, hi.2.le⟩
  rw [backwardLp_initial] at he
  rw [he]
  module

/-- A backward row has one centering displacement and one actual transport
integral. The outer factor `r a` is never discarded. -/
theorem norm_backward_sub_direct_le (d : Data ι m) (j : Fin m)
    (i : d.G.backward.Source m) :
    ‖reference d (.backward d.G j i) - (lpGraph d).direct (.backward d.G j i)‖ ≤
      (d.r * d.G.backward.location m i) *
        (|centerNode j| * ((d.sigma / 2)⁻¹ *
          CenteringFlowLp.alpha (kernelData d) * backwardEnd d.G.R *
          Real.sqrt (Module.finrank ℝ (EuclideanSpace ℝ ι))) +
          d.r * ‖∫ t in backwardEnd d.G.R..d.G.backward.location m i,
            backwardMeanLp d j t‖) := by
  rw [backward_sub_direct_integral, norm_smul, Real.norm_eq_abs]
  have hi := d.G.backward.location_mem_interval m i
  have hc : 0 ≤ d.r * d.G.backward.location m i :=
    mul_nonneg d.hr.le hi.1.le
  rw [abs_of_nonneg hc]
  have hp := CenterMeanSourceModulus.norm_position_increment_le d 0 (centerNode j)
  rw [positionLp_initial] at hp
  change ‖positionLp d (centerNode j) - initialPosition d‖ ≤ _ at hp
  have ht := norm_sub_le (positionLp d (centerNode j) - initialPosition d)
    (d.r • ∫ t in backwardEnd d.G.R..d.G.backward.location m i,
      backwardMeanLp d j t)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos d.hr] at ht
  calc
    _ ≤ (d.r * d.G.backward.location m i) *
      (‖positionLp d (centerNode j) - initialPosition d‖ +
        d.r * ‖∫ t in backwardEnd d.G.R..d.G.backward.location m i,
          backwardMeanLp d j t‖) :=
      mul_le_mul_of_nonneg_left ht hc
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (by simpa only [sub_zero] using hp) le_rfl) hc

/-- The backward physical center displacement is bounded entirely by
original-data moments and the time span, with no quadrature mesh factor. -/
theorem norm_backward_sub_direct_le_data (d : Data ι m) (j : Fin m)
    (i : d.G.backward.Source m) :
    ‖reference d (.backward d.G j i) - (lpGraph d).direct (.backward d.G j i)‖ ≤
      (d.r * d.G.backward.location m i) *
        (|centerNode j| * ((d.sigma / 2)⁻¹ *
          CenteringFlowLp.alpha (kernelData d) * backwardEnd d.G.R *
          Real.sqrt (Module.finrank ℝ E)) +
          d.r * |d.G.backward.location m i - backwardEnd d.G.R| *
            (meanBudget d + Real.exp 1 * (d.r * d.ell) *
              Real.sqrt (Module.finrank ℝ E))) := by
  have hi := d.G.backward.location_mem_interval m i
  have hrow := norm_backward_sub_direct_le d j i
  have hint := norm_backwardMean_integral_le d j (d.G.backward.location m i)
    ⟨hi.1.le, hi.2.le⟩
  have hcoef : 0 ≤ d.r * d.G.backward.location m i :=
    mul_nonneg d.hr.le hi.1.le
  calc
    _ ≤ (d.r * d.G.backward.location m i) *
      (|centerNode j| * ((d.sigma / 2)⁻¹ *
        CenteringFlowLp.alpha (kernelData d) * backwardEnd d.G.R *
        Real.sqrt (Module.finrank ℝ E)) +
        d.r * ‖∫ t in backwardEnd d.G.R..d.G.backward.location m i,
          backwardMeanLp d j t‖) := hrow
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hcoef
      have hh := mul_le_mul_of_nonneg_left hint d.hr.le
      exact add_le_add le_rfl (by simpa only [mul_assoc] using hh)

/-- The backward state displacement itself has a uniform public-data budget.
This is useful at the conditional and rotation junctions, where no row
coefficient should be divided out. -/
theorem norm_backwardLp_sub_initial_le_data (d : Data ι m) (j : Fin m)
    (a : ℝ) (ha : a ∈ Icc 0 (backwardEnd d.G.R)) :
    ‖backwardLp d j a - initialPosition d‖ ≤
      |centerNode j| * ((d.sigma / 2)⁻¹ *
        CenteringFlowLp.alpha (kernelData d) * backwardEnd d.G.R *
        Real.sqrt (Module.finrank ℝ E)) +
      d.r * |a - backwardEnd d.G.R| *
        (meanBudget d + Real.exp 1 * (d.r * d.ell) *
          Real.sqrt (Module.finrank ℝ E)) := by
  have he := backwardLp_equation d j (backwardEnd d.G.R) a
    ⟨d.G.backwardEnd_pos.le, le_rfl⟩ ha
  rw [backwardLp_initial] at he
  rw [he]
  have hp := CenterMeanSourceModulus.norm_position_increment_le d 0 (centerNode j)
  rw [positionLp_initial] at hp
  change ‖positionLp d (centerNode j) - initialPosition d‖ ≤ _ at hp
  have hint := norm_backwardMean_integral_le d j a ha
  have ht := norm_sub_le (positionLp d (centerNode j) - initialPosition d)
    (d.r • ∫ t in backwardEnd d.G.R..a, backwardMeanLp d j t)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos d.hr] at ht
  have he' :
      (positionLp d (centerNode j) - d.r •
          ∫ t in backwardEnd d.G.R..a, backwardMeanLp d j t) - initialPosition d =
        positionLp d (centerNode j) - initialPosition d - d.r •
          ∫ t in backwardEnd d.G.R..a, backwardMeanLp d j t := by
    abel
  rw [he']
  have hh := mul_le_mul_of_nonneg_left hint d.hr.le
  have hp' : ‖positionLp d (centerNode j) - initialPosition d‖ ≤
      |centerNode j| * ((d.sigma / 2)⁻¹ *
        CenteringFlowLp.alpha (kernelData d) * backwardEnd d.G.R *
        Real.sqrt (Module.finrank ℝ E)) := by
    simpa only [sub_zero] using hp
  nlinarith

/-- The conditional observation is a sum of two state displacements. Its
direct Gaussian anchor cancels literally on the common seed. -/
theorem conditional_sub_direct (d : Data ι m) (j : Fin m) (ρ : d.G.Kernel)
    (i : (d.G.conditional ρ).Source m) :
    reference d (.conditional d.G j ρ i) -
        (lpGraph d).direct (.conditional d.G j ρ i) =
      (d.r * d.G.rho ρ) •
        (backwardLp d j (d.G.rho ρ) - initialPosition d) +
      (d.r * Real.sqrt (d.G.variance ρ) * (d.G.conditional ρ).location m i) •
        (conditionalLp d j ρ ((d.G.conditional ρ).location m i) -
          initialNoise d j ρ) := by
  change (curves d).reference d.G 0 d.r (.conditional d.G j ρ i) -
    d.G.direct d.r d.sigma 0 (initialPosition d) (initialScore d)
      (initialNoise d) (.conditional d.G j ρ i) = _
  rw [MeanGeometry.direct_conditional]
  change (0 + (d.r * d.G.rho ρ) • backwardLp d j (d.G.rho ρ) +
      (d.r * Real.sqrt (d.G.variance ρ) * (d.G.conditional ρ).location m i) •
        conditionalLp d j ρ ((d.G.conditional ρ).location m i)) -
      (0 + d.r • (d.G.rho ρ • initialPosition d +
        (Real.sqrt (d.G.variance ρ) * (d.G.conditional ρ).location m i) •
          initialNoise d j ρ)) = _
  module

/-- Substituting the two exact probability-flow equations keeps the explicit
`r` factors and uses no row-mass envelope. -/
theorem conditional_sub_direct_integrals (d : Data ι m) (j : Fin m)
    (ρ : d.G.Kernel) (i : (d.G.conditional ρ).Source m) :
    reference d (.conditional d.G j ρ i) -
        (lpGraph d).direct (.conditional d.G j ρ i) =
      (d.r * d.G.rho ρ) •
        (positionLp d (centerNode j) - initialPosition d -
          d.r • ∫ t in backwardEnd d.G.R..d.G.rho ρ, backwardMeanLp d j t) +
      (d.r * Real.sqrt (d.G.variance ρ) * (d.G.conditional ρ).location m i) •
        (-(d.r * Real.sqrt (d.G.variance ρ)) •
          ∫ t in 0..(d.G.conditional ρ).location m i,
            conditionalMeanLp d j ρ t) := by
  rw [conditional_sub_direct]
  have hrho := d.G.rho_mem ρ
  have hb := backwardLp_equation d j (backwardEnd d.G.R) (d.G.rho ρ)
    ⟨d.G.backwardEnd_pos.le, le_rfl⟩ ⟨hrho.1, hrho.2.le⟩
  rw [backwardLp_initial] at hb
  have hη := (d.G.conditional ρ).location_mem_interval m i
  have hc := conditionalLp_equation d j ρ 0 ((d.G.conditional ρ).location m i)
    ⟨le_rfl, conditionalEnd_pos.le⟩ ⟨hη.1.le, hη.2.le⟩
  rw [conditionalLp_initial] at hc
  change conditionalLp d j ρ ((d.G.conditional ρ).location m i) =
    initialNoise d j ρ - (d.r * Real.sqrt (d.G.variance ρ)) •
      ∫ t in 0..(d.G.conditional ρ).location m i, conditionalMeanLp d j ρ t at hc
  rw [hb, hc]
  module

/-- The conditional row pays exactly for its backward displacement and its
local transport integral, each with its own physical observation factor. -/
theorem norm_conditional_sub_direct_le (d : Data ι m) (j : Fin m)
    (ρ : d.G.Kernel) (i : (d.G.conditional ρ).Source m) :
    ‖reference d (.conditional d.G j ρ i) -
      (lpGraph d).direct (.conditional d.G j ρ i)‖ ≤
      (d.r * d.G.rho ρ) *
        ‖backwardLp d j (d.G.rho ρ) - initialPosition d‖ +
      (d.r * Real.sqrt (d.G.variance ρ) * (d.G.conditional ρ).location m i) *
        ((d.r * Real.sqrt (d.G.variance ρ)) *
          ‖∫ t in 0..(d.G.conditional ρ).location m i,
            conditionalMeanLp d j ρ t‖) := by
  rw [conditional_sub_direct_integrals]
  have h := norm_add_le
    ((d.r * d.G.rho ρ) •
      (positionLp d (centerNode j) - initialPosition d -
        d.r • ∫ t in backwardEnd d.G.R..d.G.rho ρ,
          backwardMeanLp d j t))
    ((d.r * Real.sqrt (d.G.variance ρ) * (d.G.conditional ρ).location m i) •
      (-(d.r * Real.sqrt (d.G.variance ρ)) •
        ∫ t in 0..(d.G.conditional ρ).location m i,
          conditionalMeanLp d j ρ t))
  have hrho : 0 ≤ d.r * d.G.rho ρ :=
    mul_nonneg d.hr.le (d.G.rho_mem ρ).1
  have hη : 0 ≤ d.r * Real.sqrt (d.G.variance ρ) *
      (d.G.conditional ρ).location m i :=
    mul_nonneg (mul_nonneg d.hr.le (Real.sqrt_nonneg _))
      ((d.G.conditional ρ).location_mem_interval m i).1.le
  have hq : 0 ≤ d.r * Real.sqrt (d.G.variance ρ) :=
    mul_nonneg d.hr.le (Real.sqrt_nonneg _)
  rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hrho,
    abs_of_nonneg hη, abs_neg, abs_of_nonneg hq] at h
  have hb := backwardLp_equation d j (backwardEnd d.G.R) (d.G.rho ρ)
    ⟨d.G.backwardEnd_pos.le, le_rfl⟩
    ⟨(d.G.rho_mem ρ).1, (d.G.rho_mem ρ).2.le⟩
  rw [backwardLp_initial] at hb
  rw [hb]
  have he :
      (positionLp d (centerNode j) -
          d.r • ∫ t in backwardEnd d.G.R..d.G.rho ρ, backwardMeanLp d j t) -
          initialPosition d =
        positionLp d (centerNode j) - initialPosition d -
          d.r • ∫ t in backwardEnd d.G.R..d.G.rho ρ, backwardMeanLp d j t := by
    abel
  rw [he]
  exact h

/-- The conditional state leaves its shared Gaussian seed by precisely its
physical-radius times the actual conditional mean integral. -/
theorem norm_conditionalLp_sub_noise_eq (d : Data ι m) (j : Fin m)
    (ρ : d.G.Kernel) :
    ‖conditionalLp d j ρ conditionalEnd - initialNoise d j ρ‖ =
      (d.r * Real.sqrt (d.G.variance ρ)) *
        ‖∫ t in 0..conditionalEnd, conditionalMeanLp d j ρ t‖ := by
  have he := conditionalLp_equation d j ρ 0 conditionalEnd
    ⟨le_rfl, conditionalEnd_pos.le⟩ ⟨conditionalEnd_pos.le, le_rfl⟩
  rw [conditionalLp_initial] at he
  change conditionalLp d j ρ conditionalEnd = initialNoise d j ρ -
    (d.r * Real.sqrt (d.G.variance ρ)) •
      ∫ t in 0..conditionalEnd, conditionalMeanLp d j ρ t at he
  rw [he, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg d.hr.le (Real.sqrt_nonneg _))]

/-- The rotation obtained by setting all mean replies to zero in the actual
forward graph. This contains exactly the shared initial anchors. -/
def forwardAnchor (d : Data ι m) (j : Fin m) (ρ : d.G.Kernel) (z : Fin m) : H d :=
  (1 - (d.G.rotationScale ρ)^2 *
      (1 - Real.cos (d.G.angleNode z / d.G.rotationScale ρ))) •
        initialPosition d +
  (d.G.rotationScale ρ * Real.sin (d.G.angleNode z / d.G.rotationScale ρ)) •
        initialScore d +
  (d.G.rho ρ * Real.sqrt (2 * d.G.variance ρ) *
      (1 - Real.cos (d.G.angleNode z / d.G.rotationScale ρ)) /
      (1 + (d.G.rho ρ)^2)) • initialNoise d j ρ

/-- The actual rotation is linear in its three live state fields, with the
same coefficients as the direct anchor rotation. -/
theorem rotationLp_linear (d : Data ι m) (j : Fin m) (ρ : d.G.Kernel)
    (z : Fin m) :
    rotationLp d j ρ (d.G.angleNode z) =
      (1 - (d.G.rotationScale ρ)^2 *
        (1 - Real.cos (d.G.angleNode z / d.G.rotationScale ρ))) •
          backwardLp d j (d.G.rho ρ) +
      (d.G.rotationScale ρ * Real.sin (d.G.angleNode z / d.G.rotationScale ρ)) •
          scoreLp d (centerNode j) +
      (d.G.rho ρ * Real.sqrt (2 * d.G.variance ρ) *
        (1 - Real.cos (d.G.angleNode z / d.G.rotationScale ρ)) /
        (1 + (d.G.rho ρ)^2)) • conditionalLp d j ρ conditionalEnd := by
  rw [rotationLp_eq]
  dsimp only
  have hs : Real.sqrt (d.G.variance ρ) / conditionalEnd =
      Real.sqrt (2 * d.G.variance ρ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    simp [conditionalEnd, mul_comm]
  rw [hs, d.G.rotationScale_sq]
  unfold MeanGeometry.variance
  match_scalars <;> field_simp <;> ring

/-- Every rotation discrepancy is exactly a weighted sum of the three
underlying state increments; no independent Gaussian or approximate momentum
is introduced. -/
theorem rotation_sub_forwardAnchor (d : Data ι m) (j : Fin m)
    (ρ : d.G.Kernel) (z : Fin m) :
    rotationLp d j ρ (d.G.angleNode z) - forwardAnchor d j ρ z =
      (1 - (d.G.rotationScale ρ)^2 *
        (1 - Real.cos (d.G.angleNode z / d.G.rotationScale ρ))) •
          (backwardLp d j (d.G.rho ρ) - initialPosition d) +
      (d.G.rotationScale ρ * Real.sin (d.G.angleNode z / d.G.rotationScale ρ)) •
          (scoreLp d (centerNode j) - initialScore d) +
      (d.G.rho ρ * Real.sqrt (2 * d.G.variance ρ) *
        (1 - Real.cos (d.G.angleNode z / d.G.rotationScale ρ)) /
        (1 + (d.G.rho ρ)^2)) •
          (conditionalLp d j ρ conditionalEnd - initialNoise d j ρ) := by
  rw [rotationLp_linear]
  unfold forwardAnchor
  module

/-- Rotation preserves the backward coefficient at most one and pays for
score movement only at its physical angle. The conditional state keeps its
exact nonnegative trigonometric coefficient. -/
theorem norm_rotation_sub_forwardAnchor_le (d : Data ι m) (j : Fin m)
    (ρ : d.G.Kernel) (z : Fin m) :
    ‖rotationLp d j ρ (d.G.angleNode z) - forwardAnchor d j ρ z‖ ≤
      ‖backwardLp d j (d.G.rho ρ) - initialPosition d‖ +
      d.G.angleNode z * ‖scoreLp d (centerNode j) - initialScore d‖ +
      d.G.seedRot ρ (d.G.angleNode z) *
        ‖conditionalLp d j ρ conditionalEnd - initialNoise d j ρ‖ := by
  rw [rotation_sub_forwardAnchor]
  have hcoef :
      d.G.rho ρ * Real.sqrt (2 * d.G.variance ρ) *
          (1 - Real.cos (d.G.angleNode z / d.G.rotationScale ρ)) /
          (1 + (d.G.rho ρ)^2) = d.G.seedRot ρ (d.G.angleNode z) := by
    unfold MeanGeometry.seedRot
    ring
  rw [hcoef]
  change ‖d.G.ellRot ρ (d.G.angleNode z) •
      (backwardLp d j (d.G.rho ρ) - initialPosition d) +
      d.G.scoreRot ρ (d.G.angleNode z) •
      (scoreLp d (centerNode j) - initialScore d) +
      d.G.seedRot ρ (d.G.angleNode z) •
      (conditionalLp d j ρ conditionalEnd - initialNoise d j ρ)‖ ≤ _
  have h₁ := norm_add_le
    (d.G.ellRot ρ (d.G.angleNode z) •
      (backwardLp d j (d.G.rho ρ) - initialPosition d) +
      d.G.scoreRot ρ (d.G.angleNode z) •
      (scoreLp d (centerNode j) - initialScore d))
    (d.G.seedRot ρ (d.G.angleNode z) •
      (conditionalLp d j ρ conditionalEnd - initialNoise d j ρ))
  have h₂ := norm_add_le
    (d.G.ellRot ρ (d.G.angleNode z) •
      (backwardLp d j (d.G.rho ρ) - initialPosition d))
    (d.G.scoreRot ρ (d.G.angleNode z) •
      (scoreLp d (centerNode j) - initialScore d))
  simp only [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (d.G.seedRot_nonneg ρ _)] at h₁ h₂
  have hangle : 0 ≤ d.G.angleNode z := (d.G.angleNode_bounds z).1
  have he := d.G.ellRot_abs_le_one ρ (d.G.angleNode z)
  have hs := d.G.scoreRot_abs_le ρ (d.G.angleNode z) hangle
  have he' := mul_le_mul_of_nonneg_right he
    (norm_nonneg (backwardLp d j (d.G.rho ρ) - initialPosition d))
  have hs' := mul_le_mul_of_nonneg_right hs
    (norm_nonneg (scoreLp d (centerNode j) - initialScore d))
  nlinarith

/-- The forward row has the physical factor `r a` outside the difference
between the exact forward state and its literal anchor rotation. -/
theorem forward_sub_direct (d : Data ι m) (j : Fin m) (ρ : d.G.Kernel)
    (z : Fin m) (i : (d.G.forward ρ).Source m) :
    reference d (.forward d.G j ρ z i) -
        (lpGraph d).direct (.forward d.G j ρ z i) =
      (d.r * (d.G.forward ρ).location m i) •
        (forwardLp d j ρ (d.G.angleNode z) ((d.G.forward ρ).location m i) -
          forwardAnchor d j ρ z) := by
  change (curves d).reference d.G 0 d.r (.forward d.G j ρ z i) -
    d.G.direct d.r d.sigma 0 (initialPosition d) (initialScore d)
      (initialNoise d) (.forward d.G j ρ z i) = _
  rw [MeanGeometry.direct_forward]
  change (0 + (d.r * (d.G.forward ρ).location m i) •
      forwardLp d j ρ (d.G.angleNode z) ((d.G.forward ρ).location m i)) -
      (0 + (d.r * (d.G.forward ρ).location m i) • forwardAnchor d j ρ z) = _
  simp only [zero_add, smul_sub]

/-- Its exact flow equation leaves a rotation correction and a physical
`r`-scaled forward mean integral. -/
theorem forward_sub_direct_integral (d : Data ι m) (j : Fin m)
    (ρ : d.G.Kernel) (z : Fin m) (i : (d.G.forward ρ).Source m) :
    reference d (.forward d.G j ρ z i) -
        (lpGraph d).direct (.forward d.G j ρ z i) =
      (d.r * (d.G.forward ρ).location m i) •
        (rotationLp d j ρ (d.G.angleNode z) - forwardAnchor d j ρ z -
          d.r • ∫ t in d.G.rho ρ..(d.G.forward ρ).location m i,
            forwardMeanLp d j ρ (d.G.angleNode z) t) := by
  rw [forward_sub_direct]
  have hrho := d.G.rho_mem ρ
  have hi := (d.G.forward ρ).location_mem_interval m i
  have he := forwardLp_equation d j ρ (d.G.angleNode z) (d.G.rho ρ)
    ((d.G.forward ρ).location m i)
    ⟨hrho.1, hrho.2.le⟩ ⟨hrho.1.trans hi.1.le, hi.2.le⟩
  rw [forwardLp_initial] at he
  rw [he]
  module

/-- A forward row retains its outer physical observation radius. Its rotation
and forward-flow terms are bounded before any collocation row is summed. -/
theorem norm_forward_sub_direct_le (d : Data ι m) (j : Fin m)
    (ρ : d.G.Kernel) (z : Fin m) (i : (d.G.forward ρ).Source m) :
    ‖reference d (.forward d.G j ρ z i) -
      (lpGraph d).direct (.forward d.G j ρ z i)‖ ≤
      (d.r * (d.G.forward ρ).location m i) *
        (‖backwardLp d j (d.G.rho ρ) - initialPosition d‖ +
          d.G.angleNode z * ‖scoreLp d (centerNode j) - initialScore d‖ +
          d.G.seedRot ρ (d.G.angleNode z) *
            ((d.r * Real.sqrt (d.G.variance ρ)) *
              ‖∫ t in 0..conditionalEnd, conditionalMeanLp d j ρ t‖) +
          d.r * |(d.G.forward ρ).location m i - d.G.rho ρ| *
            (meanBudget d + Real.exp 1 * (d.r * d.ell) *
              Real.sqrt (Module.finrank ℝ E))) := by
  rw [forward_sub_direct_integral, norm_smul, Real.norm_eq_abs]
  have hi := (d.G.forward ρ).location_mem_interval m i
  have hcoef : 0 ≤ d.r * (d.G.forward ρ).location m i :=
    mul_nonneg d.hr.le ((d.G.rho_mem ρ).1.trans hi.1.le)
  rw [abs_of_nonneg hcoef]
  have htri := norm_sub_le
    (rotationLp d j ρ (d.G.angleNode z) - forwardAnchor d j ρ z)
    (d.r • ∫ t in d.G.rho ρ..(d.G.forward ρ).location m i,
      forwardMeanLp d j ρ (d.G.angleNode z) t)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos d.hr] at htri
  have hrot := norm_rotation_sub_forwardAnchor_le d j ρ z
  rw [norm_conditionalLp_sub_noise_eq] at hrot
  have hint := norm_forwardMean_integral_le d j ρ (d.G.angleNode z)
    ((d.G.forward ρ).location m i) ⟨hi.1.le, hi.2.le⟩
  have hh := mul_le_mul_of_nonneg_left hint d.hr.le
  have hsum :
      ‖rotationLp d j ρ (d.G.angleNode z) - forwardAnchor d j ρ z -
        d.r • ∫ t in d.G.rho ρ..(d.G.forward ρ).location m i,
          forwardMeanLp d j ρ (d.G.angleNode z) t‖ ≤
        ‖backwardLp d j (d.G.rho ρ) - initialPosition d‖ +
          d.G.angleNode z * ‖scoreLp d (centerNode j) - initialScore d‖ +
          d.G.seedRot ρ (d.G.angleNode z) *
            ((d.r * Real.sqrt (d.G.variance ρ)) *
              ‖∫ t in 0..conditionalEnd, conditionalMeanLp d j ρ t‖) +
          d.r * |(d.G.forward ρ).location m i - d.G.rho ρ| *
            (meanBudget d + Real.exp 1 * (d.r * d.ell) *
              Real.sqrt (Module.finrank ℝ E)) := by
    linarith
  exact mul_le_mul_of_nonneg_left hsum hcoef

end AcceleratedLogConcave.Numerics.SmoothReferenceDisplacement
