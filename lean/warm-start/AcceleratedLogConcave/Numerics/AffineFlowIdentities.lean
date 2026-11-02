import AcceleratedLogConcave.Numerics.AffineResidual
import AcceleratedLogConcave.Gibbs.PrimitiveMoments
import AcceleratedLogConcave.Conditional.ProbabilityFlow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import AcceleratedLogConcave.Conditional.Transport.KernelRegularity
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import AcceleratedLogConcave.Conditional.Stein.Transport
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import AcceleratedLogConcave.Conditional.Centering.Source

/-!
# Actual flow and kernel identities for affine collocation

This file supplies the deterministic source identities consumed by
`AffineResidual`: the physical primitive-mean dictionary, oriented probability
flow FTC, a smooth transported-Jacobian displacement, and all seven mean
equations for the actual W06/W07 source paths.

The original potential is only C², convex, and has a bounded Hessian. No base
Gibbs normalizability is assumed. The kernel and centering construction use
the source smallness `r^2 * ell ≤ 1/2`. Reversed and singleton probability
intervals, zero kernel terminal time, and all real rotation angles are retained.

Source: `sources/warm-start.tex`, conditional tilt and transport at lines
1370–1511, centering at 1562–1575, and affine graph identities at 2150–2218.
Measurable parameter selection, joint laws, quantitative regularity budgets,
and strong L² calculus are separate obligations.
-/

noncomputable section

/- Implementation component: Normalization. -/

open MeasureTheory Set Function
open scoped ContDiff
open AcceleratedLogConcave
open AcceleratedLogConcave.Numerics.AffineGraph
set_option autoImplicit false

namespace AcceleratedLogConcave.Numerics.AffineFlowIdentities

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private theorem norm_conditionalMean_eq_primitiveMean_of_contDiff
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) (x : E) (r : ℝ)
    {t : ℝ} (htlo : -1 < t) (hthi : t < 1) (y : E) :
    Conditional.conditionalMean F x r t y =
      Gibbs.primitiveMean F (x + (r*t) • y) (r * Real.sqrt (1-t^2)) := by
  have hv : 0 < 1 - t ^ 2 := by
    have hp := mul_pos (by linarith : 0 < 1-t) (by linarith : 0 < 1+t)
    nlinarith
  have hs : Real.sqrt (1-t^2) ≠ 0 := (Real.sqrt_pos.2 hv).ne'
  have hgrad : Continuous (gradient F) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp
      (hF.continuous_fderiv (by norm_num))
  have hobs : Continuous (Conditional.primitiveObservable F x r) :=
    hgrad.comp (continuous_const.add (continuous_const.smul continuous_id))
  have hmap := integral_map_of_stronglyMeasurable
    (μ := Gibbs.primitiveLaw (Conditional.primitivePotential F x r)
      (t • y) (Real.sqrt (1-t^2)))
    (show Measurable (fun z : E => t • y + Real.sqrt (1-t^2) • z) from by fun_prop)
    hobs.stronglyMeasurable
  rw [Gibbs.primitiveLaw_map_affine
    (F := Conditional.primitivePotential F x r)
    ((Gibbs.primitive_contDiff_affine_comp hF x r).continuous.measurable) hs (t • y),
    Real.sq_sqrt hv.le] at hmap
  have ha (z : E) : x + r • (t • y + Real.sqrt (1-t^2) • z) =
      (x + (r*t) • y) + (r * Real.sqrt (1-t^2)) • z := by
    simp only [smul_add, smul_smul, add_assoc]
  simpa only [Conditional.conditionalMean, Conditional.conditionalLaw,
    Conditional.conditionalVariance, Conditional.primitiveObservable,
    Conditional.primitivePotential, Gibbs.primitiveMean, Gibbs.primitiveLaw, ha] using hmap

/-- Physical dictionary for the normalized conditional posterior. The Gaussian
normalization and affine Jacobian cancel through `primitiveLaw_map_affine`. -/
theorem conditionalMean_eq_primitiveMean
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (_hell : 0 ≤ ell)
    (_hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (_hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) {r : ℝ} (_hr : 0 < r) {t : ℝ}
    (htlo : -1 < t) (hthi : t < 1) (y : E) :
    Conditional.conditionalMean F x r t y =
      Gibbs.primitiveMean F (x + (r*t) • y) (r * Real.sqrt (1-t^2)) :=
  norm_conditionalMean_eq_primitiveMean_of_contDiff hF x r htlo hthi y

section ProbabilityFlow
variable {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
  (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
  (x : E) {r : ℝ} (hr : 0 < r) {A B : ℝ} (hAB : A ≤ B)
  (hA : -1 < A) (hB : B < 1)

theorem convexProbabilityFlow_continuous (a : Icc A B) (y : E) :
    Continuous (Conditional.convexProbabilityFlow hF hell hlo hup x hr hAB hA hB a y) :=
  Conditional.probabilityFlow_continuous _ _ _ _ _ _ _ _

/-- Signed FTC for the actual probability flow, including equal and reversed
endpoints. Only derivatives in the interior of the construction slab are used. -/
theorem convexProbabilityFlow_eq_integral_conditionalMean
    (a b : Icc A B) (y : E) :
    let X := Conditional.convexProbabilityFlow hF hell hlo hup x hr hAB hA hB a y
    X b = y - r • ∫ t in (a : ℝ)..(b : ℝ), Conditional.conditionalMean F x r t (X t) := by
  let X := Conditional.convexProbabilityFlow hF hell hlo hup x hr hAB hA hB a y
  change X b = y - r • ∫ t in (a : ℝ)..(b : ℝ), Conditional.conditionalMean F x r t (X t)
  have hX : Continuous X := convexProbabilityFlow_continuous hF hell hlo hup x hr hAB hA hB a y
  have hM : ContinuousOn (fun t => Conditional.conditionalMean F x r t (X t)) (Icc A B) := by
    have hp : Continuous (fun t : ℝ => (t, X t)) := continuous_id.prodMk hX
    change ContinuousOn ((uncurry (Conditional.conditionalMean F x r)) ∘
      (fun t : ℝ => (t, X t))) (Icc A B)
    exact (Conditional.continuousOn_conditionalMean hF (ell := ell) hlo hup x r
      (a := A) (b := B) hA hB).comp hp.continuousOn (fun t ht => ⟨ht, mem_univ _⟩)
  have hsub : uIcc (a : ℝ) (b : ℝ) ⊆ Icc A B := uIcc_subset_Icc a.property b.property
  have hI : IntervalIntegrable (fun t => (-r) • Conditional.conditionalMean F x r t (X t))
      volume (a : ℝ) (b : ℝ) :=
    (continuousOn_const.smul (hM.mono hsub)).intervalIntegrable
  have hFTC : (∫ t in (a : ℝ)..(b : ℝ),
      (-r) • Conditional.conditionalMean F x r t (X t)) = X b - X a := by
    apply intervalIntegral.integral_eq_sub_of_hasDeriv_right hX.continuousOn _ hI
    intro t ht
    have htA : A < t := lt_of_le_of_lt (le_min a.property.1 b.property.1) ht.1
    have htB : t < B := lt_of_lt_of_le ht.2 (max_le a.property.2 b.property.2)
    exact ((Conditional.convexProbabilityFlow_deriv hF hell hlo hup x hr hAB hA hB a y
      ⟨htA.le, htB.le⟩).hasDerivAt (Icc_mem_nhds htA htB)).hasDerivWithinAt
  have hi : X a = y := Conditional.convexProbabilityFlow_initial hF hell hlo hup x hr hAB hA hB a y
  rw [intervalIntegral.integral_smul, hi, neg_smul] at hFTC
  exact (eq_sub_iff_add_eq.mp hFTC).symm.trans (by abel)

/-- Source primitive-mean integral equation for every orientation of time. -/
theorem convexProbabilityFlow_eq_integral_primitiveMean
    (a b : Icc A B) (y : E) :
    let X := Conditional.convexProbabilityFlow hF hell hlo hup x hr hAB hA hB a y
    X b = y - r • ∫ t in (a : ℝ)..(b : ℝ),
      Gibbs.primitiveMean F (x + (r*t) • X t) (r * Real.sqrt (1-t^2)) := by
  have h := convexProbabilityFlow_eq_integral_conditionalMean hF hell hlo hup x hr hAB hA hB a b y
  dsimp only at h ⊢
  rw [h]
  congr 2
  apply intervalIntegral.integral_congr
  intro t ht
  have hmem := (uIcc_subset_Icc a.property b.property) ht
  exact conditionalMean_eq_primitiveMean hF hell hlo hup x hr
    (hA.trans_le hmem.1) (hmem.2.trans_lt hB) _

end ProbabilityFlow

/-- The concrete source probability flow inhabits the accepted sampling
equation, without adding a flow identity or regularity premise. -/
theorem sampling_source_flowEquation
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) {r : ℝ} (hr : 0 < r) {m : ℕ} (S : SamplingGeometry m) (y0 : E) :
    let X := Conditional.convexProbabilityFlow hF hell hlo hup x hr
      S.samplingEnd_pos.le (by norm_num) S.samplingEnd_lt_one
      ⟨0, le_rfl, S.samplingEnd_pos.le⟩ y0
    AffineResidual.Sampling.FlowEquation S (Gibbs.primitiveMean F) x y0 r X := by
  dsimp only [AffineResidual.Sampling.FlowEquation, AffineResidual.Sampling.meanCurve]
  intro a ha
  exact convexProbabilityFlow_eq_integral_primitiveMean hF hell hlo hup x hr
    S.samplingEnd_pos.le (by norm_num) S.samplingEnd_lt_one
    ⟨0, le_rfl, S.samplingEnd_pos.le⟩ ⟨a, ha⟩ y0

end AcceleratedLogConcave.Numerics.AffineFlowIdentities

/- Implementation component: Kernel. -/

open Set MeasureTheory
open scoped Topology ContDiff

namespace AcceleratedLogConcave.Numerics.AffineFlowIdentities
open AcceleratedLogConcave.Conditional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A globally smooth representative of the source's transported-Jacobian
displacement. Its ordinary derivative is nonsingular at zero, and its divided
integral equals the actual transported Stein kernel. -/
theorem exists_sourceKernelCurve {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {ell : ℝ} (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (hsmall : r ^ 2 * ell ≤ 1 / 2) (y g : E) :
    ∃ f : ℝ → E, ContDiff ℝ ∞ f ∧
      (∀ t ∈ Icc 0 b, f t =
        (transportedJacobian hF hell hlo hup x hr hb hb1 t y -
          ContinuousLinearMap.id ℝ E) g) ∧
      deriv f 0 = 0 ∧ f b = 0 ∧
      IntervalIntegrable (fun t => t⁻¹ • deriv f t) volume 0 b ∧
      (∫ t in 0..b, t⁻¹ • deriv f t) =
        r • (transportedSteinKernelTranspose hF hell hlo hup x hr hb hb1 y g) := by
  obtain ⟨C, hCs, hCeq⟩ :=
    Transport.exists_smooth_transportedSteinIntegrand_extension
      hF hell hlo hup x hr hb hb1 hsmall y
  have hy : y ∈ Metric.ball y 1 := Metric.mem_ball_self (by norm_num)
  let J : ℝ → E := fun t => C (t, y) g
  have hJ : ContDiff ℝ ∞ J :=
    (hCs.comp (contDiff_id.prodMk contDiff_const)).clm_apply contDiff_const
  let H : ℝ → E := fun t => t • J t
  have hH : ContDiff ℝ ∞ H := contDiff_id.smul hJ
  let f : ℝ → E := fun t => r • ∫ q in b..t, H q
  have hfd (t : ℝ) : HasDerivAt f (r • H t) t := by
    exact (intervalIntegral.integral_hasDerivAt_right
      (hH.continuous.intervalIntegrable b t)
      hH.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      hH.continuous.continuousAt).const_smul r
  have hder : deriv f = fun t => r • H t := funext fun t => (hfd t).deriv
  have hfs : ContDiff ℝ ∞ f := by
    apply contDiff_infty_iff_deriv.mpr
    refine ⟨fun t => (hfd t).differentiableAt, ?_⟩
    rw [hder]
    exact contDiff_const.smul hH
  have hsource (t : ℝ) (ht : t ∈ Icc 0 b) :
      J t = transportedSteinIntegrand hF hell hlo hup x hr hb hb1 t y g := by
    dsimp [J]
    rw [hCeq t ht y hy]
  have hBcont : ContinuousOn
      (fun t => transportedJacobian hF hell hlo hup x hr hb hb1 t y g) (Icc 0 b) :=
    (continuousOn_transportedJacobian hF hell hlo hup x hr hb hb1 y).clm_apply
      continuousOn_const
  have hagree (t : ℝ) (ht : t ∈ Icc 0 b) : f t =
      (transportedJacobian hF hell hlo hup x hr hb hb1 t y -
        ContinuousLinearMap.id ℝ E) g := by
    have hBder (q : ℝ) (hq : q ∈ Ioo t b) :
        HasDerivAt
          (fun s => transportedJacobian hF hell hlo hup x hr hb hb1 s y g)
          (r • H q) q := by
      have hq0 : 0 < q := ht.1.trans_lt hq.1
      have hqmem : q ∈ Icc 0 b := ⟨hq0.le, hq.2.le⟩
      have hd := (transportedJacobian_deriv hF hell hlo hup x hr hb hb1 hqmem y).hasDerivAt
        (Icc_mem_nhds hq0 hq.2)
      have hdg := hd.clm_apply (hasDerivAt_const q g)
      simpa only [H, hsource q hqmem, transportedSteinIntegrand,
        smul_apply, map_zero, add_zero,
        smul_smul] using hdg
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.2
      (hBcont.mono (Icc_subset_Icc ht.1 le_rfl)) hBder
      ((continuous_const.smul hH.continuous).intervalIntegrable t b)
    dsimp [f]
    rw [← intervalIntegral.integral_smul, intervalIntegral.integral_symm, hftc]
    simp only [transportedJacobian_terminal, ContinuousLinearMap.id_apply,
      sub_apply, neg_sub]
  have hcancel (t : ℝ) (ht : t ∈ uIoo 0 b) :
      t⁻¹ • deriv f t =
        r • (transportedSteinIntegrand hF hell hlo hup x hr hb hb1 t y g) := by
    have ht' : t ∈ Ioo 0 b := by simpa only [uIoo_of_le hb] using ht
    rw [hder]
    simp only [H, smul_smul, hsource t ⟨ht'.1.le, ht'.2.le⟩]
    congr 1
    field_simp [ht'.1.ne']
  have hi : IntervalIntegrable
      (fun t => r • (transportedSteinIntegrand hF hell hlo hup x hr hb hb1 t y g))
      volume 0 b :=
    (continuousOn_const.smul
      ((continuousOn_transportedSteinIntegrand hF hell hlo hup x hr hb hb1 y).clm_apply
        continuousOn_const)).intervalIntegrable_of_Icc hb
  refine ⟨f, hfs, hagree, ?_, ?_, hi.congr_uIoo (fun t ht => (hcancel t ht).symm), ?_⟩
  · rw [hder]
    simp [H]
  · simp [f]
  · calc
      (∫ t in 0..b, t⁻¹ • deriv f t) =
          ∫ t in 0..b,
            r • (transportedSteinIntegrand hF hell hlo hup x hr hb hb1 t y g) :=
        intervalIntegral.integral_congr_uIoo hcancel
      _ = r • (transportedSteinKernelTranspose hF hell hlo hup x hr hb hb1 y g) := by
        rw [intervalIntegral.integral_smul]
        congr 1
        exact (ContinuousLinearMap.intervalIntegral_apply
          (intervalIntegrable_transportedSteinIntegrand hF hell hlo hup x hr hb hb1 y) g).symm

end AcceleratedLogConcave.Numerics.AffineFlowIdentities

/- Implementation component: Angle. -/

/-!
The rotation tangent and actual probability-flow displacement identity.
The angle parameter is an unrestricted real number, so the derivative at zero
uses an ordinary two-sided derivative. No regularity of a chosen representative
or abstract flow identity is assumed.
-/

open Set

namespace AcceleratedLogConcave.Numerics.AffineFlowIdentities

section Rotation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The rotation appearing in the affine mean construction. -/
def sourceRotation (B mid g : E) (q z : ℝ) : E :=
  mid + Real.cos (z / q) • (B-mid) + (q * Real.sin (z / q)) • g

@[simp] theorem sourceRotation_zero (B mid g : E) (q : ℝ) :
    sourceRotation B mid g q 0 = B := by
  simp [sourceRotation]

/-- The scale cancels in the tangent, with no restriction on the sign of angles. -/
theorem hasDerivAt_sourceRotation (B mid g : E) {q : ℝ} (hq : q ≠ 0) :
    HasDerivAt (sourceRotation B mid g q) g 0 := by
  change HasDerivAt (fun z => mid + Real.cos (z / q) • (B-mid) +
    (q * Real.sin (z / q)) • g) g 0
  have hdiv := (hasDerivAt_id (0 : ℝ)).div_const q
  have hcos := hdiv.cos.smul_const (B-mid)
  have hsin := (hdiv.sin.const_mul q).smul_const g
  convert ((hcos.const_add mid).add hsin) using 1
  · funext z
    rfl
  · simp [hq]

/-- Chain rule for the displacement of a rotation under a differentiable map. -/
theorem hasDerivAt_displacement_sourceRotation {T : E → E} {B : E}
    (hT : DifferentiableAt ℝ T B) (mid g : E) {q : ℝ} (hq : q ≠ 0) :
    HasDerivAt (fun z => T (sourceRotation B mid g q z) -
      sourceRotation B mid g q z)
      ((fderiv ℝ T B - ContinuousLinearMap.id ℝ E) g) 0 := by
  have hrot := hasDerivAt_sourceRotation B mid g hq
  have hT' : HasFDerivAt T (fderiv ℝ T B) (sourceRotation B mid g q 0) := by
    simpa only [sourceRotation_zero] using hT.hasFDerivAt
  have hcomp := hT'.comp_hasDerivAt (0 : ℝ) hrot
  convert hcomp.sub hrot using 1
  · funext z
    rfl
  · rfl

end Rotation

section ActualTransport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
  (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
  (x : E) {r : ℝ} (hr : 0 < r) {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)

/-- The actual flow displacement has tangent `(Bρ-I)g` under source rotation.
Both transport times may be zero, and either may equal the terminal time. -/
theorem hasDerivAt_forward_displacement_rotation {ρ : ℝ} (hρ : ρ ∈ Icc 0 β)
    (y mid g : E) {q : ℝ} (hq : q ≠ 0) :
    let B := Conditional.convexProbabilityFlow hF hell hlo hup x hr hβ
      (by norm_num) hβ1 ⟨β, hβ, le_rfl⟩ y ρ
    HasDerivAt
      (fun z => Conditional.convexProbabilityFlow hF hell hlo hup x hr hβ
        (by norm_num) hβ1 ⟨ρ, hρ⟩ (sourceRotation B mid g q z) β -
          sourceRotation B mid g q z)
      ((Conditional.transportedJacobian hF hell hlo hup x hr hβ hβ1 ρ y -
        ContinuousLinearMap.id ℝ E) g) 0 := by
  let T : E → E := Conditional.forwardProbabilityTransport hF hell hlo hup x hr hβ hβ1 ρ
  let B : E := Conditional.backwardProbabilityTransport hF hell hlo hup x hr hβ hβ1 ρ y
  have hT : DifferentiableAt ℝ T B :=
    ((Conditional.contDiff_one_forwardProbabilityTransport hF hell hlo hup x hr hβ hβ1 ρ).differentiable
      (by norm_num)).differentiableAt
  have h := hasDerivAt_displacement_sourceRotation hT mid g hq
  have hB : B = Conditional.convexProbabilityFlow hF hell hlo hup x hr hβ
      (by norm_num) hβ1 ⟨β, hβ, le_rfl⟩ y ρ := by
    dsimp [B]
    rw [Conditional.backwardProbabilityTransport_eq_flow, projIcc_of_mem hβ hρ]
  have hTeq (w : E) : T w = Conditional.convexProbabilityFlow hF hell hlo hup x hr hβ
      (by norm_num) hβ1 ⟨ρ, hρ⟩ w β := by
    dsimp [T, Conditional.forwardProbabilityTransport]
    rw [projIcc_of_mem hβ hρ]
    rfl
  change HasDerivAt _ _ 0
  simpa only [T, B, Conditional.transportedJacobian, hB, hTeq] using h

end ActualTransport

end AcceleratedLogConcave.Numerics.AffineFlowIdentities

/- Implementation component: Mean. -/

open MeasureTheory Set
open scoped ContDiff
open AcceleratedLogConcave
open AcceleratedLogConcave.Numerics
open AcceleratedLogConcave.Numerics.AffineGraph
open AcceleratedLogConcave.Numerics.AffineGraph.MeanGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace AcceleratedLogConcave.Numerics.AffineFlowIdentities

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section Mean
variable {F : EuclideanSpace ℝ ι → ℝ} (hF : ContDiff ℝ 2 F)
  {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
  (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
  (x : EuclideanSpace ℝ ι) {r : ℝ} (hr : 0 < r) (hsmall : r^2*ell ≤ 1/2)
  {m : ℕ} (G : MeanGeometry m) {σ : ℝ} (hσ : 0 < σ)
  (y0 g0 : EuclideanSpace ℝ ι) (ζ : Fin m → G.Kernel → EuclideanSpace ℝ ι)

/-- The actual source centering trajectory with the prescribed initial pair. -/
abbrev sourcePhase : ℝ → Conditional.Centering.Phase (EuclideanSpace ℝ ι) :=
  Conditional.Centering.sourceCenteringFlow hF hell hlo hup x hr
    G.backwardEnd_pos.le G.backwardEnd_lt_one hsmall (half_pos hσ)
    (WithLp.toLp 2 (y0,g0))

/-- Agreement with the constructed source objects is an output of the mean
curve construction, including one shared smooth kernel per centering node. -/
structure SourceMeanAgreement (C : AffineResidual.Mean.Curves G (EuclideanSpace ℝ ι)) : Prop where
  position : ∀ t : ℝ,
    C.position t = (sourcePhase hF hell hlo hup x hr hsmall G hσ y0 g0 t).fst
  score : ∀ t : ℝ,
    C.score t = (sourcePhase hF hell hlo hup x hr hsmall G hσ y0 g0 t).snd
  velocity : ∀ t : ℝ,
    C.velocity t = -(σ/2)⁻¹ •
      (Conditional.transportedSteinKernelTranspose hF hell hlo hup x hr
        G.backwardEnd_pos.le G.backwardEnd_lt_one
        (sourcePhase hF hell hlo hup x hr hsmall G hσ y0 g0 t).fst
        (sourcePhase hF hell hlo hup x hr hsmall G hσ y0 g0 t).snd)
  backward : ∀ (j : Fin m) (a : ℝ), a ∈ Icc (0 : ℝ) (backwardEnd G.R) →
    C.backward j a = Conditional.convexProbabilityFlow hF hell hlo hup x hr
      G.backwardEnd_pos.le (by norm_num) G.backwardEnd_lt_one
      ⟨backwardEnd G.R, G.backwardEnd_pos.le, le_rfl⟩
      (C.position (centerNode j)) a
  conditional : ∀ (j : Fin m) (k : G.Kernel) (η : ℝ),
    η ∈ Icc (0 : ℝ) conditionalEnd →
    C.conditional j k η = Conditional.convexProbabilityFlow hF hell hlo hup
      (x + (r * G.rho k) • C.backward j (G.rho k))
      (mul_pos hr (Real.sqrt_pos.2 (G.variance_pos k)))
      (G.conditional k).lo_lt_hi.le (by norm_num) conditionalEnd_lt_one
      ⟨0, le_rfl, (G.conditional k).lo_lt_hi.le⟩ (ζ j k) η
  forward : ∀ (j : Fin m) (k : G.Kernel) (z a : ℝ),
    a ∈ Icc (G.rho k) (backwardEnd G.R) →
    C.forward j k z a = Conditional.convexProbabilityFlow hF hell hlo hup x hr
      G.backwardEnd_pos.le (by norm_num) G.backwardEnd_lt_one
      ⟨G.rho k, (G.rho_mem k).1, (G.rho_mem k).2.le⟩
      (C.rotation G j k z) a
  kernel_smooth : ∀ j : Fin m, ContDiff ℝ ∞ (C.kernel j)
  kernel_zero_deriv : ∀ j : Fin m, deriv (C.kernel j) 0 = 0
  kernel_terminal : ∀ j : Fin m, C.kernel j (backwardEnd G.R) = 0
  kernel : ∀ (j : Fin m) (t : ℝ), t ∈ Icc (0 : ℝ) (backwardEnd G.R) →
    C.kernel j t =
      (Conditional.transportedJacobian hF hell hlo hup x hr
        G.backwardEnd_pos.le G.backwardEnd_lt_one t (C.position (centerNode j)) -
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι)) (C.score (centerNode j))

private theorem mean_sqrt_backward_variance :
    Real.sqrt (1 - (backwardEnd G.R)^2) = G.R := by
  have hR : 0 ≤ 1-G.R^2 := by nlinarith [G.R_pos, G.R_le_half]
  rw [backwardEnd, Real.sq_sqrt hR]
  rw [show 1 - (1-G.R^2) = G.R^2 by ring]
  exact Real.sqrt_sq G.R_pos.le

omit [DecidableEq ι] in
private theorem mean_source_position_integral (a : ℝ) :
    (sourcePhase hF hell hlo hup x hr hsmall G hσ y0 g0 a).fst = y0 +
      ∫ t in 0..a, -(σ/2)⁻¹ •
        Conditional.transportedSteinKernelTranspose hF hell hlo hup x hr
          G.backwardEnd_pos.le G.backwardEnd_lt_one
          (sourcePhase hF hell hlo hup x hr hsmall G hσ y0 g0 t).fst
          (sourcePhase hF hell hlo hup x hr hsmall G hσ y0 g0 t).snd := by
  let P := sourcePhase hF hell hlo hup x hr hsmall G hσ y0 g0
  let K := Conditional.transportedSteinKernelTranspose hF hell hlo hup x hr
    G.backwardEnd_pos.le G.backwardEnd_lt_one
  have hdP (t : ℝ) := Conditional.Centering.sourceCenteringFlow_deriv
    hF hell hlo hup x hr G.backwardEnd_pos.le G.backwardEnd_lt_one hsmall
      (half_pos hσ) (WithLp.toLp 2 (y0,g0)) t
  have hcP : Continuous P := continuous_iff_continuousAt.mpr fun t => (hdP t).continuousAt
  have hcPair := (WithLp.prod_continuous_ofLp 2 (EuclideanSpace ℝ ι)
    (EuclideanSpace ℝ ι)).comp hcP
  have hcK : Continuous K :=
    (Conditional.Centering.sourceKernel_contDiff_one hF hell hlo hup x hr
      G.backwardEnd_pos.le G.backwardEnd_lt_one hsmall).continuous
  have hcV : Continuous (fun t => -(σ/2)⁻¹ • K (P t).fst (P t).snd) :=
    ((hcK.comp hcPair.fst).clm_apply hcPair.snd).const_smul (-(σ/2)⁻¹)
  have hd (t : ℝ) : HasDerivAt (fun t => (P t).fst)
      (-(σ/2)⁻¹ • K (P t).fst (P t).snd) t := by
    convert! (WithLp.fstL 2 ℝ (EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι)).hasFDerivAt.comp_hasDerivAt
        t (hdP t) using 1
    simp [P, K, sourcePhase, Conditional.Centering.velocity, WithLp.fstL, neg_smul]
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t) (hcV.intervalIntegrable 0 a)
  have hzero : (P 0).fst = y0 := by
    change (Conditional.Centering.sourceCenteringFlow _ _ _ _ _ _ _ _ _ _ _ 0).fst = _
    rw [Conditional.Centering.sourceCenteringFlow_initial]
    rfl
  change (P a).fst = y0 + _
  rw [hi, hzero]
  abel

omit [DecidableEq ι] in
private theorem mean_source_score_integral (a : ℝ) :
    (sourcePhase hF hell hlo hup x hr hsmall G hσ y0 g0 a).snd = g0 +
      (σ/2)⁻¹ • ∫ t in 0..a,
        (Conditional.conditionalMean F x r (backwardEnd G.R)
          (sourcePhase hF hell hlo hup x hr hsmall G hσ y0 g0 t).fst -
            Conditional.conditionalMean F x r 0 0) := by
  let P := sourcePhase hF hell hlo hup x hr hsmall G hσ y0 g0
  let M := Conditional.conditionalMean F x r (backwardEnd G.R)
  let u := Conditional.conditionalMean F x r 0 0
  have hdP (t : ℝ) := Conditional.Centering.sourceCenteringFlow_deriv
    hF hell hlo hup x hr G.backwardEnd_pos.le G.backwardEnd_lt_one hsmall
      (half_pos hσ) (WithLp.toLp 2 (y0,g0)) t
  have hcP : Continuous P := continuous_iff_continuousAt.mpr fun t => (hdP t).continuousAt
  have hcPair := (WithLp.prod_continuous_ofLp 2 (EuclideanSpace ℝ ι)
    (EuclideanSpace ℝ ι)).comp hcP
  have hcM : Continuous M :=
    (Conditional.contDiff_one_conditionalMean hF hlo hup x r
      (by linarith [G.backwardEnd_pos]) G.backwardEnd_lt_one).continuous
  have hcV : Continuous (fun t => (σ/2)⁻¹ • (M (P t).fst - u)) :=
    ((hcM.comp hcPair.fst).sub (continuous_const (y := u))).const_smul ((σ/2)⁻¹)
  have hd (t : ℝ) : HasDerivAt (fun t => (P t).snd)
      ((σ/2)⁻¹ • (M (P t).fst - u)) t := by
    convert! (WithLp.sndL 2 ℝ (EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι)).hasFDerivAt.comp_hasDerivAt
        t (hdP t) using 1
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t) (hcV.intervalIntegrable 0 a)
  rw [intervalIntegral.integral_smul] at hi
  have hzero : (P 0).snd = g0 := by
    change (Conditional.Centering.sourceCenteringFlow _ _ _ _ _ _ _ _ _ _ _ 0).snd = _
    rw [Conditional.Centering.sourceCenteringFlow_initial]
    rfl
  change (P a).snd = g0 + _
  rw [hi, hzero]
  abel

omit [DecidableEq ι] in
/-- The actual centering flow and actual probability transports supply all
seven deterministic mean equations, with source agreement as a conclusion.
No law, measurability, or quantitative derivative budget is asserted here. -/
theorem exists_sourceMeanCurves_equations :
    ∃ C : AffineResidual.Mean.Curves G (EuclideanSpace ℝ ι),
      SourceMeanAgreement hF hell hlo hup x hr hsmall G hσ y0 g0 ζ C ∧
      AffineResidual.Mean.Equations G C (Gibbs.primitiveMean F) r σ x y0 g0 ζ := by
  classical
  let P := sourcePhase hF hell hlo hup x hr hsmall G hσ y0 g0
  let K := Conditional.transportedSteinKernelTranspose hF hell hlo hup x hr
    G.backwardEnd_pos.le G.backwardEnd_lt_one
  choose f hfcont hfagree hfzero hfterm hfi hfid using
    (fun j : Fin m => exists_sourceKernelCurve hF hell hlo hup x hr
      G.backwardEnd_pos.le G.backwardEnd_lt_one hsmall
      (P (centerNode j)).fst (P (centerNode j)).snd)
  let B (j : Fin m) : ℝ → EuclideanSpace ℝ ι :=
    Conditional.convexProbabilityFlow hF hell hlo hup x hr G.backwardEnd_pos.le
      (by norm_num) G.backwardEnd_lt_one
      ⟨backwardEnd G.R, G.backwardEnd_pos.le, le_rfl⟩ (P (centerNode j)).fst
  let D (j : Fin m) (k : G.Kernel) : ℝ → EuclideanSpace ℝ ι :=
    Conditional.convexProbabilityFlow hF hell hlo hup
      (x + (r * G.rho k) • B j (G.rho k))
      (mul_pos hr (Real.sqrt_pos.2 (G.variance_pos k)))
      (G.conditional k).lo_lt_hi.le (by norm_num) conditionalEnd_lt_one
      ⟨0, le_rfl, (G.conditional k).lo_lt_hi.le⟩ (ζ j k)
  let C₀ : AffineResidual.Mean.Curves G (EuclideanSpace ℝ ι) := {
    position := fun t => (P t).fst
    score := fun t => (P t).snd
    velocity := fun t => -(σ/2)⁻¹ • K (P t).fst (P t).snd
    backward := B
    conditional := D
    forward := fun _ _ _ _ => 0
    kernel := f }
  let C : AffineResidual.Mean.Curves G (EuclideanSpace ℝ ι) := { C₀ with
    forward := fun j k z => Conditional.convexProbabilityFlow hF hell hlo hup x hr
      G.backwardEnd_pos.le (by norm_num) G.backwardEnd_lt_one
      ⟨G.rho k, (G.rho_mem k).1, (G.rho_mem k).2.le⟩ (C₀.rotation G j k z) }
  have hag : SourceMeanAgreement hF hell hlo hup x hr hsmall G hσ y0 g0 ζ C := {
    position := fun _ => rfl
    score := fun _ => rfl
    velocity := fun _ => rfl
    backward := fun _ _ _ => rfl
    conditional := fun _ _ _ _ => rfl
    forward := fun _ _ _ _ _ => rfl
    kernel_smooth := hfcont
    kernel_zero_deriv := hfzero
    kernel_terminal := hfterm
    kernel := hfagree }
  have hback (j : Fin m) (a : ℝ) (ha : a ∈ Icc 0 (backwardEnd G.R)) :
      C.backward j a = C.position (centerNode j) - r • ∫ t in backwardEnd G.R..a,
        C.backwardMean G (Gibbs.primitiveMean F) x r j t := by
    exact convexProbabilityFlow_eq_integral_primitiveMean hF hell hlo hup x hr
      G.backwardEnd_pos.le (by norm_num) G.backwardEnd_lt_one
      ⟨backwardEnd G.R, G.backwardEnd_pos.le, le_rfl⟩ ⟨a, ha⟩ (P (centerNode j)).fst
  have hcond (j : Fin m) (k : G.Kernel) (η : ℝ) (hη : η ∈ Icc 0 conditionalEnd) :
      C.conditional j k η = ζ j k - (r * Real.sqrt (G.variance k)) •
        ∫ t in 0..η, C.conditionalMean G (Gibbs.primitiveMean F) x r j k t := by
    exact convexProbabilityFlow_eq_integral_primitiveMean hF hell hlo hup
      (x + (r * G.rho k) • B j (G.rho k))
      (mul_pos hr (Real.sqrt_pos.2 (G.variance_pos k)))
      (G.conditional k).lo_lt_hi.le (by norm_num) conditionalEnd_lt_one
      ⟨0, le_rfl, (G.conditional k).lo_lt_hi.le⟩ ⟨η, hη⟩ (ζ j k)
  have hforw (j : Fin m) (k : G.Kernel) (z a : ℝ)
      (ha : a ∈ Icc (G.rho k) (backwardEnd G.R)) :
      C.forward j k z a = C.rotation G j k z - r • ∫ t in G.rho k..a,
        C.forwardMean G (Gibbs.primitiveMean F) x r j k z t := by
    exact convexProbabilityFlow_eq_integral_primitiveMean hF hell hlo hup x hr
      G.backwardEnd_pos.le (by norm_num) G.backwardEnd_lt_one
      ⟨G.rho k, (G.rho_mem k).1, (G.rho_mem k).2.le⟩
      ⟨a, (G.rho_mem k).1.trans ha.1, ha.2⟩ (C₀.rotation G j k z)
  have hbase : Conditional.conditionalMean F x r 0 0 = Gibbs.primitiveMean F x r := by
    simpa using conditionalMean_eq_primitiveMean hF hell hlo hup x hr
      (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1) 0
  have hcenter (t : ℝ) :
      Conditional.conditionalMean F x r (backwardEnd G.R) (P t).fst =
        C.centerMean G (Gibbs.primitiveMean F) x r t := by
    rw [conditionalMean_eq_primitiveMean hF hell hlo hup x hr
      (by linarith [G.backwardEnd_pos]) G.backwardEnd_lt_one, mean_sqrt_backward_variance G]
    rfl
  refine ⟨C, hag, ?_⟩
  refine {
    position := ?_
    score := ?_
    backward := hback
    conditional := hcond
    forward := fun j k z a _ ha => hforw j k z a ha
    kernel_angle := ?_
    velocity_kernel := ?_ }
  · intro a _
    exact mean_source_position_integral hF hell hlo hup x hr hsmall G hσ y0 g0 a
  · intro a _
    have h := mean_source_score_integral hF hell hlo hup x hr hsmall G hσ y0 g0 a
    change C.score a = g0 + (σ/2)⁻¹ • ∫ t in 0..a,
      (Conditional.conditionalMean F x r (backwardEnd G.R) (P t).fst -
        Conditional.conditionalMean F x r 0 0) at h
    simpa only [hcenter, hbase] using h
  · intro j k
    have hact (z : ℝ) : C.forwardAction G (Gibbs.primitiveMean F) x r j k z =
        C.forward j k z (backwardEnd G.R) - C.rotation G j k z := by
      rw [hforw j k z (backwardEnd G.R) ⟨(G.rho_mem k).2.le, le_rfl⟩]
      unfold AffineResidual.Mean.Curves.forwardAction
      rw [neg_smul]
      abel
    let mid := (G.rho k / (1 + (G.rho k)^2)) •
      (G.rho k • B j (G.rho k) + (Real.sqrt (G.variance k) / conditionalEnd) •
        D j k conditionalEnd + G.rho k • B j (G.rho k))
    have hd := hasDerivAt_forward_displacement_rotation hF hell hlo hup x hr
      G.backwardEnd_pos.le G.backwardEnd_lt_one
      ⟨(G.rho_mem k).1, (G.rho_mem k).2.le⟩
      (P (centerNode j)).fst mid (P (centerNode j)).snd (G.rotationScale_pos k).ne'
    have hdC : HasDerivAt (fun z => C.forward j k z (backwardEnd G.R) - C.rotation G j k z)
        ((Conditional.transportedJacobian hF hell hlo hup x hr
          G.backwardEnd_pos.le G.backwardEnd_lt_one (G.rho k) (P (centerNode j)).fst -
            ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι)) (P (centerNode j)).snd) 0 := by
      exact hd
    rw [hag.kernel j (G.rho k) ⟨(G.rho_mem k).1, (G.rho_mem k).2.le⟩]
    rw [show C.forwardAction G (Gibbs.primitiveMean F) x r j k =
      (fun z => C.forward j k z (backwardEnd G.R) - C.rotation G j k z) from funext hact]
    exact hdC.deriv.symm
  · intro j
    change -(σ/2)⁻¹ • K (P (centerNode j)).fst (P (centerNode j)).snd =
      -(r*(σ/2))⁻¹ • ∫ t in 0..backwardEnd G.R, t⁻¹ • deriv (f j) t
    rw [hfid j, smul_smul]
    congr 1
    field_simp

end Mean
end AcceleratedLogConcave.Numerics.AffineFlowIdentities
