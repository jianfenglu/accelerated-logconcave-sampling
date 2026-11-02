import AcceleratedLogConcave.Numerics.SmoothInitialDisplacementBound
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Uniformizing the exact common-seed initializer row inventory. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory AcceleratedLogConcave
open Numerics Numerics.MeanFlowLp Numerics.MeanResidualBridge Numerics.MeanCollocationLp
open Numerics.AffineGraph Numerics.AffineGraph.MeanGeometry
open Numerics.SmoothInitialDisplacementBound Numerics.SmoothConditionalMeanBudget
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace AcceleratedLogConcave.Numerics.SmoothInitialUniformBound
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

/-- The manuscript's source-gradient size, with no graph cardinality. -/
def sourceSize (d : Data ι m) : ℝ :=
  Real.sqrt (Module.finrank ℝ E) + ‖gradient d.F d.x‖

private theorem sourceSize_nonneg (d : Data ι m) : 0 ≤ sourceSize d := by
  unfold sourceSize
  positivity

/-- The mean transport budget enters the physical rows only after multiplication
by the physical radius. This removes the apparent inverse-radius dependence. -/
theorem radius_meanBudget_le (d : Data ι m) (hrone : d.r ≤ 1) :
    d.r * meanBudget d ≤ 2 * sourceSize d := by
  let s := Real.sqrt (Module.finrank ℝ E)
  let g := ‖gradient d.F d.x‖
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hg : 0 ≤ g := norm_nonneg _
  have hr : 0 ≤ d.r := d.hr.le
  have hp : 0 ≤ d.ell * d.r ^ 2 := by positivity [d.hell]
  have hp1 : d.ell * d.r ^ 2 ≤ 1 / 2 := by
    nlinarith [d.hsmall]
  have hrg : d.r * g ≤ g := mul_le_of_le_one_left hg hrone
  have hrp : d.r * (d.ell * d.r ^ 2) ≤ d.ell * d.r ^ 2 :=
    mul_le_of_le_one_left hp hrone
  have hps : (d.ell * d.r ^ 2) * s ≤ (1 / 2) * s :=
    mul_le_mul_of_nonneg_right hp1 hs
  have hpg : (d.ell * d.r ^ 2) * g ≤ (1 / 2) * g :=
    mul_le_mul_of_nonneg_right hp1 hg
  have hrpg := mul_le_mul_of_nonneg_right hrp hg
  dsimp [sourceSize, meanBudget, radiusBudget]
  nlinarith

/-- The common radius-paid transport expression includes the centered
Gaussian fluctuation, and is bounded by the original gradient size. -/
theorem radius_transportBudget_le (d : Data ι m) (hrone : d.r ≤ 1) :
    d.r * (meanBudget d + Real.exp 1 * (d.r * d.ell) *
      Real.sqrt (Module.finrank ℝ E)) ≤ 4 * sourceSize d := by
  have hm := radius_meanBudget_le d hrone
  have hs : 0 ≤ Real.sqrt (Module.finrank ℝ E) := Real.sqrt_nonneg _
  have hp : d.ell * d.r ^ 2 ≤ 1 / 2 := by nlinarith [d.hsmall]
  have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  have hp0 : 0 ≤ d.ell * d.r ^ 2 := by positivity [d.hell]
  have hs' : Real.exp 1 * (d.ell * d.r ^ 2) *
      Real.sqrt (Module.finrank ℝ E) ≤ 3 * (1 / 2) *
      Real.sqrt (Module.finrank ℝ E) := by
    gcongr
  have hsource : Real.sqrt (Module.finrank ℝ E) ≤ sourceSize d := by
    unfold sourceSize
    exact le_add_of_nonneg_right (norm_nonneg _)
  nlinarith [mul_nonneg d.hr.le (show 0 ≤ meanBudget d by
    unfold meanBudget radiusBudget
    positivity [d.hell, d.hr.le])]

/-- The centering displacement has a numerical bound independent of the
center quadrature order. -/
theorem centerMove_le (d : Data ι m) (hscale : d.ell * d.r / d.sigma ≤ 1)
    (j : Fin m) : centerMove d j ≤ 6 * sourceSize d := by
  have hj : |centerNode j| ≤ 1 := by
    rw [abs_of_pos (centerNode_mem j).1]
    exact (centerNode_mem j).2.le
  have hj0 : 0 ≤ |centerNode j| := abs_nonneg _
  have hs : 0 ≤ Real.sqrt (Module.finrank ℝ E) := Real.sqrt_nonneg _
  have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  have he0 : 0 ≤ Real.exp 1 := (Real.exp_pos _).le
  have hscale0 : 0 ≤ d.ell * d.r / d.sigma := by
    positivity [d.hell, d.hr.le, d.hsigma.le]
  have hb : 0 ≤ backwardEnd d.G.R := d.G.backwardEnd_pos.le
  have hb1 : backwardEnd d.G.R ≤ 1 := d.G.backwardEnd_lt_one.le
  have heq : centerMove d j = |centerNode j| *
      (2 * Real.exp 1 * (d.ell * d.r / d.sigma) *
        backwardEnd d.G.R * Real.sqrt (Module.finrank ℝ E)) := by
    unfold centerMove CenteringFlowLp.alpha
    dsimp [kernelData]
    field_simp [d.hsigma.ne']
  rw [heq]
  calc
    _ ≤ 1 * (2 * 3 * 1 * 1 * Real.sqrt (Module.finrank ℝ E)) := by
      gcongr
    _ ≤ 6 * sourceSize d := by
      unfold sourceSize
      nlinarith [norm_nonneg (gradient d.F d.x)]

/-- Score movement uses the same physical scale, without a mesh factor. -/
theorem scoreMove_le (d : Data ι m) (hscale : d.ell * d.r / d.sigma ≤ 1)
    (j : Fin m) : scoreMove d j ≤ 6 * sourceSize d := by
  have hj : |centerNode j| ≤ 1 := by
    rw [abs_of_pos (centerNode_mem j).1]
    exact (centerNode_mem j).2.le
  have hs : 0 ≤ Real.sqrt (Module.finrank ℝ E) := Real.sqrt_nonneg _
  have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  have hscale0 : 0 ≤ d.ell * d.r / d.sigma := by
    positivity [d.hell, d.hr.le, d.hsigma.le]
  have heq : scoreMove d j = |centerNode j| *
      (2 * Real.exp 1 * (d.ell * d.r / d.sigma) *
        Real.sqrt (Module.finrank ℝ E)) := by
    unfold scoreMove CenteringFlowLp.alpha
    dsimp [kernelData]
    field_simp [d.hsigma.ne']
  rw [heq]
  calc
    _ ≤ 1 * (2 * 3 * 1 * Real.sqrt (Module.finrank ℝ E)) := by
      gcongr
    _ ≤ 6 * sourceSize d := by
      unfold sourceSize
      nlinarith [norm_nonneg (gradient d.F d.x)]

theorem seedBudget_le (d : Data ι m) (hrone : d.r ≤ 1) :
    seedBudget d ≤ 2 * sourceSize d := by
  have hg : 0 ≤ ‖gradient d.F d.x‖ := norm_nonneg _
  have hrg := mul_le_of_le_one_left hg hrone
  unfold seedBudget sourceSize
  nlinarith [Real.sqrt_nonneg (Module.finrank ℝ E)]

theorem backwardMove_le (d : Data ι m) (hrone : d.r ≤ 1)
    (hscale : d.ell * d.r / d.sigma ≤ 1) (j : Fin m) (a : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) :
    backwardMove d j a ≤ 10 * sourceSize d := by
  have hb0 : 0 ≤ backwardEnd d.G.R := d.G.backwardEnd_pos.le
  have hb1 : backwardEnd d.G.R ≤ 1 := d.G.backwardEnd_lt_one.le
  have hdist : |a - backwardEnd d.G.R| ≤ 1 :=
    abs_le.mpr ⟨by linarith [ha.1], by linarith [ha.2]⟩
  have hmove := centerMove_le d hscale j
  have htransport := radius_transportBudget_le d hrone
  have htransport0 : 0 ≤ d.r * (meanBudget d + Real.exp 1 *
      (d.r * d.ell) * Real.sqrt (Module.finrank ℝ E)) := by
    have hmean : 0 ≤ meanBudget d := by
      unfold meanBudget radiusBudget
      positivity [d.hell, d.hr.le]
    positivity [d.hr.le, d.hell]
  have hscaled := mul_le_of_le_one_left htransport0 hdist
  unfold backwardMove
  nlinarith

theorem conditional_radius_le (d : Data ι m) (ρ : d.G.Kernel) :
    (conditionalData d ρ).r ≤ d.r := by
  have hv : d.G.variance ρ ≤ 1 := by
    unfold MeanGeometry.variance
    nlinarith [sq_nonneg (d.G.rho ρ)]
  change d.r * Real.sqrt (d.G.variance ρ) ≤ d.r
  exact mul_le_of_le_one_right d.hr.le (Real.sqrt_le_one.mpr hv)

theorem conditional_amplification_le_three (d : Data ι m)
    (ρ : d.G.Kernel) :
    SamplingCenterLp.amplification (conditionalData d ρ) ≤ 3 := by
  let q := (conditionalData d ρ).r
  have hq : 0 ≤ q := (conditionalData d ρ).hr.le
  have hqr : q ≤ d.r := conditional_radius_le d ρ
  have hsq : q ^ 2 ≤ d.r ^ 2 := pow_le_pow_left₀ hq hqr 2
  have hmul : q ^ 2 * d.ell ≤ d.r ^ 2 * d.ell :=
    mul_le_mul_of_nonneg_right hsq d.hell
  have hp : d.r ^ 2 * d.ell ≤ 1 / 2 := by nlinarith [d.hsmall]
  have hb0 : 0 ≤ conditionalEnd := conditionalEnd_pos.le
  have hb1 : conditionalEnd ≤ 1 := conditionalEnd_lt_one.le
  have hinner : q ^ 2 * d.ell * conditionalEnd ≤ 1 := by
    have h0 : 0 ≤ q ^ 2 * d.ell := by positivity [d.hell]
    nlinarith [mul_le_of_le_one_left h0 hb1]
  unfold SamplingCenterLp.amplification
  exact (Real.exp_le_exp.mpr hinner).trans Real.exp_one_lt_three.le

/-- The center-sensitivity coefficient is bounded only after its two physical
radius factors are included. -/
theorem conditional_sensitivity_paid_le (d : Data ι m)
    (ρ : d.G.Kernel) :
    d.r ^ 2 * (3 * d.ell +
      (conditionalData d ρ).r * conditionalEnd * d.ell *
        SamplingCenterLp.amplification (conditionalData d ρ) *
        ((conditionalData d ρ).r * d.ell * conditionalEnd)) ≤ 3 := by
  let q := (conditionalData d ρ).r
  let A := SamplingCenterLp.amplification (conditionalData d ρ)
  let p := d.ell * d.r ^ 2
  let v := d.ell * q ^ 2
  have hp0 : 0 ≤ p := by dsimp [p]; positivity [d.hell]
  have hp : p ≤ 1 / 2 := by dsimp [p]; nlinarith [d.hsmall]
  have hq : 0 ≤ q := (conditionalData d ρ).hr.le
  have hqr : q ≤ d.r := conditional_radius_le d ρ
  have hv0 : 0 ≤ v := by dsimp [v]; positivity [d.hell]
  have hv : v ≤ 1 / 2 := by
    dsimp [v]
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq hqr 2) d.hell).trans
      (by dsimp [p] at hp; nlinarith)
  have hb0 : 0 ≤ conditionalEnd := conditionalEnd_pos.le
  have hb : conditionalEnd ≤ 1 := conditionalEnd_lt_one.le
  have hA0 : 0 ≤ A := by dsimp [A, SamplingCenterLp.amplification]; positivity
  have hA : A ≤ 3 := conditional_amplification_le_three d ρ
  have hterm : p * v * conditionalEnd ^ 2 * A ≤
      (1 / 2 : ℝ) * (1 / 2) * 1 ^ 2 * 3 := by
    gcongr
  have heq : d.r ^ 2 * (3 * d.ell + q * conditionalEnd * d.ell * A *
      (q * d.ell * conditionalEnd)) = 3 * p + p * v * conditionalEnd ^ 2 * A := by
    dsimp [p, v]
    ring
  change d.r ^ 2 * (3 * d.ell + q * conditionalEnd * d.ell * A *
    (q * d.ell * conditionalEnd)) ≤ 3
  rw [heq]
  linarith

private def sensitivity (d : Data ι m) (ρ : d.G.Kernel) : ℝ :=
  3 * d.ell + (conditionalData d ρ).r * conditionalEnd * d.ell *
    SamplingCenterLp.amplification (conditionalData d ρ) *
      ((conditionalData d ρ).r * d.ell * conditionalEnd)

private def backwardEnvelope (d : Data ι m) (j : Fin m)
    (ρ : d.G.Kernel) : ℝ :=
  seedBudget d + centerMove d j + d.r * |d.G.rho ρ - backwardEnd d.G.R| *
    (meanBudget d + Real.exp 1 * (d.r * d.ell) *
      Real.sqrt (Module.finrank ℝ E))

private theorem backwardEnvelope_le (d : Data ι m) (hrone : d.r ≤ 1)
    (hscale : d.ell * d.r / d.sigma ≤ 1) (j : Fin m)
    (ρ : d.G.Kernel) : backwardEnvelope d j ρ ≤ 12 * sourceSize d := by
  have hρ0 := (d.G.rho_mem ρ).1
  have hρ1 := ((d.G.rho_mem ρ).2.trans d.G.backwardEnd_lt_one).le
  have hb0 : 0 ≤ backwardEnd d.G.R := d.G.backwardEnd_pos.le
  have hb1 : backwardEnd d.G.R ≤ 1 := d.G.backwardEnd_lt_one.le
  have hdist : |d.G.rho ρ - backwardEnd d.G.R| ≤ 1 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hseed := seedBudget_le d hrone
  have hcenter := centerMove_le d hscale j
  have htransport := radius_transportBudget_le d hrone
  have htransport0 : 0 ≤ d.r * (meanBudget d + Real.exp 1 *
      (d.r * d.ell) * Real.sqrt (Module.finrank ℝ E)) := by
    have hmean : 0 ≤ meanBudget d := by
      unfold meanBudget radiusBudget
      positivity [d.hell, d.hr.le]
    positivity [d.hell, d.hr.le]
  have hscaled := mul_le_of_le_one_left htransport0 hdist
  unfold backwardEnvelope
  nlinarith

/-- Uniform source-size control of the actual random-center conditional mean
after its physical observation radius is restored. -/
theorem radius_conditionalMeanBudget_le (d : Data ι m) (hrone : d.r ≤ 1)
    (hscale : d.ell * d.r / d.sigma ≤ 1) (j : Fin m)
    (ρ : d.G.Kernel) :
    d.r * conditionalMeanBudget d j ρ ≤ 40 * sourceSize d := by
  let q := (conditionalData d ρ).r
  let s := Real.sqrt (Module.finrank ℝ E)
  let C := sensitivity d ρ
  let B := backwardEnvelope d j ρ
  have hr0 : 0 ≤ d.r := d.hr.le
  have hq0 : 0 ≤ q := (conditionalData d ρ).hr.le
  have hqr : q ≤ d.r := conditional_radius_le d ρ
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hρ0 : 0 ≤ d.G.rho ρ := (d.G.rho_mem ρ).1
  have hρ1 : d.G.rho ρ ≤ 1 :=
    ((d.G.rho_mem ρ).2.trans d.G.backwardEnd_lt_one).le
  have hC0 : 0 ≤ C := by
    dsimp [C, sensitivity, SamplingCenterLp.amplification]
    positivity [d.hell, (conditionalData d ρ).hr.le, conditionalEnd_pos.le]
  have hC : d.r ^ 2 * C ≤ 3 := conditional_sensitivity_paid_le d ρ
  have hB0 : 0 ≤ B := by
    dsimp [B, backwardEnvelope, centerMove, seedBudget, meanBudget, radiusBudget,
      CenteringFlowLp.alpha]
    positivity [d.hell, d.hr.le, d.hsigma.le, d.G.backwardEnd_pos.le]
  have hB : B ≤ 12 * sourceSize d := backwardEnvelope_le d hrone hscale j ρ
  have hsource0 := sourceSize_nonneg d
  have hcenterTerm : d.r ^ 2 * C * d.G.rho ρ * B ≤
      3 * 1 * (12 * sourceSize d) := by
    gcongr
  have hm := radius_meanBudget_le d hrone
  have hp : d.ell * d.r ^ 2 ≤ 1 / 2 := by nlinarith [d.hsmall]
  have hp0 : 0 ≤ d.ell * d.r ^ 2 := by positivity [d.hell]
  have hqrTerm : d.r * q * d.ell ≤ d.ell * d.r ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hqr (mul_nonneg hr0 d.hell)
    nlinarith
  have hqrTerm0 : 0 ≤ d.r * q * d.ell := by positivity [d.hell]
  have hqrTerm1 : d.r * q * d.ell ≤ 1 / 2 := hqrTerm.trans hp
  have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  have he0 : 0 ≤ Real.exp 1 := (Real.exp_pos _).le
  have hfluct : d.r * Real.exp 1 * (q * d.ell) * s ≤ 2 * sourceSize d := by
    have hh : Real.exp 1 * (d.r * q * d.ell) * s ≤
        3 * (1 / 2) * s := by gcongr
    have hss : s ≤ sourceSize d := by
      dsimp [sourceSize]
      exact le_add_of_nonneg_right (norm_nonneg _)
    nlinarith
  have heq : conditionalMeanBudget d j ρ =
      meanBudget d + Real.exp 1 * (q * d.ell) * s +
        C * (d.r * d.G.rho ρ) * B := by
    dsimp [conditionalMeanBudget, C, sensitivity, B, backwardEnvelope,
      centerMove, q, s]
  rw [heq]
  nlinarith

private theorem conditionalMeanBudget_nonneg (d : Data ι m) (j : Fin m)
    (ρ : d.G.Kernel) : 0 ≤ conditionalMeanBudget d j ρ := by
  exact (norm_nonneg (conditionalMeanLp d j ρ 0)).trans
    (norm_conditionalMeanLp_le_data d j ρ 0 ⟨le_rfl, conditionalEnd_pos.le⟩)

theorem conditionalRowTerm_le (d : Data ι m) (hrone : d.r ≤ 1)
    (hscale : d.ell * d.r / d.sigma ≤ 1) (j : Fin m)
    (ρ : d.G.Kernel) (i : (d.G.conditional ρ).Source m) :
    (Real.sqrt (d.G.variance ρ) * (d.G.conditional ρ).location m i) *
      ((d.r * Real.sqrt (d.G.variance ρ)) *
        |(d.G.conditional ρ).location m i| * conditionalMeanBudget d j ρ) ≤
          40 * sourceSize d := by
  let v := Real.sqrt (d.G.variance ρ)
  let a := (d.G.conditional ρ).location m i
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hv1 : v ≤ 1 := Real.sqrt_le_one.mpr (by
    unfold MeanGeometry.variance
    nlinarith [sq_nonneg (d.G.rho ρ)])
  have ha0 : 0 ≤ a := ((d.G.conditional ρ).location_mem_interval m i).1.le
  have ha1 : a ≤ 1 :=
    (((d.G.conditional ρ).location_mem_interval m i).2.trans conditionalEnd_lt_one).le
  have hva0 : 0 ≤ v * a := mul_nonneg hv0 ha0
  have hva1 : v * a ≤ 1 := by
    calc
      v * a ≤ 1 * a := mul_le_mul_of_nonneg_right hv1 ha0
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left ha1 (by norm_num)
      _ = 1 := by ring
  have hc0 := conditionalMeanBudget_nonneg d j ρ
  have hrc0 : 0 ≤ d.r * conditionalMeanBudget d j ρ := mul_nonneg d.hr.le hc0
  have hrc := radius_conditionalMeanBudget_le d hrone hscale j ρ
  rw [abs_of_nonneg ha0]
  have heq : (v * a) * ((d.r * v) * a * conditionalMeanBudget d j ρ) =
      (v * a) * ((v * a) * (d.r * conditionalMeanBudget d j ρ)) := by ring
  change (v * a) * ((d.r * v) * a * conditionalMeanBudget d j ρ) ≤ _
  rw [heq]
  have h₁ := mul_le_of_le_one_left hrc0 hva1
  have h₂ := mul_le_of_le_one_left (mul_nonneg hva0 hrc0) hva1
  nlinarith [mul_le_mul_of_nonneg_left h₁ hva0]

theorem forwardMove_le (d : Data ι m) (hrone : d.r ≤ 1)
    (hscale : d.ell * d.r / d.sigma ≤ 1) (hpsi : d.G.psi ≤ 1)
    (j : Fin m) (ρ : d.G.Kernel) (z : Fin m)
    (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) :
    forwardMove d j ρ z a ≤ 60 * sourceSize d := by
  let w := d.G.angleNode z
  let v := Real.sqrt (d.G.variance ρ)
  let c := conditionalMeanBudget d j ρ
  have hw0 : 0 ≤ w := (d.G.angleNode_bounds z).1
  have hw1 : w ≤ 1 := (d.G.angleNode_bounds z).2.trans hpsi
  have hw2 : w ^ 2 ≤ 1 := by nlinarith
  have hseed0 : 0 ≤ d.G.seedRot ρ w := d.G.seedRot_nonneg ρ w
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hc0 : 0 ≤ c := conditionalMeanBudget_nonneg d j ρ
  have hrc0 : 0 ≤ d.r * c := mul_nonneg d.hr.le hc0
  have hrc := radius_conditionalMeanBudget_le d hrone hscale j ρ
  have hscaled := d.G.seedRot_scaled_le_sq ρ w
  have hseedTerm : d.G.seedRot ρ w * ((d.r * v) *
      (|conditionalEnd| * c)) ≤ 40 * sourceSize d := by
    rw [abs_of_nonneg conditionalEnd_pos.le]
    have heq : d.G.seedRot ρ w * ((d.r * v) * (conditionalEnd * c)) =
        (d.G.seedRot ρ w * v * conditionalEnd) * (d.r * c) := by ring
    rw [heq]
    exact (mul_le_mul_of_nonneg_right (hscaled.trans hw2) hrc0).trans
      (by simpa using hrc)
  have hb := backwardMove_le d hrone hscale j (d.G.rho ρ)
    ⟨(d.G.rho_mem ρ).1, ((d.G.rho_mem ρ).2.trans d.G.backwardEnd_lt_one).le⟩
  have hs := scoreMove_le d hscale j
  have hs0 : 0 ≤ scoreMove d j := by
    unfold scoreMove CenteringFlowLp.alpha
    dsimp [kernelData]
    positivity [d.hell, d.hr.le, d.hsigma.le]
  have hscore := mul_le_mul_of_nonneg_right hw1 hs0
  have hscore' := mul_le_mul_of_nonneg_left hs hw0
  have ht := radius_transportBudget_le d hrone
  have htransport0 : 0 ≤ d.r * (meanBudget d + Real.exp 1 *
      (d.r * d.ell) * Real.sqrt (Module.finrank ℝ E)) := by
    have hmean : 0 ≤ meanBudget d := by
      unfold meanBudget radiusBudget
      positivity [d.hell, d.hr.le]
    positivity [d.hell, d.hr.le]
  have hρ0 := (d.G.rho_mem ρ).1
  have hρ1 := ((d.G.rho_mem ρ).2.trans d.G.backwardEnd_lt_one).le
  have hdist : |a - d.G.rho ρ| ≤ 1 :=
    abs_le.mpr ⟨by linarith [ha.1], by linarith [ha.2]⟩
  have htrans := mul_le_of_le_one_left htransport0 hdist
  unfold forwardMove
  nlinarith

/-- Every literal row coefficient has the same numerical majorant. The proof
uses only physical interval lengths and never sums over graph nodes. -/
theorem rowCoefficient_le_sourceSize (d : Data ι m) (hrone : d.r ≤ 1)
    (hscale : d.ell * d.r / d.sigma ≤ 1) (hpsi : d.G.psi ≤ 1)
    (i : d.G.MeanNode) :
    rowCoefficient d i ≤ 100 * sourceSize d := by
  have hsize0 := sourceSize_nonneg d
  rcases i with u | j | ⟨j,k⟩ | ⟨j,ρ,k⟩ | ⟨j,ρ,z,k⟩
  · cases u
    simp [rowCoefficient]
    positivity
  · have hb0 : 0 ≤ backwardEnd d.G.R := d.G.backwardEnd_pos.le
    have hb1 : backwardEnd d.G.R ≤ 1 := d.G.backwardEnd_lt_one.le
    have hmove := centerMove_le d hscale j
    have hh := mul_le_mul_of_nonneg_left hmove hb0
    have hhh := mul_le_of_le_one_left (mul_nonneg (by norm_num : (0:ℝ) ≤ 6) hsize0) hb1
    change backwardEnd d.G.R * centerMove d j ≤ _
    nlinarith
  · have ha := d.G.backward.location_mem_interval m k
    have ha0 : 0 ≤ d.G.backward.location m k := ha.1.le
    have ha1 : d.G.backward.location m k ≤ 1 :=
      (ha.2.trans d.G.backwardEnd_lt_one).le
    have hmove := backwardMove_le d hrone hscale j _ ⟨ha0, ha1⟩
    have hh := mul_le_mul_of_nonneg_left hmove ha0
    have hhh := mul_le_of_le_one_left (mul_nonneg (by norm_num : (0:ℝ) ≤ 10) hsize0) ha1
    change d.G.backward.location m k * backwardMove d j (d.G.backward.location m k) ≤ _
    nlinarith
  · have hρ0 : 0 ≤ d.G.rho ρ := (d.G.rho_mem ρ).1
    have hρ1 : d.G.rho ρ ≤ 1 :=
      ((d.G.rho_mem ρ).2.trans d.G.backwardEnd_lt_one).le
    have hmove := backwardMove_le d hrone hscale j _ ⟨hρ0, hρ1⟩
    have hh := mul_le_mul_of_nonneg_left hmove hρ0
    have hhh := mul_le_of_le_one_left (mul_nonneg (by norm_num : (0:ℝ) ≤ 10) hsize0) hρ1
    have hc := conditionalRowTerm_le d hrone hscale j ρ k
    change d.G.rho ρ * backwardMove d j (d.G.rho ρ) +
      (Real.sqrt (d.G.variance ρ) * (d.G.conditional ρ).location m k) *
        ((d.r * Real.sqrt (d.G.variance ρ)) *
          |(d.G.conditional ρ).location m k| * conditionalMeanBudget d j ρ) ≤ _
    nlinarith
  · have ha := (d.G.forward ρ).location_mem_interval m k
    have ha0 : 0 ≤ (d.G.forward ρ).location m k :=
      (d.G.rho_mem ρ).1.trans ha.1.le
    have ha1 : (d.G.forward ρ).location m k ≤ 1 :=
      (ha.2.trans d.G.backwardEnd_lt_one).le
    have hmove := forwardMove_le d hrone hscale hpsi j ρ z _ ⟨ha0, ha1⟩
    have hh := mul_le_mul_of_nonneg_left hmove ha0
    have hhh := mul_le_of_le_one_left (mul_nonneg (by norm_num : (0:ℝ) ≤ 60) hsize0) ha1
    change (d.G.forward ρ).location m k *
      forwardMove d j ρ z ((d.G.forward ρ).location m k) ≤ _
    nlinarith

/-- The exact finite inventory norm is controlled by one source-size factor. -/
theorem norm_rowCoefficient_le_sourceSize (d : Data ι m) (hrone : d.r ≤ 1)
    (hscale : d.ell * d.r / d.sigma ≤ 1) (hpsi : d.G.psi ≤ 1) :
    ‖rowCoefficient d‖ ≤ 100 * sourceSize d := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) (sourceSize_nonneg d))).mpr
  intro i
  have hrow := row_displacement_le d i
  have hnonneg : 0 ≤ rowCoefficient d i := by
    have hr := d.hr
    have hn := norm_nonneg (reference d i - (lpGraph d).direct i)
    nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact rowCoefficient_le_sourceSize d hrone hscale hpsi i

/-- The exact common-seed initializer has a dimension and gradient bound
with an absolute coefficient, independent of order and row count. -/
theorem initialError_le_sourceSize (d : Data ι m) (hrone : d.r ≤ 1)
    (hscale : d.ell * d.r / d.sigma ≤ 1) (hpsi : d.G.psi ≤ 1) :
    initialError d ≤ 100 * d.r * sourceSize d := by
  have hcoef := norm_rowCoefficient_le_sourceSize d hrone hscale hpsi
  have hinit := initialError_le_data d
  have hh := mul_le_mul_of_nonneg_left hcoef d.hr.le
  nlinarith

end AcceleratedLogConcave.Numerics.SmoothInitialUniformBound
