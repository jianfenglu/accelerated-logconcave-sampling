import AcceleratedLogConcave.Numerics.SmoothConditional

/-!
# Literal conditional replacement in the mean residual receiver

The replacement mean equals its smooth common-seed lift on the whole open
construction slab. This proves ordinary smoothness at both source endpoints.
The source equations, rotation, and every reference row are preserved.
No quantitative CellRegularity or full Regularity is asserted.
-/
noncomputable section
open Set Function MeasureTheory
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Numerics.MeanResidualBridge
open MeanFlowLp AffineGraph AffineGraph.MeanGeometry
open ConditionalSmoothing Analysis.PositiveVarianceSlab
section Algebraic
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {m : ℕ} (G : MeanGeometry m) (C : AffineResidual.Mean.Curves G X)
  (D : Fin m → G.Kernel → ℝ → X)
  (hD : ∀ j ρ t, t ∈ Icc 0 conditionalEnd → D j ρ t = C.conditional j ρ t)
include hD

private theorem conditionalReplacement_mean_eq (U : X → ℝ → X) (x : X) (r : ℝ)
    (j : Fin m) (ρ : G.Kernel) {t : ℝ} (ht : t ∈ Icc 0 conditionalEnd) :
    ({ C with conditional := D } : AffineResidual.Mean.Curves G X).conditionalMean G U x r j ρ t =
      C.conditionalMean G U x r j ρ t := by
  change U (x+(r*G.rho ρ) • C.backward j (G.rho ρ)+(r*Real.sqrt (G.variance ρ)*t) • D j ρ t) _ = _
  rw [hD j ρ t ht]
  rfl

private theorem conditionalReplacement_rotation_eq (j : Fin m) (ρ : G.Kernel) (z : ℝ) :
    ({ C with conditional := D } : AffineResidual.Mean.Curves G X).rotation G j ρ z =
      C.rotation G j ρ z := by
  simp only [AffineResidual.Mean.Curves.rotation,hD j ρ conditionalEnd ⟨conditionalEnd_pos.le,le_rfl⟩]

private theorem conditionalReplacement_reference_eq (x : X) (r : ℝ) :
    ({ C with conditional := D } : AffineResidual.Mean.Curves G X).reference G x r =
      C.reference G x r := by
  funext i
  rcases i with _ | j | ⟨j,ρ⟩ | ⟨j,⟨ρ,k⟩⟩ | ⟨j,⟨ρ,z,k⟩⟩
  · rfl
  · rfl
  · rfl
  · have ht := (G.conditional ρ).location_mem_interval m k
    change x+(r*G.rho ρ) • C.backward j (G.rho ρ)+
      (r*Real.sqrt (G.variance ρ)*(G.conditional ρ).location m k) • D j ρ ((G.conditional ρ).location m k) = _
    rw [hD j ρ _ ⟨ht.1.le,ht.2.le⟩]
    rfl
  · rfl

private theorem conditionalReplacement_equations (U : X → ℝ → X) (r σ : ℝ)
    (x y0 g0 : X) (ζ : Fin m → G.Kernel → X)
    (h : AffineResidual.Mean.Equations G C U r σ x y0 g0 ζ) :
    AffineResidual.Mean.Equations G { C with conditional := D } U r σ x y0 g0 ζ := by
  constructor
  · exact h.position
  · exact h.score
  · exact h.backward
  · intro j ρ t ht
    change D j ρ t = _
    rw [hD j ρ t ht,h.conditional j ρ t ht]
    congr 2
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht.1] at hu
    exact (conditionalReplacement_mean_eq G C D hD U x r j ρ ⟨hu.1,hu.2.trans ht.2⟩).symm
  · intro j ρ z t hz ht
    rw [conditionalReplacement_rotation_eq G C D hD]
    exact h.forward j ρ z t hz ht
  · exact h.kernel_angle
  · exact h.velocity_kernel
end Algebraic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι
variable (d : MeanFlowLp.Data ι m)

def curvesWithConditional : AffineResidual.Mean.Curves d.G (H d) :=
  { curves d with conditional := smoothConditional d }

@[simp] theorem curvesWithConditional_position :
    (curvesWithConditional d).position = (curves d).position := rfl
@[simp] theorem curvesWithConditional_score :
    (curvesWithConditional d).score = (curves d).score := rfl
@[simp] theorem curvesWithConditional_velocity :
    (curvesWithConditional d).velocity = (curves d).velocity := rfl
@[simp] theorem curvesWithConditional_backward :
    (curvesWithConditional d).backward = (curves d).backward := rfl
@[simp] theorem curvesWithConditional_forward :
    (curvesWithConditional d).forward = (curves d).forward := rfl
@[simp] theorem curvesWithConditional_kernel :
    (curvesWithConditional d).kernel = (curves d).kernel := rfl

theorem smoothConditionalReplacement_conditionalMean_eq (U : H d → ℝ → H d)
    (j : Fin m) (ρ : d.G.Kernel) {t : ℝ} (ht : t ∈ Icc 0 conditionalEnd) :
    (curvesWithConditional d).conditionalMean d.G U 0 d.r j ρ t =
      (curves d).conditionalMean d.G U 0 d.r j ρ t := by
  simp only [AffineResidual.Mean.Curves.conditionalMean,curvesWithConditional,curves,
    smoothConditional_eq d j ρ ht]

theorem smoothConditionalReplacement_rotation_eq (j : Fin m) (ρ : d.G.Kernel) (z : ℝ) :
    (curvesWithConditional d).rotation d.G j ρ z = (curves d).rotation d.G j ρ z := by
  simp only [AffineResidual.Mean.Curves.rotation,curvesWithConditional,curves,
    smoothConditional_eq d j ρ ⟨conditionalEnd_pos.le,le_rfl⟩]

theorem smoothConditionalReplacement_reference_eq :
    (curvesWithConditional d).reference d.G 0 d.r = (curves d).reference d.G 0 d.r :=
  conditionalReplacement_reference_eq d.G (curves d) (smoothConditional d)
    (fun j ρ _ ht => smoothConditional_eq d j ρ ht) 0 d.r

omit [DecidableEq ι] in
private theorem replacement_smul_ae {Z : H d} {f : Seed d → E}
    (h : (Z : Seed d → E) =ᵐ[seedMeasure d] f) (a : ℝ) :
    (a • Z : H d) =ᵐ[seedMeasure d] (fun w => a • f w) := by
  filter_upwards [Lp.coeFn_smul a Z,h] with w h1 h2
  simpa only [Pi.smul_apply,h2] using h1

omit [DecidableEq ι] in
private theorem replacement_add_ae {Z W : H d} {f g : Seed d → E}
    (hZ : (Z : Seed d → E) =ᵐ[seedMeasure d] f)
    (hW : (W : Seed d → E) =ᵐ[seedMeasure d] g) :
    (Z+W : H d) =ᵐ[seedMeasure d] (fun w => f w+g w) := by
  filter_upwards [Lp.coeFn_add Z W,hZ,hW] with w h1 h2 h3
  simpa only [Pi.add_apply,h2,h3] using h1

/-- The first time jet is the actual physical posterior mean on the open slab. -/
theorem smoothConditionalMean_ae (j : Fin m) (ρ : d.G.Kernel) {t : ℝ}
    (ht : t ∈ Ioo (left conditionalEnd) (right conditionalEnd)) :
    (smoothConditionalMean d j ρ t : Seed d → E) =ᵐ[seedMeasure d]
      (fun w => Gibbs.primitiveMean d.F
        (conditionalCenter d j ρ w + ((conditionalData d ρ).r*t) • conditionalJet d j ρ 0 t w)
        ((conditionalData d ρ).r*Real.sqrt (1-t^2))) := by
  have htime : time (conditionalData d ρ) t = t := time_eq _ ⟨ht.1.le,ht.2.le⟩
  have ht' := construction_subset conditionalEnd_pos.le conditionalEnd_lt_one ⟨ht.1.le,ht.2.le⟩
  have h := replacement_smul_ae d (conditionalJet_memLp d j ρ 1 t).coeFn_toLp
    (-(conditionalData d ρ).r)⁻¹
  filter_upwards [h] with w hw
  erw [hw]
  simp only [conditionalJet,jet_one,openVelocity,htime,jet_zero,jointPath_fst,
    conditionalInput]
  rw [smul_smul,inv_mul_cancel₀ (neg_ne_zero.mpr (conditionalData d ρ).hr.ne'),one_smul]
  exact AffineFlowIdentities.conditionalMean_eq_primitiveMean d.hF d.hell d.hlo d.hup
    (conditionalCenter d j ρ w) (conditionalData d ρ).hr ht'.1 ht'.2 _

/-- Equality on an open neighborhood is essential: closed-slab agreement alone
would not transfer ordinary endpoint derivatives. -/
theorem replacement_conditionalMean_eq_smooth (U : H d → ℝ → H d)
    (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U)
    (j : Fin m) (ρ : d.G.Kernel) {t : ℝ}
    (ht : t ∈ Ioo (left conditionalEnd) (right conditionalEnd)) :
    (curvesWithConditional d).conditionalMean d.G U 0 d.r j ρ t = smoothConditionalMean d j ρ t := by
  have ht' := construction_subset conditionalEnd_pos.le conditionalEnd_lt_one ⟨ht.1.le,ht.2.le⟩
  have hq : 0 < (conditionalData d ρ).r*Real.sqrt (1-t^2) :=
    mul_pos (conditionalData d ρ).hr (Real.sqrt_pos.mpr (by nlinarith [ht'.1,ht'.2]))
  have hc := replacement_add_ae d
    (replacement_smul_ae d (backward_memLp d j (d.G.rho ρ)).coeFn_toLp (d.r*d.G.rho ρ))
    (replacement_smul_ae d (conditionalJet_memLp d j ρ 0 t).coeFn_toLp
      (d.r*Real.sqrt (d.G.variance ρ)*t))
  let Z : H d := (d.r*d.G.rho ρ) • backwardLp d j (d.G.rho ρ) +
    (d.r*Real.sqrt (d.G.variance ρ)*t) • smoothConditional d j ρ t
  have hp := hu.2.1 Z ((conditionalData d ρ).r*Real.sqrt (1-t^2)) hq
  simp only [AffineResidual.Mean.Curves.conditionalMean,zero_add,curvesWithConditional,curves]
  apply Lp.ext
  filter_upwards [hp,hc,smoothConditionalMean_ae d j ρ ht] with w h1 h2 h3
  erw [h1,h2,h3]
  simp only [primitiveData,conditionalCenter,conditionalData,add_assoc]

theorem contDiffAt_replacement_conditionalMean (U : H d → ℝ → H d)
    (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U)
    (j : Fin m) (ρ : d.G.Kernel) (n : ℕ) {t : ℝ} (ht : t ∈ Icc 0 conditionalEnd) :
    ContDiffAt ℝ n ((curvesWithConditional d).conditionalMean d.G U 0 d.r j ρ) t := by
  have ht' := source_subset conditionalEnd_pos.le conditionalEnd_lt_one ht
  have hs := (contDiffOn_smoothConditionalMean d j ρ n t ht').contDiffAt
    (isOpen_Ioo.mem_nhds ht')
  apply hs.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht'] with u hu'
  exact replacement_conditionalMean_eq_smooth d U hu j ρ hu'

theorem smoothConditionalReplacement_equations (U : H d → ℝ → H d)
    (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U) :
    AffineResidual.Mean.Equations d.G (curvesWithConditional d) U d.r d.sigma 0
      (initialPosition d) (initialScore d) (initialNoise d) :=
  conditionalReplacement_equations d.G (curves d) (smoothConditional d)
    (fun j ρ _ ht => smoothConditional_eq d j ρ ht) U d.r d.sigma 0
    (initialPosition d) (initialScore d) (initialNoise d) (equations d U hu)

end AcceleratedLogConcave.Numerics.MeanResidualBridge
