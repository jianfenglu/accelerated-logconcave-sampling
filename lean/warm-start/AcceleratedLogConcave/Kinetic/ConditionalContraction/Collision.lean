import AcceleratedLogConcave.Kinetic.ConditionalContraction.ConditionalCorrector
import AcceleratedLogConcave.Kinetic.ConditionalContraction.MomentumReheatingLoss
import AcceleratedLogConcave.Kinetic.Reheating.Current

/-! Actual collision-stage corrected energy. The sole remaining analytic
intermediates are explicitly named DormantW12 and OrdinaryHeatCurrentBound. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace ContDiff
namespace AcceleratedLogConcave.Kinetic.ConditionalContraction
open Analysis.Poisson Reheating
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [IsProbabilityMeasure μ]

private theorem collision_ou_decay_lower (r : ℝ) (hr : 0 ≤ r) (hr' : r ≤ 1/2) :
    r ≤ 1 - Real.exp (-2*r) := by
  have he := Real.add_one_le_exp (2*r)
  have hexp : Real.exp (-2*r) * Real.exp (2*r) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos (-2*r)).le
  rw [hexp] at hm
  by_contra h
  have hp : 0 < Real.exp (-2*r) + r - 1 := by linarith
  have hpos := mul_pos (show 0 < 1 + 2*r by linarith) hp
  nlinarith

/-- A stronger retained loss used for energy absorption. -/
theorem momentum_reheating_micro_loss_half (r : ℝ) (hr : 0 ≤ r) (hr' : r ≤ 1/2)
    (t : ℝ) (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    (r/2) * ‖f - gaussianPositionProjection μ f‖^2 ≤
      ‖f‖^2 - ‖ouProduct (heatedLaw μ t) r hr (reheatingDensity μ t f)‖^2 := by
  let O := momentumCollision μ r hr
  let X := ‖f - momentumBaseEmbedding μ (momentumAverage μ f)‖^2
  let Y := ‖momentumAverage μ f - productEmbedding μ (stdGaussian E) (gaussianAverage μ f)‖^2
  let Z := ‖O f - Reheating.hiddenEmbedding μ (hiddenAverage μ (O f))‖^2
  have hP := momentumCollision_loss μ r hr f
  change (1 - Real.exp (-2*r)) * X ≤ ‖f‖^2 - ‖O f‖^2 at hP
  have hE := reheating_hidden_loss μ t (O f)
  change (1/4 : ℝ) * Z ≤ ‖O f‖^2 - ‖reheatingDensity μ t (O f)‖^2 at hE
  have hYZ : Y ≤ Z := by
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (momentumAverage_hidden_residual_le μ r hr f)
  have hfirst : (r/2) * X ≤ ‖f‖^2 - ‖O f‖^2 := by
    apply le_trans _ hP
    exact mul_le_mul_of_nonneg_right (by linarith [collision_ou_decay_lower r hr hr']) (sq_nonneg _)
  have hsecond : (r/2) * Y ≤ ‖O f‖^2 - ‖reheatingDensity μ t (O f)‖^2 := by
    apply le_trans _ hE
    calc
      _ ≤ (r/2) * Z := mul_le_mul_of_nonneg_left hYZ (by positivity)
      _ ≤ (1/4 : ℝ) * Z := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  rw [← reheatingDensity_momentumCollision]
  have hsplit := momentum_micro_decomposition μ f
  change ‖f - gaussianPositionProjection μ f‖^2 = X + Y at hsplit
  rw [hsplit, mul_add]
  linarith

variable (t : ℝ) (V₀ Vₜ : E → ℝ) (hV₀ : ContDiff ℝ 2 V₀) (hVₜ : ContDiff ℝ 2 Vₜ)
  (hI₀ : Integrable (fun x => Real.exp (-V₀ x))) (hIₜ : Integrable (fun x => Real.exp (-Vₜ x)))
  (hμ₀ : μ = volume.tilted (fun x => -V₀ x))
  (hμₜ : heatedLaw μ t = volume.tilted (fun x => -Vₜ x))
  (m mₜ L : ℝ) (hm : 0 < m) (hmₜ : 0 < mₜ)
  (hl₀ : ∀ x a, m*‖a‖^2 ≤ fderiv ℝ (fderiv ℝ V₀) x a a)
  (hu₀ : ∀ x a, fderiv ℝ (fderiv ℝ V₀) x a a ≤ L*‖a‖^2)
  (hlₜ : ∀ x a, mₜ*‖a‖^2 ≤ fderiv ℝ (fderiv ℝ Vₜ) x a a)
  (huₜ : ∀ x a, fderiv ℝ (fderiv ℝ Vₜ) x a a ≤ L*‖a‖^2)

/-- Explicit ordinary heat-current intermediate, to be discharged by the actual
relative-density heat evolution. It concerns only the ordinary heat channel. -/
def OrdinaryHeatCurrentBound : Prop :=
  ∀ g : Lp ℝ 2 (μ.prod (stdGaussian E)),
    let v₀ := heatDensity μ t (Reheating.hiddenEmbedding μ g)
    |inner ℝ (visibleCorrector (heatedLaw μ t) Vₜ hVₜ hIₜ hμₜ mₜ L hmₜ hlₜ huₜ v₀) v₀ -
      inner ℝ (visibleCorrector μ V₀ hV₀ hI₀ hμ₀ m L hm hl₀ hu₀ g) g| ≤
    (t/4)*‖g‖^2 + Real.sqrt (t*(‖g‖^2-‖v₀‖^2))*‖g‖

variable {Ω : Type*} [MeasurableSpace Ω] {η : Measure Ω}
  {p q : Ω → GaussianPhase E}
  (hp : MeasurePreserving p η (gaussianPhaseMeasure μ))
  (hq : MeasurePreserving q η (gaussianPhaseMeasure μ))
  (hpos : ∀ z, (p z).1.1 = (q z).1.1)

/-- Actual collision output, in the physical dormant/reheat/momentum order. -/
def collisionDensity (Γ : ℝ) (hΓ : 0 ≤ Γ) :
    Lp ℝ 2 (gaussianPhaseMeasure μ) →L[ℝ] Lp ℝ 2 ((heatedLaw μ t).prod (stdGaussian E)) :=
  (ouProduct (heatedLaw μ t) Γ hΓ).comp
    ((reheatingDensity μ t).comp (referenceChannel hp hq).adjoint)

include hpos

/-- Corrected energy across the actual complete collision stages. Only the
named W12 and ordinary heat-current intermediates remain explicit. -/
theorem collision_energy_le_of_ordinary_current
    (ht : 0 ≤ t) (Γ : ℝ) (hΓ : 0 ≤ Γ) (hΓ' : Γ ≤ 1/2)
    (θ : ℝ) (hθ : 0 ≤ θ) (C a : ℝ)
    (hW : DormantW12 μ hp hq V₀ hV₀ hI₀ hμ₀ m L hm hl₀ hu₀ C a)
    (hcurrent : OrdinaryHeatCurrentBound μ t V₀ Vₜ hV₀ hVₜ hI₀ hIₜ hμ₀ hμₜ m mₜ L hm hmₜ hl₀ hu₀ hlₜ huₜ)
    (hsmall : (θ * Real.sqrt m) * Real.sqrt t ≤ 1/24)
    (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    quadraticEnergy (visibleCorrector (heatedLaw μ t) Vₜ hVₜ hIₜ hμₜ mₜ L hmₜ hlₜ huₜ)
      (θ * Real.sqrt m) (collisionDensity μ t hp hq Γ hΓ f) ≤
    gaussianCorrectedEnergy μ V₀ hV₀ hI₀ hμ₀ m L hm hl₀ hu₀ (θ * Real.sqrt m) f -
      (Γ/32) * ‖f - gaussianPositionProjection μ f‖^2 +
      (8*θ^2*Γ + (C/2)*(θ*Real.sqrt m)*a +
        100*((θ*Real.sqrt m)+(θ*Real.sqrt m)^2)*t) * ‖f‖^2 := by
  let ε := θ * Real.sqrt m
  let z := (referenceChannel hp hq).adjoint f
  let w := momentumCollision μ Γ hΓ z
  let v := reheatingDensity μ t w
  have hε : 0 ≤ ε := mul_nonneg hθ (Real.sqrt_nonneg m)
  have hQ := positionChannel_correctedEnergy_le μ hp hq hpos V₀ hV₀ hI₀ hμ₀ m L hm hl₀ hu₀
    C a ε hε hW f
  have hO := momentumCollision_correctedEnergy_le μ V₀ hV₀ hI₀ hμ₀ m L hm hl₀ hu₀ Γ hΓ θ hθ z
  have hH := reheating_energy_le_of_ordinary_current μ t ht V₀ Vₜ hV₀ hVₜ hI₀ hIₜ hμ₀ hμₜ
    m mₜ L hm hmₜ hl₀ hu₀ hlₜ huₜ hcurrent ε hε hsmall w
  have hloss := momentum_reheating_micro_loss_half μ Γ hΓ hΓ' t z
  rw [← reheatingDensity_momentumCollision] at hloss
  have hzn : ‖z‖ ≤ ‖f‖ := by
    have hn : ‖(referenceChannel hp hq).adjoint‖ ≤ 1 := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact referenceChannel_norm_le hp hq
    simpa only [one_mul] using ContinuousLinearMap.le_of_opNorm_le _ hn f
  have hwn : ‖w‖ ≤ ‖z‖ := by
    simpa only [one_mul] using ContinuousLinearMap.le_of_opNorm_le _ (momentumCollision_norm_le μ Γ hΓ) z
  have hDz : 0 ≤ ‖f‖^2 - ‖z‖^2 := by nlinarith [norm_nonneg f, norm_nonneg z]
  have hDw : 0 ≤ ‖z‖^2 - ‖w‖^2 := by nlinarith [norm_nonneg z, norm_nonneg w]
  have hwf : ‖w‖^2 ≤ ‖f‖^2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hwn.trans hzn)
  have hP : gaussianPositionProjection μ z = gaussianPositionProjection μ f :=
    positionProjection_positionChannel_adjoint μ hp hq hpos f
  have hsplit := positionChannel_micro_loss μ hp hq hpos f
  change ‖f - gaussianPositionProjection μ f‖^2 =
    ‖z - gaussianPositionProjection μ z‖^2 + (‖f‖^2 - ‖z‖^2) at hsplit
  have hmacro : ‖gaussianPositionProjection μ z‖^2 ≤ ‖f‖^2 := by
    rw [hP]
    nlinarith [gaussianPositionProjection_norm_sq μ f, sq_nonneg ‖f - gaussianPositionProjection μ f‖]
  have hObudget := mul_le_mul_of_nonneg_left hmacro (show 0 ≤ 8*θ^2*Γ by positivity)
  have hHbudget := mul_le_mul_of_nonneg_left hwf (show 0 ≤ 100*(ε+ε^2)*t by positivity)
  have hreserve := mul_nonneg (show 0 ≤ (1/2 : ℝ) - Γ/32 by linarith) hDz
  have hmicro := mul_nonneg hΓ (sq_nonneg ‖z - gaussianPositionProjection μ z‖)
  have hv : collisionDensity μ t hp hq Γ hΓ f = v :=
    (reheatingDensity_momentumCollision μ Γ hΓ t z).symm
  rw [hv]
  change quadraticEnergy _ ε v ≤ _
  change gaussianCorrectedEnergy μ V₀ hV₀ hI₀ hμ₀ m L hm hl₀ hu₀ ε z ≤
    gaussianCorrectedEnergy μ V₀ hV₀ hI₀ hμ₀ m L hm hl₀ hu₀ ε f - (1/2:ℝ)*(‖f‖^2-‖z‖^2) +
      (C/2)*ε*a*‖f‖^2 at hQ
  change gaussianCorrectedEnergy μ V₀ hV₀ hI₀ hμ₀ m L hm hl₀ hu₀ ε w ≤
    gaussianCorrectedEnergy μ V₀ hV₀ hI₀ hμ₀ m L hm hl₀ hu₀ ε z - (1/2:ℝ)*(‖z‖^2-‖w‖^2) +
      (Γ/32)*‖z-gaussianPositionProjection μ z‖^2 + 8*θ^2*Γ*‖gaussianPositionProjection μ z‖^2 at hO
  change (Γ/2)*‖z-gaussianPositionProjection μ z‖^2 ≤ ‖z‖^2-‖v‖^2 at hloss
  change _ ≤ gaussianCorrectedEnergy μ V₀ hV₀ hI₀ hμ₀ m L hm hl₀ hu₀ ε f -
    (Γ/32)*‖f-gaussianPositionProjection μ f‖^2 + (8*θ^2*Γ+(C/2)*ε*a+100*(ε+ε^2)*t)*‖f‖^2
  nlinarith

/-- Source-scale collision estimate with the explicit absolute coefficient
`C₂ = C/2 + 200`, conditional only on W12 and ordinary heat current. -/
theorem collision_energy_source_le_of_ordinary_current
    (ht : 0 ≤ t) (Γ : ℝ) (hΓ : 0 ≤ Γ) (hΓ' : Γ ≤ 1/2)
    (θ : ℝ) (hθ : 0 ≤ θ) (C a : ℝ)
    (hW : DormantW12 μ hp hq V₀ hV₀ hI₀ hμ₀ m L hm hl₀ hu₀ C a)
    (hcurrent : OrdinaryHeatCurrentBound μ t V₀ Vₜ hV₀ hVₜ hI₀ hIₜ hμ₀ hμₜ m mₜ L hm hmₜ hl₀ hu₀ hlₜ huₜ)
    (hsmall : (θ * Real.sqrt m) * Real.sqrt t ≤ 1/24)
    (hε : θ * Real.sqrt m ≤ 1) (hta : t ≤ a)
    (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    quadraticEnergy (visibleCorrector (heatedLaw μ t) Vₜ hVₜ hIₜ hμₜ mₜ L hmₜ hlₜ huₜ)
      (θ * Real.sqrt m) (collisionDensity μ t hp hq Γ hΓ f) ≤
    gaussianCorrectedEnergy μ V₀ hV₀ hI₀ hμ₀ m L hm hl₀ hu₀ (θ * Real.sqrt m) f -
      (Γ/32) * ‖f - gaussianPositionProjection μ f‖^2 +
      (8*θ^2*Γ + (C/2+200)*θ*Real.sqrt m*a) * ‖f‖^2 := by
  have hbase := collision_energy_le_of_ordinary_current μ t V₀ Vₜ hV₀ hVₜ hI₀ hIₜ hμ₀ hμₜ
    m mₜ L hm hmₜ hl₀ hu₀ hlₜ huₜ hp hq hpos ht Γ hΓ hΓ' θ hθ C a hW hcurrent hsmall f
  apply hbase.trans
  have hε0 : 0 ≤ θ * Real.sqrt m := mul_nonneg hθ (Real.sqrt_nonneg m)
  have hε2 : (θ * Real.sqrt m)^2 ≤ θ * Real.sqrt m := by nlinarith
  have hc : 100*((θ*Real.sqrt m)+(θ*Real.sqrt m)^2)*t ≤ 200*(θ*Real.sqrt m)*a := by
    calc
      _ ≤ 200*(θ*Real.sqrt m)*t := by nlinarith [mul_nonneg ht (sub_nonneg.mpr hε2)]
      _ ≤ _ := mul_le_mul_of_nonneg_left hta (by positivity)
  have hcoef : 8*θ^2*Γ + (C/2)*(θ*Real.sqrt m)*a +
      100*((θ*Real.sqrt m)+(θ*Real.sqrt m)^2)*t ≤
      8*θ^2*Γ + (C/2+200)*θ*Real.sqrt m*a := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖f‖)
  linarith

end AcceleratedLogConcave.Kinetic.ConditionalContraction
