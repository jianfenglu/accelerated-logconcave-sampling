import AcceleratedLogConcave.Kinetic.Mixing.Constants
import AcceleratedLogConcave.Kinetic.Mixing.DiscreteAverage
import AcceleratedLogConcave.Kinetic.Mixing.Factorization
import AcceleratedLogConcave.Kinetic.ConditionalContraction.Collision
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Clock integration of the transport and collision estimates. The integrated
transport budget is an explicit intermediate hypothesis, to be supplied by the
actual transported energy curve. No clock contraction is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace AcceleratedLogConcave.Kinetic

/-- Integrated transport budget. `R` is microscopic squared norm and `κ` is
`ε * ell`. This formulation only needs continuity at the initial endpoint. -/
def ScalarTransportEnergyBudget (r Ein N κ : ℝ) (E R : ℝ → ℝ) : Prop :=
  ∀ t ∈ Ico 0 r, E t ≤ Ein - κ * N * t / 8 + 3 * κ * ∫ s in 0..t, R s

/-- Positivity of microscopic energy bounds each partial accumulated error by
the full accumulated error. No comparison with the initial microscopic norm
is needed. -/
theorem scalarTransportEnergyBudget_uniform (r Ein N κ : ℝ) (hκ : 0 ≤ κ)
    (E R : ℝ → ℝ) (hR : ∀ t ∈ Icc 0 r, 0 ≤ R t)
    (hRI : IntervalIntegrable R volume 0 r)
    (hbudget : ScalarTransportEnergyBudget r Ein N κ E R)
    (t : ℝ) (ht : t ∈ Ico 0 r) :
    E t ≤ Ein - κ * N * t / 8 + 3 * κ * ∫ s in 0..r, R s := by
  apply (hbudget t ht).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2.le _ hRI
  exact (ae_restrict_mem measurableSet_Ioc).mono fun s hs => hR s ⟨hs.1.le, hs.2⟩

/-- The actual normalized uniform clock gives the source survival estimate.
The sharper survival weight is bounded by `r`, precisely as in the source. -/
theorem scalarTransportEnergyBudget_average (r Ein N κ : ℝ) (hr : 0 < r)
    (hκ : 0 ≤ κ) (E R : ℝ → ℝ)
    (hEI : IntervalIntegrable E volume 0 r)
    (hRI : IntervalIntegrable R volume 0 r)
    (hR : ∀ t ∈ Icc 0 r, 0 ≤ R t)
    (hbudget : ScalarTransportEnergyBudget r Ein N κ E R) :
    r⁻¹ * (∫ t in 0..r, E t) ≤
      Ein - κ * N * r / 16 + 3 * κ * r * (r⁻¹ * ∫ t in 0..r, R t) := by
  have htime : IntervalIntegrable (fun t : ℝ => κ * N * t / 8) volume 0 r :=
    (by fun_prop : Continuous (fun t : ℝ => κ * N * t / 8)).intervalIntegrable _ _
  have hlinear : IntervalIntegrable (fun t : ℝ => Ein - κ * N * t / 8)
      volume 0 r := (continuous_const.sub (continuous_const.mul continuous_id |>.div_const 8)).intervalIntegrable _ _
  have hi := intervalIntegral.integral_mono_on_of_le_Ioo hr.le hEI
    (hlinear.add intervalIntegrable_const)
    (fun t ht => scalarTransportEnergyBudget_uniform r Ein N κ hκ E R hR hRI hbudget t ⟨ht.1.le, ht.2⟩)
  have hid : (∫ t in 0..r, (Ein - κ * N * t / 8 +
      3 * κ * ∫ s in 0..r, R s)) =
      r * Ein - κ * N * r ^ 2 / 16 + r * (3 * κ * ∫ s in 0..r, R s) := by
    rw [intervalIntegral.integral_add hlinear intervalIntegrable_const,
      intervalIntegral.integral_sub intervalIntegrable_const
        htime,
      intervalIntegral.integral_div, intervalIntegral.integral_const_mul]
    simp only [intervalIntegral.integral_const, integral_id, sub_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), smul_eq_mul]
    ring
  rw [hid] at hi
  have hi' := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hr.le)
  convert hi' using 1; field_simp

/-- Average collision after transport, with the source constants left visible. -/
theorem scalar_transport_collision_clock (r Ein N κ Γ err : ℝ) (hr : 0 < r)
    (hκ : 0 ≤ κ) (E R G : ℝ → ℝ)
    (hEI : IntervalIntegrable E volume 0 r)
    (hRI : IntervalIntegrable R volume 0 r)
    (hGI : IntervalIntegrable G volume 0 r)
    (hR : ∀ t ∈ Icc 0 r, 0 ≤ R t)
    (hbudget : ScalarTransportEnergyBudget r Ein N κ E R)
    (hcollision : ∀ t ∈ Ico 0 r, G t ≤ E t - Γ * R t / 32 + err * N) :
    r⁻¹ * (∫ t in 0..r, G t) ≤ Ein - κ * N * r / 16 +
      (3 * κ * r - Γ / 32) * (r⁻¹ * ∫ t in 0..r, R t) + err * N := by
  have hi := intervalIntegral.integral_mono_on_of_le_Ioo hr.le hGI
    ((hEI.sub ((hRI.const_mul Γ).div_const 32)).add intervalIntegrable_const) (fun t ht => hcollision t ⟨ht.1.le, ht.2⟩)
  rw [intervalIntegral.integral_add (hEI.sub ((hRI.const_mul Γ).div_const 32))
      intervalIntegrable_const,
    intervalIntegral.integral_sub hEI ((hRI.const_mul Γ).div_const 32),
    intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at hi
  simp only [sub_zero, smul_eq_mul] at hi
  have hi' := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hr.le)
  have hb := scalarTransportEnergyBudget_average r Ein N κ hr hκ E R hEI hRI hR hbudget
  have hr0 : r ≠ 0 := ne_of_gt hr
  have heq : r⁻¹ * ((∫ t in 0..r, E t) - (Γ * ∫ t in 0..r, R t) / 32 +
      r * (err * N)) = r⁻¹ * (∫ t in 0..r, E t) -
        Γ / 32 * (r⁻¹ * ∫ t in 0..r, R t) + err * N := by
    field_simp
  rw [heq] at hi'
  linarith

/-- The bounded clock is exactly the normalized interval integral, including
for merely strongly measurable, integrable density families. -/
theorem boundedClockLaw_integral {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (r : ℝ) (hr : 0 < r) (f : Icc (0 : ℝ) r → H)
    (hf : AEStronglyMeasurable f (boundedClockLaw r hr)) :
    (∫ t, f t ∂boundedClockLaw r hr) = r⁻¹ • ∫ t in 0..r, f (clockTime r hr t) := by
  rw [boundedClockLaw, integral_map (clockTime_continuous r hr).measurable.aemeasurable hf,
    clockLaw_integral r hr]

/-- Strong integrability on the bounded clock supplies ordinary interval
integrability of the clipped representative. -/
theorem boundedClockLaw_intervalIntegrable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (r : ℝ) (hr : 0 < r) (f : Icc (0 : ℝ) r → H)
    (hf : Integrable f (boundedClockLaw r hr)) :
    IntervalIntegrable (fun t => f (clockTime r hr t)) volume 0 r := by
  have hi := hf.comp_measurable (clockTime_continuous r hr).measurable
  change Integrable (fun t => f (clockTime r hr t))
    ((ENNReal.ofReal r)⁻¹ • volume.restrict (Ioc 0 r)) at hi
  have hi' := (integrable_smul_measure
    (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
    (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hr)))).mp hi
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hr.le).mpr hi'

/-- Explicit source parameters absorb the averaged microscopic error and give
multiplicative contraction. `hJensen` is the scalar Jensen conclusion, supplied
below for the actual clock-averaged density. -/
theorem scalar_transport_collision_contraction
    (r Ein Eout N Γ θ C₂ h : ℝ) (hr : 0 < r)
    (hΓ : 0 ≤ Γ) (hθ : 0 ≤ θ) (hC : 0 < C₂) (hN : 0 ≤ N)
    (hEin : Ein ≤ N)
    (hθr : θ ≤ (192 * Real.sqrt 2 * r)⁻¹)
    (hθc : θ ≤ (Real.sqrt 2 * r / 16) / 32)
    (hh : h ≤ (Real.sqrt 2 * r / 16) / (8 * C₂))
    (E R G : ℝ → ℝ)
    (hEI : IntervalIntegrable E volume 0 r)
    (hRI : IntervalIntegrable R volume 0 r)
    (hGI : IntervalIntegrable G volume 0 r)
    (hR : ∀ t ∈ Icc 0 r, 0 ≤ R t)
    (hbudget : ScalarTransportEnergyBudget r Ein N (Real.sqrt 2 * θ * Γ) E R)
    (hcollision : ∀ t ∈ Ico 0 r,
      G t ≤ E t - Γ * R t / 32 + (8 * θ^2 * Γ + 2 * C₂ * θ * h * Γ) * N)
    (hJensen : Eout ≤ r⁻¹ * ∫ t in 0..r, G t) :
    Eout ≤ (1 + ((Real.sqrt 2 * r / 16) * θ / 2) * Γ)⁻¹ * Ein := by
  have hav := scalar_transport_collision_clock r Ein N (Real.sqrt 2 * θ * Γ) Γ
    (8 * θ^2 * Γ + 2 * C₂ * θ * h * Γ) hr (by positivity)
    E R G hEI hRI hGI hR hbudget hcollision
  have hstep : Eout ≤ Ein + Γ * (3 * Real.sqrt 2 * θ * r - 1 / 32) *
      (r⁻¹ * ∫ t in 0..r, R t) - θ * Γ *
        (Real.sqrt 2 * r / 16 - 8 * θ - 2 * C₂ * h) * N := by
    convert hJensen.trans hav using 1; ring
  have hRbar : 0 ≤ r⁻¹ * ∫ t in 0..r, R t :=
    mul_nonneg (inv_nonneg.mpr hr.le) (intervalIntegral.integral_nonneg hr.le hR)
  obtain ⟨hmicro, hscalar⟩ := clock_error_absorption θ h C₂
    (Real.sqrt 2 * r / 16) r hC hr hθr hθc hh
  exact contraction_of_clock_estimate Eout Ein N (r⁻¹ * ∫ t in 0..r, R t)
    Γ θ (Real.sqrt 2 * r / 16) C₂ h r hΓ hθ (by positivity) hN hRbar hEin
    hmicro hscalar hstep

section StrongMeasurability
variable {H Ω : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

/-- Contractivity supplies Bochner integrability once strong measurability is
known; norm measurability of the operator family is not required. -/
theorem integrable_contraction_family (T : Ω → H →L[ℝ] H)
    (hT : ∀ t, ‖T t‖ ≤ 1) (f : H)
    (hf : AEStronglyMeasurable (fun t => T t f) μ) :
    Integrable (fun t => T t f) μ := by
  apply (integrable_const ‖f‖).mono' hf
  exact Filter.Eventually.of_forall fun t =>
    ((T t).le_opNorm f).trans (by nlinarith [norm_nonneg f, hT t])

end StrongMeasurability

section EnergyIntegrability
variable {H Ω : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

/-- The source energy bounds and contraction make endpoint energy integrable
under only strong measurability on the fixed input. -/
theorem integrable_contraction_energy (T : Ω → H →L[ℝ] H)
    (hT : ∀ t, ‖T t‖ ≤ 1) (A : H →L[ℝ] H) (ε : ℝ)
    (hpos : ∀ g, 0 ≤ quadraticEnergy A ε g)
    (hupper : ∀ g, quadraticEnergy A ε g ≤ ‖g‖^2) (f : H)
    (hf : AEStronglyMeasurable (fun t => T t f) μ) :
    Integrable (fun t => quadraticEnergy A ε (T t f)) μ := by
  apply (integrable_const (‖f‖^2)).mono'
    ((quadraticEnergy_continuous A ε).comp_aestronglyMeasurable hf)
  apply Filter.Eventually.of_forall
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (hpos _)]
  apply (hupper _).trans
  have hn := ((T t).le_opNorm f).trans
    (show ‖T t‖ * ‖f‖ ≤ ‖f‖ by nlinarith [norm_nonneg f, hT t])
  exact pow_le_pow_left₀ (norm_nonneg _) hn 2

end EnergyIntegrability

section ActualDensity
open Analysis.Poisson Reheating ConditionalContraction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {r : ℝ} (hr : 0 < r) (F : ReferencePoissonFamily E 0 r)
  (ell s n : ℝ) (hsn : s^2+n^2=1)
  (κ : Icc (0 : ℝ) r → Kernel (GaussianPhase E) E)
  [∀ t, IsMarkovKernel (κ t)]
  (hκ : ∀ t, ConditionallyInvariant (stdGaussian E) (κ t))
  (τ : Icc (0 : ℝ) r → ℝ) (Γ : ℝ) (hΓ : 0 ≤ Γ)
  (hreturn : ∀ t : Icc (0 : ℝ) r, heatedLaw (F.law t) (τ t) = F.law 0)
  (hI : ∀ f, Integrable (fun t =>
    returningClockChannel F ell t s n hsn (κ t) (hκ t) (τ t) Γ hΓ (hreturn t) f)
    (boundedClockLaw r hr))
  (hIa : ∀ f, Integrable (fun t =>
    (returningClockChannel F ell t s n hsn (κ t) (hκ t) (τ t) Γ hΓ (hreturn t)).adjoint f)
    (boundedClockLaw r hr))
  (A : Lp ℝ 2 ((F.law 0).prod (stdGaussian E)) →L[ℝ]
    Lp ℝ 2 ((F.law 0).prod (stdGaussian E))) (ε : ℝ)
  (hpos : ∀ g, 0 ≤ quadraticEnergy A ε g)
  (hupper : ∀ g, quadraticEnergy A ε g ≤ ‖g‖^2)

include hIa hpos hupper

/-- Jensen for the literal independently clock-averaged density channel, with
all endpoint integrability deduced from contraction and source energy bounds. -/
theorem discretePhaseDensity_energy_le
    (f : Lp ℝ 2 ((F.law 0).prod (stdGaussian E))) :
    quadraticEnergy A ε (discretePhaseDensity hr F ell s n hsn κ hκ τ Γ hΓ hreturn hI f) ≤
      r⁻¹ * ∫ t in 0..r, quadraticEnergy A ε
        ((returningClockChannel F ell (clockTime r hr t) s n hsn
          (κ (clockTime r hr t)) (hκ (clockTime r hr t)) (τ (clockTime r hr t))
          Γ hΓ (hreturn (clockTime r hr t))).adjoint f) := by
  let T := fun t : Icc (0 : ℝ) r =>
    (returningClockChannel F ell t s n hsn (κ t) (hκ t) (τ t) Γ hΓ (hreturn t)).adjoint
  have hT (t) : ‖T t‖ ≤ 1 := by
    dsimp only [T]
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact returningClockChannel_norm_le F ell t s n hsn (κ t) (hκ t) (τ t) Γ hΓ (hreturn t)
  have hEI := integrable_contraction_energy (boundedClockLaw r hr) T hT A ε hpos hupper f
    (hIa f).aestronglyMeasurable
  rw [discretePhaseDensity_eq_average hr F ell s n hsn κ hκ τ Γ hΓ hreturn hI hIa]
  have hj := clockAverage_energy_le (boundedClockLaw r hr) T hIa hT A ε hpos f hEI
  rw [boundedClockLaw_integral r hr _ hEI.aestronglyMeasurable] at hj
  exact hj

/-- Actual clock density contraction from the proved collision budget and the
explicit integrated transport budget. In applications `A` is the visible
Gaussian corrector; its energy bounds are proved below. -/
theorem discretePhaseDensity_transport_clock_contraction
    (f : Lp ℝ 2 ((F.law 0).prod (stdGaussian E)))
    (θ C₂ h : ℝ) (hθ : 0 ≤ θ) (hC : 0 < C₂)
    (hθr : θ ≤ (192 * Real.sqrt 2 * r)⁻¹)
    (hθc : θ ≤ (Real.sqrt 2 * r / 16) / 32)
    (hh : h ≤ (Real.sqrt 2 * r / 16) / (8 * C₂))
    (Etr R : ℝ → ℝ)
    (hEI : IntervalIntegrable Etr volume 0 r)
    (hRI : IntervalIntegrable R volume 0 r)
    (hR : ∀ t ∈ Icc 0 r, 0 ≤ R t)
    (hbudget : ScalarTransportEnergyBudget r (quadraticEnergy A ε f) (‖f‖^2)
      (Real.sqrt 2 * θ * Γ) Etr R)
    (hcollision : ∀ t ∈ Ico 0 r,
      quadraticEnergy A ε
        ((returningClockChannel F ell (clockTime r hr t) s n hsn
          (κ (clockTime r hr t)) (hκ (clockTime r hr t)) (τ (clockTime r hr t))
          Γ hΓ (hreturn (clockTime r hr t))).adjoint f) ≤
        Etr t - Γ * R t / 32 + (8 * θ^2 * Γ + 2 * C₂ * θ * h * Γ) * ‖f‖^2) :
    quadraticEnergy A ε (discretePhaseDensity hr F ell s n hsn κ hκ τ Γ hΓ hreturn hI f) ≤
      (1 + ((Real.sqrt 2 * r / 16) * θ / 2) * Γ)⁻¹ * quadraticEnergy A ε f := by
  let T := fun t : Icc (0 : ℝ) r =>
    (returningClockChannel F ell t s n hsn (κ t) (hκ t) (τ t) Γ hΓ (hreturn t)).adjoint
  have hT (t) : ‖T t‖ ≤ 1 := by
    dsimp only [T]
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact returningClockChannel_norm_le F ell t s n hsn (κ t) (hκ t) (τ t) Γ hΓ (hreturn t)
  have hGI := boundedClockLaw_intervalIntegrable r hr _
    (integrable_contraction_energy (boundedClockLaw r hr) T hT A ε hpos hupper f
      (hIa f).aestronglyMeasurable)
  exact scalar_transport_collision_contraction r (quadraticEnergy A ε f) _ (‖f‖^2)
    Γ θ C₂ h hr hΓ hθ hC (sq_nonneg _) (hupper f) hθr hθc hh Etr R _
    hEI hRI hGI hR hbudget hcollision
    (discretePhaseDensity_energy_le hr F ell s n hsn κ hκ τ Γ hΓ hreturn hI hIa A ε hpos hupper f)

end ActualDensity

section VisibleEnergy
open Reheating
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsProbabilityMeasure μ]
  (V : E → ℝ) (hV : ContDiff ℝ 2 V) (hI : Integrable (fun x => Real.exp (-V x)))
  (hμ : μ = volume.tilted (fun x => -V x))
  (m L : ℝ) (hm : 0 < m)
  (hlower : ∀ x a, m * ‖a‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x a a)
  (hupper : ∀ x a, fderiv ℝ (fderiv ℝ V) x a a ≤ L * ‖a‖ ^ 2)

/-- The visible energy is the actual full Gaussian energy of its hidden lift. -/
theorem visibleCorrector_energy_eq (ε : ℝ) (f : Lp ℝ 2 (μ.prod (stdGaussian E))) :
    quadraticEnergy (visibleCorrector μ V hV hI hμ m L hm hlower hupper) ε f =
      gaussianCorrectedEnergy μ V hV hI hμ m L hm hlower hupper ε
        (Kinetic.hiddenEmbedding μ f) := by
  unfold quadraticEnergy gaussianCorrectedEnergy
  rw [visibleCorrector_inner, (Kinetic.hiddenEmbedding μ).norm_map]

/-- The energy bounds used by Jensen are the proved W04 bounds for the actual
visible corrector, rather than extra assumptions on the chosen channel. -/
theorem visibleCorrector_energy_bounds_quarter (θ : ℝ) (hθ : 0 ≤ θ) (hθq : θ ≤ 1 / 4)
    (f : Lp ℝ 2 (μ.prod (stdGaussian E))) :
    (3/8 : ℝ) * ‖f‖^2 ≤
      quadraticEnergy (visibleCorrector μ V hV hI hμ m L hm hlower hupper) (θ * Real.sqrt m) f ∧
    quadraticEnergy (visibleCorrector μ V hV hI hμ m L hm hlower hupper) (θ * Real.sqrt m) f ≤
      (5/8 : ℝ) * ‖f‖^2 := by
  rw [visibleCorrector_energy_eq]
  simpa only [(Kinetic.hiddenEmbedding μ).norm_map] using
    gaussianCorrectedEnergy_bounds_quarter μ V hV hI hμ m L hm hlower hupper θ hθ hθq
      (Kinetic.hiddenEmbedding μ f)

end VisibleEnergy

end AcceleratedLogConcave.Kinetic
