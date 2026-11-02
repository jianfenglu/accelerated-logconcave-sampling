import AcceleratedLogConcave.Kinetic.Mixing.DiscretePhase
import AcceleratedLogConcave.Kinetic.Mixing.Clock
import AcceleratedLogConcave.Kinetic.Mixing.Survival

/-! Independent uniform-clock averaging of the constructed physical phase
step. Strong measurability is explicit until supplied by the measurable kernel
family; no dissipative or contraction estimate is included as family data. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace AcceleratedLogConcave.Kinetic
open Analysis.Poisson Reheating ConditionalContraction

/-- The clipping only defines the map off the support of the uniform clock. -/
def clockTime (r : ℝ) (hr : 0 < r) (x : ℝ) : Icc (0 : ℝ) r :=
  ⟨max 0 (min r x), le_max_left _ _, max_le hr.le (min_le_left _ _)⟩

theorem clockTime_continuous (r : ℝ) (hr : 0 < r) : Continuous (clockTime r hr) := by
  apply Continuous.subtype_mk
  exact continuous_const.max (continuous_const.min continuous_id)

theorem clockTime_eq (r : ℝ) (hr : 0 < r) (x : ℝ) (hx : x ∈ Icc 0 r) :
    (clockTime r hr x : ℝ) = x := by simp [clockTime, min_eq_right hx.2, max_eq_right hx.1]

/-- Actual uniform clock as a measure on the permitted interval. -/
def boundedClockLaw (r : ℝ) (hr : 0 < r) : Measure (Icc (0 : ℝ) r) :=
  (clockLaw r).map (clockTime r hr)

instance boundedClockLaw_probability (r : ℝ) (hr : 0 < r) :
    IsProbabilityMeasure (boundedClockLaw r hr) := by
  let : IsProbabilityMeasure (clockLaw r) := clockLaw_probability r hr
  exact (Measure.isProbabilityMeasure_map_iff
    (clockTime_continuous r hr).measurable.aemeasurable).mpr inferInstance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {r : ℝ} (hr : 0 < r) (F : ReferencePoissonFamily E 0 r)
  (ell s n : ℝ) (hsn : s^2+n^2=1)
  (κ : Icc (0 : ℝ) r → Kernel (GaussianPhase E) E)
  [∀ t, IsMarkovKernel (κ t)]
  (hκ : ∀ t, ConditionallyInvariant (stdGaussian E) (κ t))
  (τ : Icc (0 : ℝ) r → ℝ) (Γ : ℝ) (hΓ : 0 ≤ Γ)
  (hreturn : ∀ t : Icc (0 : ℝ) r, heatedLaw (F.law t) (τ t) = F.law 0)

/-- The actual independently clock-averaged test operator. -/
def discretePhaseOperator
    (hI : ∀ f, Integrable (fun t =>
      returningClockChannel F ell t s n hsn (κ t) (hκ t) (τ t) Γ hΓ (hreturn t) f)
      (boundedClockLaw r hr)) :
    Lp ℝ 2 ((F.law 0).prod (stdGaussian E)) →L[ℝ]
      Lp ℝ 2 ((F.law 0).prod (stdGaussian E)) :=
  clockAverage (boundedClockLaw r hr)
    (fun t => returningClockChannel F ell t s n hsn (κ t) (hκ t) (τ t) Γ hΓ (hreturn t))
    hI (fun t => returningClockChannel_norm_le F ell t s n hsn (κ t) (hκ t) (τ t) Γ hΓ (hreturn t))

variable (hI : ∀ f, Integrable (fun t =>
    returningClockChannel F ell t s n hsn (κ t) (hκ t) (τ t) Γ hΓ (hreturn t) f)
    (boundedClockLaw r hr))

theorem discretePhaseOperator_norm_le :
    ‖discretePhaseOperator hr F ell s n hsn κ hκ τ Γ hΓ hreturn hI‖ ≤ 1 :=
  clockAverage_norm_le _ _ _ _

/-- The density step is the ordinary Hilbert adjoint of the physical test step. -/
def discretePhaseDensity :=
  (discretePhaseOperator hr F ell s n hsn κ hκ τ Γ hΓ hreturn hI).adjoint

theorem discretePhaseOperator_one :
    discretePhaseOperator hr F ell s n hsn κ hκ τ Γ hΓ hreturn hI
      (oneL2 ((F.law 0).prod (stdGaussian E))) =
      oneL2 ((F.law 0).prod (stdGaussian E)) := by
  change (∫ t, returningClockChannel F ell t s n hsn (κ t) (hκ t) (τ t) Γ hΓ
    (hreturn t) (oneL2 ((F.law 0).prod (stdGaussian E))) ∂boundedClockLaw r hr) = _
  simp only [returningClockChannel_one, integral_const, probReal_univ, one_smul]

theorem discretePhaseDensity_mean (f : Lp ℝ 2 ((F.law 0).prod (stdGaussian E))) :
    mean ((F.law 0).prod (stdGaussian E))
      (discretePhaseDensity hr F ell s n hsn κ hκ τ Γ hΓ hreturn hI f) =
      mean ((F.law 0).prod (stdGaussian E)) f := by
  change inner ℝ (oneL2 _) ((discretePhaseOperator hr F ell s n hsn κ hκ τ Γ hΓ hreturn hI).adjoint f) = _
  rw [ContinuousLinearMap.adjoint_inner_right, discretePhaseOperator_one]
  rfl

theorem discretePhaseOperator_mean (f : Lp ℝ 2 ((F.law 0).prod (stdGaussian E))) :
    mean ((F.law 0).prod (stdGaussian E))
      (discretePhaseOperator hr F ell s n hsn κ hκ τ Γ hΓ hreturn hI f) =
      mean ((F.law 0).prod (stdGaussian E)) f :=
  clockAverage_invariant _ _ _ _ _
    (fun t => returningClockChannel_mean F ell t s n hsn (κ t) (hκ t) (τ t) Γ hΓ (hreturn t)) f

/-- Averaging the actual component density steps gives the same density operator. -/
theorem discretePhaseDensity_eq_average
    (hIa : ∀ f, Integrable (fun t =>
      (returningClockChannel F ell t s n hsn (κ t) (hκ t) (τ t) Γ hΓ (hreturn t)).adjoint f)
      (boundedClockLaw r hr)) :
    discretePhaseDensity hr F ell s n hsn κ hκ τ Γ hΓ hreturn hI =
      clockAverage (boundedClockLaw r hr)
        (fun t => (returningClockChannel F ell t s n hsn (κ t) (hκ t) (τ t) Γ hΓ (hreturn t)).adjoint)
        hIa (fun t => by
          rw [ContinuousLinearMap.adjoint.norm_map]
          exact returningClockChannel_norm_le F ell t s n hsn (κ t) (hκ t) (τ t) Γ hΓ (hreturn t)) :=
  clockAverage_adjoint _ _ _ _ hIa

end AcceleratedLogConcave.Kinetic
