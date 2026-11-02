import AcceleratedLogConcave.Kinetic.Mixing.SourceContraction

/-! Reference invariance and exact tape pairing for the source-parameter phase
transition (split, coupled flow, conditional dormant update, rotation,
correlated reheating, momentum OU, independent uniform clock).

The input and output laws of the constructed random tape are the same reference
law `μ ⊗ γ`: this is the measure-preservation content of `fixedClockOutput` and
`fixedClockInput`, transported to the clock average. The statements below are
conclusions of that construction. They assume no contraction or mixing estimate
and no W12 dormant bound. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic
open Analysis.Poisson Reheating ConditionalContraction
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The independent uniform clock on `[0,1/2]` of the source transition. -/
def sourceClockLaw : Measure (Icc (0:ℝ) (1/2)) := boundedClockLaw (1/2) (by norm_num)

/-- Exact joint-tape pairing of one fixed-clock step: the test operator is the
conditional expectation along the constructed tape. -/
theorem sourceClockChannel_pairing
    {μ : Measure E} [IsProbabilityMeasure μ] {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ell Γ : ℝ) (hΓ : 0 ≤ Γ)
    (κ : Icc (0:ℝ) (1/2) → Kernel (GaussianPhase E) E)
    [∀ t, IsMarkovKernel (κ t)]
    (hκ : ∀ t, ConditionallyInvariant (stdGaussian E) (κ t))
    (t : Icc (0:ℝ) (1/2))
    (f g : Lp ℝ 2 (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E))) :
    inner ℝ f (sourceClockChannel H hA hR ell Γ hΓ κ hκ t g) =
      ∫ z : ((GaussianPhase E × E) × E) × E, f (fixedClockInput (clockTransportFamily H hA hR) ell t (1/2)
          (Real.sqrt 3/2) source_split_coefficients z) *
        g (fixedClockOutput (1/2) (Real.sqrt 3/2) source_split_coefficients
          (A*(t:ℝ)^2) Γ z) ∂fixedClockTape (clockTransportFamily H hA hR) t (κ t) :=
  referenceChannel_pairing _ _ f g

/-- Invariance of the reference law for a fixed clock: constants are fixed. -/
theorem sourceClockChannel_one
    {μ : Measure E} [IsProbabilityMeasure μ] {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ell Γ : ℝ) (hΓ : 0 ≤ Γ)
    (κ : Icc (0:ℝ) (1/2) → Kernel (GaussianPhase E) E)
    [∀ t, IsMarkovKernel (κ t)]
    (hκ : ∀ t, ConditionallyInvariant (stdGaussian E) (κ t))
    (t : Icc (0:ℝ) (1/2)) :
    sourceClockChannel H hA hR ell Γ hΓ κ hκ t (oneL2 (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E))) = oneL2 (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E)) :=
  returningClockChannel_one ..

theorem sourcePhaseOperator_norm_le
    {μ : Measure E} [IsProbabilityMeasure μ] {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ell Γ : ℝ) (hΓ : 0 ≤ Γ)
    (κ : Icc (0:ℝ) (1/2) → Kernel (GaussianPhase E) E)
    [∀ t, IsMarkovKernel (κ t)]
    (hκ : ∀ t, ConditionallyInvariant (stdGaussian E) (κ t))
    (hI : ∀ f, Integrable (fun t => sourceClockChannel H hA hR ell Γ hΓ κ hκ t f)
      (boundedClockLaw (1/2) (by norm_num)))
    :
    ‖sourcePhaseOperator H hA hR ell Γ hΓ κ hκ hI‖ ≤ 1 :=
  discretePhaseOperator_norm_le ..

/-- The clock-averaged transition preserves the reference law: it fixes `1`. -/
theorem sourcePhaseOperator_one
    {μ : Measure E} [IsProbabilityMeasure μ] {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ell Γ : ℝ) (hΓ : 0 ≤ Γ)
    (κ : Icc (0:ℝ) (1/2) → Kernel (GaussianPhase E) E)
    [∀ t, IsMarkovKernel (κ t)]
    (hκ : ∀ t, ConditionallyInvariant (stdGaussian E) (κ t))
    (hI : ∀ f, Integrable (fun t => sourceClockChannel H hA hR ell Γ hΓ κ hκ t f)
      (boundedClockLaw (1/2) (by norm_num)))
    :
    sourcePhaseOperator H hA hR ell Γ hΓ κ hκ hI (oneL2 (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E))) = oneL2 (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E)) :=
  discretePhaseOperator_one ..

theorem sourcePhaseOperator_mean
    {μ : Measure E} [IsProbabilityMeasure μ] {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ell Γ : ℝ) (hΓ : 0 ≤ Γ)
    (κ : Icc (0:ℝ) (1/2) → Kernel (GaussianPhase E) E)
    [∀ t, IsMarkovKernel (κ t)]
    (hκ : ∀ t, ConditionallyInvariant (stdGaussian E) (κ t))
    (hI : ∀ f, Integrable (fun t => sourceClockChannel H hA hR ell Γ hΓ κ hκ t f)
      (boundedClockLaw (1/2) (by norm_num)))
    (f : Lp ℝ 2 (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E))) :
    mean (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E)) (sourcePhaseOperator H hA hR ell Γ hΓ κ hκ hI f) = mean (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E)) f :=
  discretePhaseOperator_mean (f := f) ..

/-- The density transition preserves total mass. -/
theorem sourcePhaseDensity_mean
    {μ : Measure E} [IsProbabilityMeasure μ] {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ell Γ : ℝ) (hΓ : 0 ≤ Γ)
    (κ : Icc (0:ℝ) (1/2) → Kernel (GaussianPhase E) E)
    [∀ t, IsMarkovKernel (κ t)]
    (hκ : ∀ t, ConditionallyInvariant (stdGaussian E) (κ t))
    (hI : ∀ f, Integrable (fun t => sourceClockChannel H hA hR ell Γ hΓ κ hκ t f)
      (boundedClockLaw (1/2) (by norm_num)))
    (f : Lp ℝ 2 (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E))) :
    mean (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E)) (sourcePhaseDensity H hA hR ell Γ hΓ κ hκ hI f) = mean (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E)) f :=
  discretePhaseDensity_mean (f := f) ..

/-- The clock-averaged test operator is the expectation, over the independent
uniform clock, of the tape pairings of the fixed-clock steps. -/
theorem sourcePhaseOperator_pairing
    {μ : Measure E} [IsProbabilityMeasure μ] {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ell Γ : ℝ) (hΓ : 0 ≤ Γ)
    (κ : Icc (0:ℝ) (1/2) → Kernel (GaussianPhase E) E)
    [∀ t, IsMarkovKernel (κ t)]
    (hκ : ∀ t, ConditionallyInvariant (stdGaussian E) (κ t))
    (hI : ∀ f, Integrable (fun t => sourceClockChannel H hA hR ell Γ hΓ κ hκ t f)
      (boundedClockLaw (1/2) (by norm_num)))
    (f g : Lp ℝ 2 (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E))) :
    inner ℝ f (sourcePhaseOperator H hA hR ell Γ hΓ κ hκ hI g) =
      ∫ t : Icc (0:ℝ) (1/2), (∫ z : ((GaussianPhase E × E) × E) × E, f (fixedClockInput (clockTransportFamily H hA hR) ell t (1/2)
          (Real.sqrt 3/2) source_split_coefficients z) *
        g (fixedClockOutput (1/2) (Real.sqrt 3/2) source_split_coefficients
          (A*(t:ℝ)^2) Γ z) ∂fixedClockTape (clockTransportFamily H hA hR) t (κ t))
        ∂sourceClockLaw := by
  unfold sourcePhaseOperator discretePhaseOperator
  rw [clockAverage_pairing]
  exact integral_congr_ae (Filter.Eventually.of_forall fun t =>
    sourceClockChannel_pairing H hA hR ell Γ hΓ κ hκ t f g)

/-- Law interpretation of the density step: started from relative density `f`, the
output has relative density `P* f`, tested against any `g` through the tape. -/
theorem sourcePhaseDensity_pairing
    {μ : Measure E} [IsProbabilityMeasure μ] {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ell Γ : ℝ) (hΓ : 0 ≤ Γ)
    (κ : Icc (0:ℝ) (1/2) → Kernel (GaussianPhase E) E)
    [∀ t, IsMarkovKernel (κ t)]
    (hκ : ∀ t, ConditionallyInvariant (stdGaussian E) (κ t))
    (hI : ∀ f, Integrable (fun t => sourceClockChannel H hA hR ell Γ hΓ κ hκ t f)
      (boundedClockLaw (1/2) (by norm_num)))
    (f g : Lp ℝ 2 (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E))) :
    inner ℝ (sourcePhaseDensity H hA hR ell Γ hΓ κ hκ hI f) g =
      ∫ t : Icc (0:ℝ) (1/2), (∫ z : ((GaussianPhase E × E) × E) × E, f (fixedClockInput (clockTransportFamily H hA hR) ell t (1/2)
          (Real.sqrt 3/2) source_split_coefficients z) *
        g (fixedClockOutput (1/2) (Real.sqrt 3/2) source_split_coefficients
          (A*(t:ℝ)^2) Γ z) ∂fixedClockTape (clockTransportFamily H hA hR) t (κ t))
        ∂sourceClockLaw := by
  rw [sourcePhaseDensity, ContinuousLinearMap.adjoint_inner_left]
  exact sourcePhaseOperator_pairing H hA hR ell Γ hΓ κ hκ hI f g

end AcceleratedLogConcave.Kinetic
