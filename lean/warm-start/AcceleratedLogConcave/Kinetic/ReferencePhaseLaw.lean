import AcceleratedLogConcave.Kinetic.Mixing.ClockKernel
import AcceleratedLogConcave.Kinetic.ReferenceChannelLaw
import AcceleratedLogConcave.Kinetic.ReferenceChannelIteration
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.WithDensity

/-! The source reference phase transition as a genuine clock and random-tape
law. The jointly measurable dormant kernel is the one used by the existing
source channel; its initial-frame disintegration is `frameTape`. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
open Set MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.ReferencePhaseLaw
open AcceleratedLogConcave.Kinetic
open AcceleratedLogConcave.Kinetic.Reheating
open AcceleratedLogConcave.Kinetic.ConditionalContraction
open AcceleratedLogConcave.Analysis.Poisson

variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "Clock" => Icc (0:ℝ) (1/2)
local notation "Tape" => (((GaussianPhase E × E) × E) × E)

private instance sourceClockLaw_probability : IsProbabilityMeasure sourceClockLaw := by
  unfold sourceClockLaw
  infer_instance

variable {μ : Measure (EuclideanSpace ℝ ι)} [IsProbabilityMeasure μ] {A R : ℝ}
  (H : VarianceHeatFamily (ι := ι) μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
  (ell Γ : ℝ) (hΓ : 0 ≤ Γ)
  (K : Kernel (Clock × GaussianPhase (EuclideanSpace ℝ ι)) (EuclideanSpace ℝ ι))
  [IsMarkovKernel K]
  (hκ : ∀ t, ConditionallyInvariant (stdGaussian (EuclideanSpace ℝ ι))
    (clockSection K t))

/-- The actual split, coupled-flow, dormant, reheating and OU tape, with its
independent source clock. The base of `frameTape` is the initial phase law. -/
def jointTape : Measure (Clock × Tape) :=
  sourceClockLaw ⊗ₘ frameTape (clockTransportFamily H hA hR) ell (1/2) (Real.sqrt 3/2)
    source_split_coefficients K

instance jointTape_probability : IsProbabilityMeasure (jointTape H hA hR ell K) := by
  unfold jointTape
  infer_instance

/-- The visible input phase is the initial-phase coordinate of the frame tape. -/
def input (z : Clock × Tape) : E × E := z.2.1.1.1.1

/-- Move the initial-frame tape to the physical fixed-clock tape. -/
def toPhysicalTape (z : Clock × Tape) : Tape :=
  Prod.map (Prod.map (Prod.map
    (preCollisionMap (clockTransportFamily H hA hR) ell z.1 (1/2) (Real.sqrt 3/2)
      source_split_coefficients) id) id) id z.2


/-- The literal output of the source reference split-flow/collision/reheat/OU
step, evaluated on the same complete tape. -/
def output (z : Clock × Tape) : E × E :=
  fixedClockOutput (1/2) (Real.sqrt 3/2) source_split_coefficients
    (A*(z.1:ℝ)^2) Γ (toPhysicalTape H hA hR ell z)

theorem input_measurable : Measurable (input (ι := ι)) := by
  unfold input
  fun_prop

theorem toPhysicalTape_measurable :
    Measurable (toPhysicalTape (ι := ι) H hA hR ell) := by
  have hΦ := preCollisionMap_measurable_uncurry (clockTransportFamily H hA hR) ell
    (1/2) (Real.sqrt 3/2) source_split_coefficients
  unfold toPhysicalTape
  exact (((hΦ.comp (measurable_fst.prodMk
    (measurable_snd.fst.fst.fst))).prodMk (measurable_snd.fst.fst.snd)).prodMk
    (measurable_snd.fst.snd)).prodMk (measurable_snd.snd)

theorem output_measurable :
    Measurable (output (ι := ι) H hA hR ell Γ) := by
  have hτ : Measurable (fun z : Clock × Tape => A*(z.1:ℝ)^2) := by fun_prop
  have hmain := (fixedClockOutput_measurable_uncurry
    (1/2) (Real.sqrt 3/2) source_split_coefficients Γ).comp
      (hτ.prodMk (toPhysicalTape_measurable H hA hR ell))
  exact hmain

theorem input_eq_fixedClockInput (t : Clock) (z : Tape) :
    input (ι := ι) (t,z) =
      fixedClockInput (clockTransportFamily H hA hR) ell t (1/2)
        (Real.sqrt 3/2) source_split_coefficients
        (toPhysicalTape H hA hR ell (t,z)) := by
  simp [input, toPhysicalTape, fixedClockInput]

/-- At each clock value the initial-frame tape is exactly the physical tape
used by the source channel, pushed through the pre-collision flow. -/
theorem physicalTape_preserving (t : Clock) :
    MeasurePreserving (fun z : Tape => toPhysicalTape H hA hR ell (t,z))
      (frameTape (clockTransportFamily H hA hR) ell (1/2) (Real.sqrt 3/2)
        source_split_coefficients K t)
      (fixedClockTape (clockTransportFamily H hA hR) t (clockSection K t)) := by
  refine ⟨(toPhysicalTape_measurable H hA hR ell).comp
    (measurable_const.prodMk measurable_id), ?_⟩
  exact (fixedClockTape_eq_map (clockTransportFamily H hA hR) ell
    (1/2) (Real.sqrt 3/2) source_split_coefficients K t).symm

theorem input_preserving_fixed_clock (t : Clock) :
    MeasurePreserving (fun z : Tape => input (ι := ι) (t,z))
      (frameTape (clockTransportFamily H hA hR) ell (1/2) (Real.sqrt 3/2)
        source_split_coefficients K t)
      (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E)) := by
  have hp := (fixedClockInput_measurePreserving (clockTransportFamily H hA hR)
    ell t (1/2) (Real.sqrt 3/2) source_split_coefficients (clockSection K t)).comp
    (physicalTape_preserving H hA hR ell K t)
  convert hp using 1
  funext z
  exact input_eq_fixedClockInput H hA hR ell t z

include hκ hΓ in
theorem output_preserving_fixed_clock (t : Clock) :
    MeasurePreserving (fun z : Tape => output H hA hR ell Γ (t,z))
      (frameTape (clockTransportFamily H hA hR) ell (1/2) (Real.sqrt 3/2)
        source_split_coefficients K t)
      (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E)) := by
  have hq := (fixedClockOutput_measurePreserving (clockTransportFamily H hA hR)
    t (1/2) (Real.sqrt 3/2) source_split_coefficients (clockSection K t)
    (hκ t) (A*(t:ℝ)^2) Γ hΓ).comp
    (physicalTape_preserving H hA hR ell K t)
  rw [clockTransportFamily_heat_return H hA hR t t.property] at hq
  exact hq

private theorem compProd_preserving_of_fibers
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (ξ : Measure α) [IsProbabilityMeasure ξ]
    (κ : Kernel α β) [IsMarkovKernel κ]
    (ν : Measure γ) (f : α × β → γ) (hf : Measurable f)
    (h : ∀ a, MeasurePreserving (fun b => f (a,b)) (κ a) ν) :
    MeasurePreserving f (ξ ⊗ₘ κ) ν := by
  refine ⟨hf, ?_⟩
  ext S hS
  rw [Measure.map_apply hf hS, Measure.compProd_apply (hS.preimage hf)]
  have hpoint : ∀ a, κ a (Prod.mk a ⁻¹' (f ⁻¹' S)) = ν S := by
    intro a
    have he := (h a).map_eq
    have hs := congrArg (fun m : Measure γ => m S) he
    rwa [Measure.map_apply (h a).measurable hS] at hs
  simp_rw [hpoint]
  simp

theorem input_preserving :
    MeasurePreserving (input (ι := ι)) (jointTape H hA hR ell K)
      (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E)) := by
  exact compProd_preserving_of_fibers sourceClockLaw
    (frameTape (clockTransportFamily H hA hR) ell (1/2) (Real.sqrt 3/2)
      source_split_coefficients K)
    _ (input (ι := ι)) input_measurable
    (input_preserving_fixed_clock H hA hR ell K)

include hκ hΓ in
theorem output_preserving :
    MeasurePreserving (output H hA hR ell Γ) (jointTape H hA hR ell K)
      (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E)) := by
  exact compProd_preserving_of_fibers sourceClockLaw
    (frameTape (clockTransportFamily H hA hR) ell (1/2) (Real.sqrt 3/2)
      source_split_coefficients K)
    _ (output H hA hR ell Γ) (output_measurable H hA hR ell Γ)
    (output_preserving_fixed_clock H hA hR ell Γ hΓ K hκ)

include hκ hΓ in
/-- The already constructed source phase test operator, with clock
integrability discharged by the jointly measurable kernel. -/
def phaseOperator :
    Lp ℝ 2 (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E)) →L[ℝ]
      Lp ℝ 2 (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E)) :=
  sourcePhaseOperator H hA hR ell Γ hΓ (clockSection K) hκ
    (fun f => sourceClockChannel_integrable H hA hR ell Γ hΓ K hκ f)

include hκ hΓ in
/-- The density adjoint that appears in the source mixing theorems. -/
def phaseDensity :
    Lp ℝ 2 (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E)) →L[ℝ]
      Lp ℝ 2 (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E)) :=
  sourcePhaseDensity H hA hR ell Γ hΓ (clockSection K) hκ
    (fun f => sourceClockChannel_integrable H hA hR ell Γ hΓ K hκ f)

include hκ hΓ in
theorem joint_pairing
    (f g : Lp ℝ 2 (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E))) :
    (∫ z : Clock × Tape,
      f (input (ι := ι) z) * g (output H hA hR ell Γ z)
        ∂jointTape H hA hR ell K) =
    ∫ t : Clock, (∫ z : Tape,
      f (fixedClockInput (clockTransportFamily H hA hR) ell t (1/2)
        (Real.sqrt 3/2) source_split_coefficients z) *
      g (fixedClockOutput (1/2) (Real.sqrt 3/2) source_split_coefficients
        (A*(t:ℝ)^2) Γ z)
        ∂fixedClockTape (clockTransportFamily H hA hR) t (clockSection K t))
      ∂sourceClockLaw := by
  have hp := input_preserving H hA hR ell K
  have hq := output_preserving H hA hR ell Γ hΓ K hκ
  have hInt : Integrable (fun z : Clock × Tape =>
      f (input (ι := ι) z) * g (output H hA hR ell Γ z))
      (jointTape H hA hR ell K) :=
    ((Lp.memLp f).comp_measurePreserving hp).integrable_mul
      ((Lp.memLp g).comp_measurePreserving hq)
  rw [jointTape, Measure.integral_compProd hInt]
  apply integral_congr_ae
  filter_upwards [] with t
  have htp := input_preserving_fixed_clock H hA hR ell K t
  have htq := output_preserving_fixed_clock H hA hR ell Γ hΓ K hκ t
  have hphys := physicalTape_preserving H hA hR ell K t
  have hfixp := fixedClockInput_measurePreserving (clockTransportFamily H hA hR)
    ell t (1/2) (Real.sqrt 3/2) source_split_coefficients (clockSection K t)
  have hfixq : MeasurePreserving
      (fixedClockOutput (1/2) (Real.sqrt 3/2) source_split_coefficients
        (A*(t:ℝ)^2) Γ : Tape → E × E)
      (fixedClockTape (clockTransportFamily H hA hR) t (clockSection K t))
      (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E)) := by
    have hh := fixedClockOutput_measurePreserving (clockTransportFamily H hA hR)
      t (1/2) (Real.sqrt 3/2) source_split_coefficients (clockSection K t)
      (hκ t) (A*(t:ℝ)^2) Γ hΓ
    rwa [clockTransportFamily_heat_return H hA hR t t.property] at hh
  have htarget : Integrable (fun z : Tape =>
      f (fixedClockInput (clockTransportFamily H hA hR) ell t (1/2)
        (Real.sqrt 3/2) source_split_coefficients z) *
      g (fixedClockOutput (1/2) (Real.sqrt 3/2) source_split_coefficients
        (A*(t:ℝ)^2) Γ z))
      (fixedClockTape (clockTransportFamily H hA hR) t (clockSection K t)) :=
    ((Lp.memLp f).comp_measurePreserving hfixp).integrable_mul
      ((Lp.memLp g).comp_measurePreserving hfixq)
  rw [← hphys.map_eq,
    integral_map hphys.measurable.aemeasurable
      (by simpa only [hphys.map_eq] using htarget.aestronglyMeasurable)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [← input_eq_fixedClockInput H hA hR ell t z]
  rfl

include hκ hΓ in
/-- The existing source test operator is exactly the channel of the genuine
clock-tape coupling. No stochastic law identity is an assumption. -/
theorem phaseOperator_eq_referenceChannel :
    phaseOperator H hA hR ell Γ hΓ K hκ =
      referenceChannel (input_preserving H hA hR ell K)
        (output_preserving H hA hR ell Γ hΓ K hκ) := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℝ
  intro f
  change inner ℝ f
    (sourcePhaseOperator H hA hR ell Γ hΓ (clockSection K) hκ
      (fun u => sourceClockChannel_integrable H hA hR ell Γ hΓ K hκ u) g) =
    inner ℝ f
      (referenceChannel (input_preserving H hA hR ell K)
        (output_preserving H hA hR ell Γ hΓ K hκ) g)
  exact (sourcePhaseOperator_pairing H hA hR ell Γ hΓ (clockSection K) hκ
    (fun u => sourceClockChannel_integrable H hA hR ell Γ hΓ K hκ u) f g).trans
      ((joint_pairing H hA hR ell Γ hΓ K hκ f g).symm.trans
        (referenceChannel_pairing (input_preserving H hA hR ell K)
          (output_preserving H hA hR ell Γ hΓ K hκ) f g).symm)

include hκ hΓ in
/-- Hence the source density is the adjoint of that actual coupling channel. -/
theorem phaseDensity_eq_referenceChannel_adjoint :
    phaseDensity H hA hR ell Γ hΓ K hκ =
      (referenceChannel (input_preserving H hA hR ell K)
        (output_preserving H hA hR ell Γ hΓ K hκ)).adjoint := by
  simpa only [phaseDensity, sourcePhaseDensity, phaseOperator] using
    congrArg ContinuousLinearMap.adjoint
      (phaseOperator_eq_referenceChannel H hA hR ell Γ hΓ K hκ)

/-- A genuine Markov kernel obtained by disintegrating the *constructed*
complete source clock-tape law along its visible input phase. -/
def phaseKernel : Kernel (E × E) (E × E) :=
  condDistrib (output H hA hR ell Γ) (input (ι := ι))
    (jointTape H hA hR ell K)

instance phaseKernel_markov : IsMarkovKernel (phaseKernel H hA hR ell Γ K) := by
  unfold phaseKernel
  infer_instance

/-- The phase kernel has the actual input-output coupling as its disintegration;
the right side retains the literal tape and independent clock. -/
theorem phaseKernel_disintegration :
    (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E)) ⊗ₘ
      phaseKernel H hA hR ell Γ K =
      (jointTape H hA hR ell K).map
        (fun z => (input (ι := ι) z, output H hA hR ell Γ z)) := by
  rw [← (input_preserving H hA hR ell K).map_eq]
  exact compProd_map_condDistrib
    (input_measurable (ι := ι)).aemeasurable
    (output_measurable H hA hR ell Γ).aemeasurable

include hκ hΓ in
/-- The physical source reference law is stationary for this genuine kernel. -/
theorem phaseKernel_invariant :
    phaseKernel H hA hR ell Γ K ∘ₘ
      (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E)) =
      (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E)) := by
  calc
    _ = phaseKernel H hA hR ell Γ K ∘ₘ
        (jointTape H hA hR ell K).map (input (ι := ι)) := by
          rw [(input_preserving H hA hR ell K).map_eq]
    _ = (jointTape H hA hR ell K).map (output H hA hR ell Γ) := by
      exact condDistrib_comp_map
        (input_measurable (ι := ι)).aemeasurable
        (output_measurable H hA hR ell Γ).aemeasurable
    _ = _ := (output_preserving H hA hR ell Γ hΓ K hκ).map_eq

/-- Starting from any joint visible-phase law, reweight the complete reference
tape by its input RN density and read its literal output. -/
def warmOutput (ν : Measure (E × E)) : Measure (E × E) :=
  ReferenceChannelLaw.outputLaw ν (jointTape H hA hR ell K)
    (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E))
    (input (ι := ι)) (output H hA hR ell Γ)

include hκ hΓ in
theorem warmOutput_centered_rnDeriv
    {ν : Measure (E × E)} [IsProbabilityMeasure ν] {B : ℝ}
    (h : AcceleratedLogConcave.Probability.L2Warm
      (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E)) ν B) :
    (fun x => ((warmOutput H hA hR ell Γ K ν).rnDeriv
      (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E)) x).toReal-1) =ᵐ[
        (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E))]
      (phaseDensity H hA hR ell Γ hΓ K hκ
        (h.centeredDensity : Lp ℝ 2
          (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E))) : E × E → ℝ) := by
  have hp := input_preserving H hA hR ell K
  have hq := output_preserving H hA hR ell Γ hΓ K hκ
  have he := ReferenceChannelLaw.output_centered_rnDeriv hp hq h
  simpa only [warmOutput, ← phaseDensity_eq_referenceChannel_adjoint H hA hR ell Γ hΓ K hκ]
    using he

include hκ hΓ in
theorem warmOutput_totalVariation_le
    {ν : Measure (E × E)} [IsProbabilityMeasure ν] {B : ℝ}
    (h : AcceleratedLogConcave.Probability.L2Warm
      (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E)) ν B) :
    have : IsProbabilityMeasure (warmOutput H hA hR ell Γ K ν) :=
      ReferenceChannelLaw.outputLaw_probability
        (input_preserving H hA hR ell K)
        (output_preserving H hA hR ell Γ hΓ K hκ) h.absolutelyContinuous
    AcceleratedLogConcave.Probability.totalVariationDistance
      (warmOutput H hA hR ell Γ K ν)
      (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E)) ≤
      ‖phaseDensity H hA hR ell Γ hΓ K hκ
        (h.centeredDensity : Lp ℝ 2
          (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E)))‖/2 := by
  have he := ReferenceChannelLaw.output_totalVariation_le
    (input_preserving H hA hR ell K)
    (output_preserving H hA hR ell Γ hΓ K hκ) h
  simpa only [warmOutput, ← phaseDensity_eq_referenceChannel_adjoint H hA hR ell Γ hΓ K hκ]
    using he

private theorem map_withDensity_pullback
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (η : Measure α) (f : α → β) (hf : Measurable f)
    (w : β → ENNReal) (hw : Measurable w) :
    (η.withDensity (w ∘ f)).map f = (η.map f).withDensity w := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hs.preimage hf),
    withDensity_apply _ hs, setLIntegral_map hs hw hf]
  rfl

/-- The reweighted-tape output is exactly the action of the disintegrated
source phase kernel on every warm input law. This uses only equality of
measures, so the conditional kernel's arbitrary null-set version is harmless. -/
theorem warmOutput_eq_kernel
    {ν : Measure (E × E)} [IsProbabilityMeasure ν] {B : ℝ}
    (h : AcceleratedLogConcave.Probability.L2Warm
      (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E)) ν B) :
    warmOutput H hA hR ell Γ K ν =
      phaseKernel H hA hR ell Γ K ∘ₘ ν := by
  let μ₀ := ((clockTransportFamily H hA hR).law 0).prod (stdGaussian E)
  let η := jointTape H hA hR ell K
  let p := input (ι := ι)
  let q := output H hA hR ell Γ
  let φ : Clock × Tape → (E × E) × (E × E) := fun z => (p z, q z)
  let w : (E × E) × (E × E) → ENNReal := fun z => ν.rnDeriv μ₀ z.1
  have hφ : Measurable φ := (input_measurable (ι := ι)).prodMk
    (output_measurable H hA hR ell Γ)
  have hw : Measurable w := (Measure.measurable_rnDeriv ν μ₀).comp measurable_fst
  have hν : μ₀.withDensity (ν.rnDeriv μ₀) = ν :=
    Measure.withDensity_rnDeriv_eq ν μ₀ h.absolutelyContinuous
  calc
    warmOutput H hA hR ell Γ K ν = (η.withDensity (w ∘ φ)).map q := by rfl
    _ = ((η.map φ).withDensity w).map Prod.snd := by
      rw [← map_withDensity_pullback η φ hφ w hw]
      rw [Measure.map_map measurable_snd hφ]
      rfl
    _ = ((μ₀ ⊗ₘ phaseKernel H hA hR ell Γ K).withDensity w).map Prod.snd := by
      rw [phaseKernel_disintegration H hA hR ell Γ K]
    _ = ((μ₀.withDensity (ν.rnDeriv μ₀)) ⊗ₘ
      phaseKernel H hA hR ell Γ K).map Prod.snd := by
      rw [Measure.withDensity_compProd (Measure.measurable_rnDeriv ν μ₀)]
    _ = phaseKernel H hA hR ell Γ K ∘ₘ ν := by
      rw [hν]
      change (ν ⊗ₘ phaseKernel H hA hR ell Γ K).snd = _
      exact Measure.snd_compProd ν (phaseKernel H hA hR ell Γ K)

/-- The repeated source reference output law, formed by reweighting the same
genuine clock-tape coupling at every step. -/
def warmIterateLaw (ν : Measure (E × E)) (k : ℕ) : Measure (E × E) :=
  ReferenceChannelIteration.iterateLaw (jointTape H hA hR ell K)
    (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E))
    (input (ι := ι)) (output H hA hR ell Γ) ν k

include hκ hΓ in
theorem warmIterate_power
    {ν : Measure (E × E)} [IsProbabilityMeasure ν] {B : ℝ}
    (h : AcceleratedLogConcave.Probability.L2Warm
      (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E)) ν B)
    (k : ℕ) :
    have : IsProbabilityMeasure (warmIterateLaw H hA hR ell Γ K ν k) :=
      ReferenceChannelIteration.iterateLaw_probability
        (input_preserving H hA hR ell K)
        (output_preserving H hA hR ell Γ hΓ K hκ) h.absolutelyContinuous k
    ∃ hw : AcceleratedLogConcave.Probability.L2Warm
        (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E))
        (warmIterateLaw H hA hR ell Γ K ν k)
        (1+‖((phaseDensity H hA hR ell Γ hΓ K hκ)^k)
          (h.centeredDensity : Lp ℝ 2
            (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E)))‖^2),
      (hw.centeredDensity : Lp ℝ 2
        (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E))) =
        ((phaseDensity H hA hR ell Γ hΓ K hκ)^k)
          (h.centeredDensity : Lp ℝ 2
            (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E))) := by
  have hp := input_preserving H hA hR ell K
  have hq := output_preserving H hA hR ell Γ hΓ K hκ
  let : IsProbabilityMeasure (ReferenceChannelIteration.iterateLaw
      (jointTape H hA hR ell K)
      (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E))
      (input (ι := ι)) (output H hA hR ell Γ) ν k) :=
    ReferenceChannelIteration.iterateLaw_probability hp hq h.absolutelyContinuous k
  have hw := ReferenceChannelIteration.iterateLaw_warm hp hq h k
  have hae := ReferenceChannelIteration.iterateLaw_centered_rnDeriv hp hq h k
  rw [← phaseDensity_eq_referenceChannel_adjoint H hA hR ell Γ hΓ K hκ] at hw hae
  refine ⟨hw, ?_⟩
  apply Lp.ext
  filter_upwards [hw.centeredDensity_coe_ae, hae] with x hx hy
  exact hx.trans hy

include hκ hΓ in
theorem warmIterate_totalVariation_le
    {ν : Measure (E × E)} [IsProbabilityMeasure ν] {B : ℝ}
    (h : AcceleratedLogConcave.Probability.L2Warm
      (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E)) ν B)
    (k : ℕ) :
    have : IsProbabilityMeasure (warmIterateLaw H hA hR ell Γ K ν k) :=
      ReferenceChannelIteration.iterateLaw_probability
        (input_preserving H hA hR ell K)
        (output_preserving H hA hR ell Γ hΓ K hκ) h.absolutelyContinuous k
    AcceleratedLogConcave.Probability.totalVariationDistance
      (warmIterateLaw H hA hR ell Γ K ν k)
      (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E)) ≤
      ‖((phaseDensity H hA hR ell Γ hΓ K hκ)^k)
        (h.centeredDensity : Lp ℝ 2
          (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E)))‖/2 := by
  have hp := input_preserving H hA hR ell K
  have hq := output_preserving H hA hR ell Γ hΓ K hκ
  have ht := ReferenceChannelIteration.iterateLaw_totalVariation_le hp hq h k
  simpa only [warmIterateLaw,
    ← phaseDensity_eq_referenceChannel_adjoint H hA hR ell Γ hΓ K hκ] using ht

include hκ hΓ in
/-- Each recursively reweighted output measure is exactly a step of the
constructed Markov phase kernel, including after warm dependent inputs. -/
theorem warmIterate_succ_eq_kernel
    {ν : Measure (E × E)} [IsProbabilityMeasure ν] {B : ℝ}
    (h : AcceleratedLogConcave.Probability.L2Warm
      (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E)) ν B)
    (k : ℕ) :
    warmIterateLaw H hA hR ell Γ K ν (k+1) =
      phaseKernel H hA hR ell Γ K ∘ₘ warmIterateLaw H hA hR ell Γ K ν k := by
  have hp := input_preserving H hA hR ell K
  have hq := output_preserving H hA hR ell Γ hΓ K hκ
  let : IsProbabilityMeasure (ReferenceChannelIteration.iterateLaw
      (jointTape H hA hR ell K)
      (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E))
      (input (ι := ι)) (output H hA hR ell Γ) ν k) :=
    ReferenceChannelIteration.iterateLaw_probability hp hq h.absolutelyContinuous k
  let : IsProbabilityMeasure (warmIterateLaw H hA hR ell Γ K ν k) :=
    ReferenceChannelIteration.iterateLaw_probability hp hq h.absolutelyContinuous k
  have hw := ReferenceChannelIteration.iterateLaw_warm hp hq h k
  change warmOutput H hA hR ell Γ K
    (warmIterateLaw H hA hR ell Γ K ν k) = _
  exact warmOutput_eq_kernel H hA hR ell Γ K hw

/-- Repeated composition of the actual conditional phase kernel, starting at
an arbitrary phase law. -/
def kernelIterateLaw (ν : Measure (E × E)) : ℕ → Measure (E × E)
  | 0 => ν
  | k+1 => phaseKernel H hA hR ell Γ K ∘ₘ kernelIterateLaw ν k

include hκ hΓ in
/-- The recursively reweighted joint-tape law is precisely every iterate of
the genuine conditional phase kernel for an arbitrary joint warm input. -/
theorem warmIterate_eq_kernelIterate
    {ν : Measure (E × E)} [IsProbabilityMeasure ν] {B : ℝ}
    (h : AcceleratedLogConcave.Probability.L2Warm
      (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E)) ν B)
    (k : ℕ) :
    warmIterateLaw H hA hR ell Γ K ν k =
      kernelIterateLaw H hA hR ell Γ K ν k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [warmIterate_succ_eq_kernel H hA hR ell Γ hΓ K hκ h k, ih]
    rfl

private theorem centeredOperator_power_coe
    {X : Type*} [MeasurableSpace X] (ρ : Measure X) [IsProbabilityMeasure ρ]
    (T : Lp ℝ 2 ρ →L[ℝ] Lp ℝ 2 ρ)
    (hT : ∀ f, mean ρ (T f) = mean ρ f)
    (k : ℕ) (f : centered ρ) :
    (((centeredOperator ρ T hT)^k) f : Lp ℝ 2 ρ) =
      (T^k) (f : Lp ℝ 2 ρ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp]
    change T ((((centeredOperator ρ T hT)^k) f : centered ρ) : Lp ℝ 2 ρ) = _
    rw [ih, pow_succ', mul_apply_eq_comp]

include hκ hΓ in
/-- The ordinary full-density power on a mean-zero input is the same vector
as the source's original centered-density power. -/
theorem phaseDensity_power_centered (k : ℕ)
    (f : centered (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E))) :
    (((sourceCenteredPhaseDensity H hA hR ell Γ hΓ (clockSection K) hκ
      (fun u => sourceClockChannel_integrable H hA hR ell Γ hΓ K hκ u))^k) f :
          Lp ℝ 2 (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E))) =
      ((phaseDensity H hA hR ell Γ hΓ K hκ)^k)
        (f : Lp ℝ 2 (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E))) := by
  exact centeredOperator_power_coe _ _
    (fun g => sourcePhaseDensity_mean H hA hR ell Γ hΓ (clockSection K) hκ
      (fun u => sourceClockChannel_integrable H hA hR ell Γ hΓ K hκ u) g)
    k f

end AcceleratedLogConcave.Kinetic.ReferencePhaseLaw
