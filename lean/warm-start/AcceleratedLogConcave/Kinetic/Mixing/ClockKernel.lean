import AcceleratedLogConcave.Kinetic.Mixing.SourceInvariance
import AcceleratedLogConcave.Kinetic.Mixing.WeakMeasurable

/-! Joint measurability of the clock-indexed dormant kernel and the resulting
strong measurability of the fixed-clock channels in the clock time. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic
open Analysis.Poisson Reheating ConditionalContraction

section Flow
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {a b : ℝ} (F : ReferencePoissonFamily E a b) (ell : ℝ)

/-- For each initial point the coupled trajectory is continuous in time. -/
theorem referenceCoupledTrajectory_continuous (z : E × E) :
    Continuous (referenceCoupledTrajectory F ell z) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E E).continuous.comp
    (OAI.LogConcaveSampling.GlobalODE.flow_continuous _ _ _ _)

/-- The coupled flow is jointly measurable in time and initial point. -/
theorem referenceCoupledPairFlow_measurable_uncurry :
    Measurable (fun p : Icc a b × (E × E) => referenceCoupledPairFlow F ell p.1 p.2) := by
  refine measurable_uncurry_of_continuous_of_measurable
    (u := fun (t : Icc a b) (z : E × E) => referenceCoupledPairFlow F ell t z) ?_
    (fun t => (referenceCoupledPairFlow F ell t).measurable)
  intro z
  exact (referenceCoupledTrajectory_continuous F ell z).comp continuous_subtype_val

/-- The dormant coordinate is untouched, so the extended flow is jointly measurable. -/
theorem referenceExtendedFlow_measurable_uncurry :
    Measurable (fun p : Icc a b × GaussianPhase E => referenceExtendedFlow F ell p.1 p.2) :=
  ((referenceCoupledPairFlow_measurable_uncurry F ell).comp
    (measurable_fst.prodMk (measurable_snd.fst))).prodMk (measurable_snd.snd)

variable (s n : ℝ) (hsn : s^2+n^2=1)

/-- The initial split followed by the flow, jointly in clock time and phase point. -/
theorem preCollisionMap_measurable_uncurry :
    Measurable (fun p : Icc a b × GaussianPhase E => preCollisionMap F ell p.1 s n hsn p.2) :=
  (referenceExtendedFlow_measurable_uncurry F ell).comp
    (measurable_fst.prodMk ((phaseSplit (E := E) s n hsn).measurable.comp measurable_snd))

end Flow

section Compose
variable {α α' β : Type*} [MeasurableSpace α] [MeasurableSpace α'] [MeasurableSpace β]

/-- Pushing the base of a composition product through a measurable map. -/
theorem compProd_map_comap (μ : Measure α) [SFinite μ] (e : α → α') (he : Measurable e)
    (κ : Kernel α' β) [IsSFiniteKernel κ] :
    (μ.map e) ⊗ₘ κ = (μ ⊗ₘ κ.comap e he).map (Prod.map e id) := by
  ext S hS
  rw [Measure.map_apply (he.prodMap measurable_id) hS, Measure.compProd_apply hS,
    Measure.compProd_apply ((he.prodMap measurable_id) hS),
    lintegral_map (Kernel.measurable_kernel_prodMk_left hS) he]
  rfl

end Compose

section Tape
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {a b : ℝ}

/-- The dormant kernel read in the initial-time frame: it is evaluated at the
flowed point `preCollisionMap t w`. -/
def frameKernel (F : ReferencePoissonFamily E a b) (ell s n : ℝ) (hsn : s^2+n^2=1)
    (K : Kernel (Icc a b × GaussianPhase E) E) [IsMarkovKernel K] :
    Kernel (Icc a b × GaussianPhase E) E :=
  K.comap (fun p => (p.1, preCollisionMap F ell p.1 s n hsn p.2))
    (measurable_fst.prodMk (preCollisionMap_measurable_uncurry F ell s n hsn))

instance frameKernel_markov (F : ReferencePoissonFamily E a b) (ell s n : ℝ) (hsn : s^2+n^2=1)
    (K : Kernel (Icc a b × GaussianPhase E) E) [IsMarkovKernel K] :
    IsMarkovKernel (frameKernel F ell s n hsn K) := by
  unfold frameKernel
  infer_instance

/-- The fixed-clock tape expressed in initial-time coordinates, as a kernel in `t`. -/
def frameTape (F : ReferencePoissonFamily E a b) (ell s n : ℝ) (hsn : s^2+n^2=1)
    (K : Kernel (Icc a b × GaussianPhase E) E) [IsMarkovKernel K] :
    Kernel (Icc a b) (((GaussianPhase E × E) × E) × E) :=
  (((Kernel.const (Icc a b) (gaussianPhaseMeasure (F.law a))) ⊗ₖ frameKernel F ell s n hsn K) ×ₖ
    Kernel.const (Icc a b) (stdGaussian E)) ×ₖ Kernel.const (Icc a b) (stdGaussian E)

instance frameTape_markov (F : ReferencePoissonFamily E a b) (ell s n : ℝ) (hsn : s^2+n^2=1)
    (K : Kernel (Icc a b × GaussianPhase E) E) [IsMarkovKernel K] :
    IsMarkovKernel (frameTape F ell s n hsn K) := by
  unfold frameTape
  infer_instance

theorem fixedClockTape_eq_map (F : ReferencePoissonFamily E a b) (ell s n : ℝ)
    (hsn : s^2+n^2=1) (K : Kernel (Icc a b × GaussianPhase E) E) [IsMarkovKernel K]
    (t : Icc a b) :
    fixedClockTape F t (K.comap (Prod.mk t) measurable_prodMk_left) =
      (frameTape F ell s n hsn K t).map
        (Prod.map (Prod.map (Prod.map (preCollisionMap F ell t s n hsn) id) id) id) := by
  have hΦ := preCollisionMap_measurePreserving F ell t s n hsn
  have hmeas := hΦ.measurable
  have hν1 : ((Kernel.const (Icc a b) (gaussianPhaseMeasure (F.law a))) ⊗ₖ
      frameKernel F ell s n hsn K) t =
      gaussianPhaseMeasure (F.law a) ⊗ₘ
        ((K.comap (Prod.mk t) measurable_prodMk_left).comap
          (preCollisionMap F ell t s n hsn) hmeas) := by
    ext S hS
    rw [Kernel.compProd_apply hS, Measure.compProd_apply hS]
    rfl
  unfold fixedClockTape dormantJoint
  change ((gaussianPhaseMeasure (F.law t) ⊗ₘ _).prod (stdGaussian E)).prod (stdGaussian E) = _
  rw [← hΦ.map_eq, compProd_map_comap _ _ hmeas]
  unfold frameTape
  rw [Kernel.prod_apply, Kernel.prod_apply, Kernel.const_apply, hν1]
  have h1 := Measure.map_prod_map (gaussianPhaseMeasure (F.law a) ⊗ₘ
    ((K.comap (Prod.mk t) measurable_prodMk_left).comap
      (preCollisionMap F ell t s n hsn) hmeas)) (stdGaussian E)
    ((hmeas.prodMap measurable_id)) (measurable_id (α := E))
  rw [Measure.map_id] at h1
  have h2 := Measure.map_prod_map ((gaussianPhaseMeasure (F.law a) ⊗ₘ
    ((K.comap (Prod.mk t) measurable_prodMk_left).comap
      (preCollisionMap F ell t s n hsn) hmeas)).prod (stdGaussian E)) (stdGaussian E)
    ((hmeas.prodMap measurable_id).prodMap measurable_id) (measurable_id (α := E))
  rw [Measure.map_id] at h2
  rw [h1, h2]

theorem fixedClockOutput_measurable_uncurry (s n : ℝ) (hsn : s^2+n^2=1) (Γ : ℝ) :
    Measurable (fun p : ℝ × (((GaussianPhase E × E) × E) × E) =>
      fixedClockOutput s n hsn p.1 Γ p.2) := by
  have hrot : Measurable (phaseRotate (E := E) s n hsn) := (phaseRotate (E := E) s n hsn).measurable
  unfold fixedClockOutput correlatedHeatObservation gaussianMix dormantNewState
  simp only
  fun_prop

theorem fixedClockInput_measurable (F : ReferencePoissonFamily E a b) (ell s n : ℝ)
    (hsn : s^2+n^2=1) (t : Icc a b) :
    Measurable (fixedClockInput F ell t s n hsn) := by
  have hz : Measurable (fun z : ((GaussianPhase E × E) × E) × E => z.1.1.1) := by fun_prop
  have hsymm : Measurable (preCollisionMap F ell t s n hsn).symm :=
    (preCollisionMap F ell t s n hsn).symm.measurable
  exact measurable_fst.comp (hsymm.comp hz)

theorem fixedClockOutput_measurable (s n : ℝ) (hsn : s^2+n^2=1) (τ Γ : ℝ) :
    Measurable (fixedClockOutput s n hsn τ Γ (E := E)) :=
  Measurable.of_uncurry_left (f := fun τ : ℝ => fixedClockOutput s n hsn τ Γ (E := E))
    (fixedClockOutput_measurable_uncurry (E := E) s n hsn Γ)

/-- Matrix coefficients on indicator sets: the tape probability of the event
`input ∈ A, output ∈ B` is measurable in the clock time. -/
theorem measurable_clockTape_event (F : ReferencePoissonFamily E a b) (ell s n : ℝ)
    (hsn : s^2+n^2=1) (K : Kernel (Icc a b × GaussianPhase E) E) [IsMarkovKernel K]
    (τ : Icc a b → ℝ) (hτ : Measurable τ) (Γ : ℝ) {A B : Set (E × E)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Measurable (fun t : Icc a b =>
      fixedClockTape F t (K.comap (Prod.mk t) measurable_prodMk_left)
        {z | fixedClockInput F ell t s n hsn z ∈ A ∧
          fixedClockOutput s n hsn (τ t) Γ z ∈ B}) := by
  have hΦ := preCollisionMap_measurable_uncurry F ell s n hsn
  have hΨ : Measurable (fun p : Icc a b × (((GaussianPhase E × E) × E) × E) =>
      Prod.map (Prod.map (Prod.map (preCollisionMap F ell p.1 s n hsn) id) id) id p.2) := by
    refine (((hΦ.comp (measurable_fst.prodMk (measurable_snd.fst.fst.fst))).prodMk
      (measurable_snd.fst.fst.snd)).prodMk (measurable_snd.fst.snd)).prodMk (measurable_snd.snd)
  have hOut := (fixedClockOutput_measurable_uncurry (E := E) s n hsn Γ).comp
    ((hτ.comp measurable_fst).prodMk hΨ)
  let S' : Set (Icc a b × (((GaussianPhase E × E) × E) × E)) :=
    {p | p.2.1.1.1.1 ∈ A ∧ fixedClockOutput s n hsn (τ p.1) Γ
      (Prod.map (Prod.map (Prod.map (preCollisionMap F ell p.1 s n hsn) id) id) id p.2) ∈ B}
  have hS' : MeasurableSet S' :=
    (hA.preimage measurable_snd.fst.fst.fst.fst).inter (hB.preimage hOut)
  have hfun : (fun t : Icc a b =>
      fixedClockTape F t (K.comap (Prod.mk t) measurable_prodMk_left)
        {z | fixedClockInput F ell t s n hsn z ∈ A ∧
          fixedClockOutput s n hsn (τ t) Γ z ∈ B}) =
      fun t => frameTape F ell s n hsn K t (Prod.mk t ⁻¹' S') := by
    funext t
    have hΨt : Measurable (Prod.map (Prod.map (Prod.map
        (preCollisionMap F ell t s n hsn) (id : E → E)) (id : E → E)) (id : E → E)) :=
      by
        have := (preCollisionMap F ell t s n hsn).measurable
        fun_prop
    have hin := fixedClockInput_measurable F ell s n hsn t
    have hout := fixedClockOutput_measurable (E := E) s n hsn (τ t) Γ
    have hSt : MeasurableSet {z | fixedClockInput F ell t s n hsn z ∈ A ∧
        fixedClockOutput s n hsn (τ t) Γ z ∈ B} :=
      (hA.preimage hin).inter (hB.preimage hout)
    rw [fixedClockTape_eq_map F ell s n hsn K t, Measure.map_apply hΨt hSt]
    congr 1
    ext u
    show (((preCollisionMap F ell t s n hsn).symm
        ((Prod.map (Prod.map (Prod.map (preCollisionMap F ell t s n hsn) id) id) id u).1.1.1)).1 ∈ A ∧
      fixedClockOutput s n hsn (τ t) Γ
        (Prod.map (Prod.map (Prod.map (preCollisionMap F ell t s n hsn) id) id) id u) ∈ B) ↔
      (u.1.1.1.1 ∈ A ∧ fixedClockOutput s n hsn (τ t) Γ
        (Prod.map (Prod.map (Prod.map (preCollisionMap F ell t s n hsn) id) id) id u) ∈ B)
    refine and_congr ?_ Iff.rfl
    simp
  rw [hfun]
  exact Kernel.measurable_kernel_prodMk_left hS'

end Tape

section Source
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

local instance fact_two_ne_top : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩

/-- The source clock-indexed dormant kernel obtained from a jointly measurable kernel. -/
abbrev clockSection (K : Kernel (Icc (0:ℝ) (1/2) × GaussianPhase E) E) :
    Icc (0:ℝ) (1/2) → Kernel (GaussianPhase E) E :=
  fun t => K.comap (Prod.mk t) measurable_prodMk_left

theorem sourceClockChannel_indicator_measurable
    {μ : Measure E} [IsProbabilityMeasure μ] {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ell Γ : ℝ) (hΓ : 0 ≤ Γ)
    (K : Kernel (Icc (0:ℝ) (1/2) × GaussianPhase E) E) [IsMarkovKernel K]
    (hκ : ∀ t, ConditionallyInvariant (stdGaussian E) (clockSection K t))
    (c d : ℝ) {A' B' : Set (E × E)} (hA' : MeasurableSet A') (hB' : MeasurableSet B') :
    Measurable fun t : Icc (0:ℝ) (1/2) =>
      ⟪indicatorConstLp 2 hA' (measure_ne_top (((clockTransportFamily H hA hR).law 0).prod
        (stdGaussian E)) A') c,
        sourceClockChannel H hA hR ell Γ hΓ (clockSection K) hκ t
          (indicatorConstLp 2 hB' (measure_ne_top (((clockTransportFamily H hA hR).law 0).prod
            (stdGaussian E)) B') d)⟫ := by
  let F := clockTransportFamily H hA hR
  have hτ : Measurable (fun t : Icc (0:ℝ) (1/2) => A * (t:ℝ)^2) := by fun_prop
  have hev := measurable_clockTape_event F ell (1/2) (Real.sqrt 3/2) source_split_coefficients K
    (fun t => A * (t:ℝ)^2) hτ Γ hA' hB'
  have hconv := hev.ennreal_toReal.const_mul (c*d)
  have hfun : ∀ t : Icc (0:ℝ) (1/2),
      ⟪indicatorConstLp 2 hA' (measure_ne_top (((clockTransportFamily H hA hR).law 0).prod
        (stdGaussian E)) A') c,
        sourceClockChannel H hA hR ell Γ hΓ (clockSection K) hκ t
          (indicatorConstLp 2 hB' (measure_ne_top (((clockTransportFamily H hA hR).law 0).prod
            (stdGaussian E)) B') d)⟫ =
      (c*d) * (fixedClockTape F t (clockSection K t)
        {z | fixedClockInput F ell t (1/2) (Real.sqrt 3/2) source_split_coefficients z ∈ A' ∧
          fixedClockOutput (1/2) (Real.sqrt 3/2) source_split_coefficients
            (A*(t:ℝ)^2) Γ z ∈ B'}).toReal := by
    intro t
    rw [sourceClockChannel_pairing]
    have hp := fixedClockInput_measurePreserving F ell t (1/2) (Real.sqrt 3/2)
      source_split_coefficients (clockSection K t)
    have hq : MeasurePreserving (fixedClockOutput (1/2) (Real.sqrt 3/2)
        source_split_coefficients (A*(t:ℝ)^2) Γ :
          ((GaussianPhase E × E) × E) × E → E × E) (fixedClockTape F t (clockSection K t))
        ((F.law 0).prod (stdGaussian E)) := by
      have := fixedClockOutput_measurePreserving F t (1/2) (Real.sqrt 3/2)
        source_split_coefficients (clockSection K t) (hκ t) (A*(t:ℝ)^2) Γ hΓ
      rwa [clockTransportFamily_heat_return H hA hR t t.property] at this
    have h1 := hp.quasiMeasurePreserving.ae_eq_comp
      (indicatorConstLp_coeFn (p := 2) (hs := hA') (hμs := measure_ne_top _ A') (c := c))
    have h2 := hq.quasiMeasurePreserving.ae_eq_comp
      (indicatorConstLp_coeFn (p := 2) (hs := hB') (hμs := measure_ne_top _ B') (c := d))
    have hSm : MeasurableSet {z | fixedClockInput F ell t (1/2) (Real.sqrt 3/2)
        source_split_coefficients z ∈ A' ∧ fixedClockOutput (1/2) (Real.sqrt 3/2)
          source_split_coefficients (A*(t:ℝ)^2) Γ z ∈ B'} :=
      ((hA'.preimage (fixedClockInput_measurable F ell _ _ _ t)).inter
        (hB'.preimage (fixedClockOutput_measurable _ _ _ _ _)))
    refine (integral_congr_ae (h1.mul h2)).trans ?_
    have hind : (fun z => (A'.indicator (fun _ => c) ∘ fixedClockInput F ell t (1/2)
        (Real.sqrt 3/2) source_split_coefficients) z *
        (B'.indicator (fun _ => d) ∘ fixedClockOutput (1/2) (Real.sqrt 3/2)
          source_split_coefficients (A*(t:ℝ)^2) Γ) z) =
        {z | fixedClockInput F ell t (1/2) (Real.sqrt 3/2) source_split_coefficients z ∈ A' ∧
          fixedClockOutput (1/2) (Real.sqrt 3/2) source_split_coefficients
            (A*(t:ℝ)^2) Γ z ∈ B'}.indicator (fun _ => c*d) := by
      funext z
      classical
      simp only [Function.comp_apply]
      rw [Set.indicator_apply, Set.indicator_apply, Set.indicator_apply]
      split_ifs <;> simp_all
    refine (integral_congr_ae (Filter.Eventually.of_forall fun z => congrFun hind z)).trans ?_
    rw [integral_indicator_const _ hSm]
    simp [Measure.real, mul_comm]
  convert hconv using 1
  funext t
  exact hfun t

/-- Every fixed-clock channel family from a jointly measurable kernel is strongly
measurable in the clock time, on each input. -/
theorem sourceClockChannel_stronglyMeasurable
    {μ : Measure E} [IsProbabilityMeasure μ] {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ell Γ : ℝ) (hΓ : 0 ≤ Γ)
    (K : Kernel (Icc (0:ℝ) (1/2) × GaussianPhase E) E) [IsMarkovKernel K]
    (hκ : ∀ t, ConditionallyInvariant (stdGaussian E) (clockSection K t))
    (g : Lp ℝ 2 (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E))) :
    StronglyMeasurable fun t : Icc (0:ℝ) (1/2) =>
      sourceClockChannel H hA hR ell Γ hΓ (clockSection K) hκ t g := by
  apply stronglyMeasurable_of_weak
  intro f
  exact measurable_inner_of_indicator _
    (fun t => sourceClockChannel H hA hR ell Γ hΓ (clockSection K) hκ t)
    (fun c d {A' B'} hA' hB' =>
      sourceClockChannel_indicator_measurable H hA hR ell Γ hΓ K hκ c d hA' hB') f g

/-- Strong integrability of the clock channels over the uniform clock. -/
theorem sourceClockChannel_integrable
    {μ : Measure E} [IsProbabilityMeasure μ] {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ell Γ : ℝ) (hΓ : 0 ≤ Γ)
    (K : Kernel (Icc (0:ℝ) (1/2) × GaussianPhase E) E) [IsMarkovKernel K]
    (hκ : ∀ t, ConditionallyInvariant (stdGaussian E) (clockSection K t))
    (f : Lp ℝ 2 (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E))) :
    Integrable (fun t => sourceClockChannel H hA hR ell Γ hΓ (clockSection K) hκ t f)
      (boundedClockLaw (1/2) (by norm_num)) :=
  integrable_of_stronglyMeasurable_contraction _
    (fun t => sourceClockChannel H hA hR ell Γ hΓ (clockSection K) hκ t)
    (fun t => sourceClockChannel_norm_le H hA hR ell Γ hΓ (clockSection K) hκ t)
    (fun g => sourceClockChannel_stronglyMeasurable H hA hR ell Γ hΓ K hκ g) f

/-- Strong integrability of the adjoint clock channels. -/
theorem sourceClockChannel_adjoint_integrable
    {μ : Measure E} [IsProbabilityMeasure μ] {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ell Γ : ℝ) (hΓ : 0 ≤ Γ)
    (K : Kernel (Icc (0:ℝ) (1/2) × GaussianPhase E) E) [IsMarkovKernel K]
    (hκ : ∀ t, ConditionallyInvariant (stdGaussian E) (clockSection K t))
    (f : Lp ℝ 2 (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E))) :
    Integrable (fun t => (sourceClockChannel H hA hR ell Γ hΓ (clockSection K) hκ t).adjoint f)
      (boundedClockLaw (1/2) (by norm_num)) :=
  integrable_of_stronglyMeasurable_contraction _
    (fun t => (sourceClockChannel H hA hR ell Γ hΓ (clockSection K) hκ t).adjoint)
    (fun t => by
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact sourceClockChannel_norm_le H hA hR ell Γ hΓ (clockSection K) hκ t)
    (stronglyMeasurable_adjoint _
      (fun g => sourceClockChannel_stronglyMeasurable H hA hR ell Γ hΓ K hκ g)) f

/-- One-step contraction for every centered L² density, from a jointly measurable
conditionally invariant dormant kernel. The clock integrability hypotheses of
`sourcePhaseDensity_energy_contraction` are conclusions here. The dormant bound
`physicalDormantW12` remains the only analytic premise. -/
theorem sourcePhaseDensity_energy_contraction_of_kernel {μ : Measure E} [IsProbabilityMeasure μ]
    {h R m θ C : ℝ} (hh0 : 0 < h)
    (H : VarianceHeatFamily μ (3*(2*h^2)/4) R) (hR : 2*h^2 < R)
    (hm : ∀ v ∈ Icc (3*(2*h^2)/4) (2*h^2), H.source.lower v = m)
    (hm0 : 0 < m) (hm1 : m ≤ 1) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ (Real.sqrt 2/32)/32) (hC : 0 ≤ C)
    (hh : h ≤ 1/4) (hhC : h ≤ (Real.sqrt 2/32)/(8*(C/2+200)))
    (K : Kernel (Icc (0:ℝ) (1/2) × GaussianPhase E) E) [IsMarkovKernel K]
    (hκ : ∀ t, ConditionallyInvariant (stdGaussian E) (clockSection K t))
    (hW : ∀ t, physicalDormantW12 (clockTransportFamily H (by positivity) hR)
      t (clockSection K t) (hκ t) C (2*h^2))
    (f : centered (((clockTransportFamily H (by positivity) hR).law 0).prod (stdGaussian E))) :
    quadraticEnergy (sourceCorrector H (by positivity) hR) (θ*Real.sqrt m)
      (sourcePhaseDensity H (by positivity) hR (Real.sqrt 2*h) (Real.sqrt m*h)
        (by positivity) (clockSection K) hκ
        (fun f => sourceClockChannel_integrable H (by positivity) hR _ _ (by positivity) K hκ f) f) ≤
      sourceContractionFactor θ m h *
        quadraticEnergy (sourceCorrector H (by positivity) hR) (θ*Real.sqrt m) f :=
  sourcePhaseDensity_energy_contraction hh0 H hR hm hm0 hm1 hθ0 hθ hC hh hhC
    (clockSection K) hκ hW
    (fun f => sourceClockChannel_integrable H (by positivity) hR _ _ (by positivity) K hκ f)
    (fun f => sourceClockChannel_adjoint_integrable H (by positivity) hR _ _ (by positivity) K hκ f) f

/-- Iterated centered L² mixing of the density and observable operators of the
constructed source transition, with the dormant bound as the only analytic premise. -/
theorem sourcePhase_mixing_of_kernel {μ : Measure E} [IsProbabilityMeasure μ]
    {h R m θ C : ℝ} (hh0 : 0 < h)
    (H : VarianceHeatFamily μ (3*(2*h^2)/4) R) (hR : 2*h^2 < R)
    (hm : ∀ v ∈ Icc (3*(2*h^2)/4) (2*h^2), H.source.lower v = m)
    (hm0 : 0 < m) (hm1 : m ≤ 1) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ (Real.sqrt 2/32)/32) (hC : 0 ≤ C)
    (hh : h ≤ 1/4) (hhC : h ≤ (Real.sqrt 2/32)/(8*(C/2+200)))
    (K : Kernel (Icc (0:ℝ) (1/2) × GaussianPhase E) E) [IsMarkovKernel K]
    (hκ : ∀ t, ConditionallyInvariant (stdGaussian E) (clockSection K t))
    (hW : ∀ t, physicalDormantW12 (clockTransportFamily H (by positivity) hR)
      t (clockSection K t) (hκ t) C (2*h^2))
    (k : ℕ) :
    ‖sourceCenteredPhaseDensity H (by positivity) hR (Real.sqrt 2*h) (Real.sqrt m*h)
      (by positivity) (clockSection K) hκ
      (fun f => sourceClockChannel_integrable H (by positivity) hR _ _ (by positivity) K hκ f) ^ k‖ ≤
        Real.sqrt ((5/3:ℝ)*(sourceContractionFactor θ m h)^k) ∧
    ‖sourceCenteredPhaseOperator H (by positivity) hR (Real.sqrt 2*h) (Real.sqrt m*h)
      (by positivity) (clockSection K) hκ
      (fun f => sourceClockChannel_integrable H (by positivity) hR _ _ (by positivity) K hκ f) ^ k‖ ≤
        Real.sqrt ((5/3:ℝ)*(sourceContractionFactor θ m h)^k) :=
  sourcePhase_mixing hh0 H hR hm hm0 hm1 hθ0 hθ hC hh hhC (clockSection K) hκ hW
    (fun f => sourceClockChannel_integrable H (by positivity) hR _ _ (by positivity) K hκ f)
    (fun f => sourceClockChannel_adjoint_integrable H (by positivity) hR _ _ (by positivity) K hκ f) k

end Source

end AcceleratedLogConcave.Kinetic
