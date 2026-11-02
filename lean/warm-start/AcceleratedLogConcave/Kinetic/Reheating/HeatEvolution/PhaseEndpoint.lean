import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.InitialCorrector
import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.PhaseTransport
import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.PhaseCurrentCalculus

/-! Physical endpoint identification for the genuine ordinary heat current. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set InnerProductSpace
open scoped Topology RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Changing only the presentation of an equal reference law does not change
its genuine weighted Poisson current. -/
theorem visibleCorrector_inner_congr_measure (μ ν : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (he : μ = ν)
    (V : E → ℝ) (hV : ContDiff ℝ 2 V) (hI : Integrable (fun x => Real.exp (-V x)))
    (hμ : μ = volume.tilted (fun x => -V x)) (hν : ν = volume.tilted (fun x => -V x))
    (m L : ℝ) (hm : 0 < m)
    (hl : ∀ x v, m*‖v‖^2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hu : ∀ x v, fderiv ℝ (fderiv ℝ V) x v v ≤ L*‖v‖^2)
    (f : Lp ℝ 2 (μ.prod (stdGaussian E))) (g : Lp ℝ 2 (ν.prod (stdGaussian E)))
    (hfg : f =ᵐ[μ.prod (stdGaussian E)] g) :
    inner ℝ (visibleCorrector μ V hV hI hμ m L hm hl hu f) f =
      inner ℝ (visibleCorrector ν V hV hI hν m L hm hl hu g) g := by
  subst ν
  have heq : f = g := Lp.ext hfg
  subst g
  rfl

theorem phaseHeatCurrent_eq_physical {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
    (t : ℝ) (ht : t ∈ Ioo a b) :
    let q := (compactPhaseHeatQuotient_memLp F hf hc hheat t (Ioo_subset_Icc_self ht)).1.toLp _
    phaseHeatCurrent F hf hc hheat t =
      inner ℝ (phaseVisibleCorrector F t (Ioo_subset_Icc_self ht) q) q := by
  dsimp only
  unfold phaseHeatCurrent
  rw [phaseHeatMovingCoreLp_eq_pullback F hf hc hheat t (Ioo_subset_Icc_self ht),
    phaseHeatPullback_hiddenEmbedding,
    phaseHeat_corrector_pullback_pairing F t ht]
  exact real_inner_comm _ _

theorem phaseHeatCurrent_initial {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a)) :
    let g := compactTestL2 ((F.law a).prod (stdGaussian E)) f hf.continuous hc
    phaseHeatCurrent F hf hc hheat a =
      inner ℝ (phaseVisibleCorrector F a ⟨le_rfl,F.ordered⟩ g) g := by
  dsimp only
  unfold phaseHeatCurrent
  rw [phaseHeatMovingCoreLp_initial, corrector_initial_eq_physical]
  rw [real_inner_comm]
  exact (visibleCorrector_inner (F.law a) (F.potential a) (F.potential_C2 a)
    (F.integrable a F.leftTime.property) (F.gibbs_law a F.leftTime.property)
    (F.lower a) 1 (F.lower_pos a F.leftTime.property) (F.hessian_lower a F.leftTime.property)
    (by simpa only [one_mul] using F.hessian_upper a F.leftTime.property) _).symm

theorem phaseHeatCurrent_continuousOn_Ico {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a)) :
    ContinuousOn (phaseHeatCurrent F hf hc hheat) (Ico a b) := by
  have hq := (Kinetic.hiddenEmbedding (F.law a)).continuous.comp
    (phaseHeatMovingCoreLp_continuous F hf hc hheat)
  exact hq.continuousOn.inner ((corrector_continuousOn_Ico F).clm_apply hq.continuousOn)

/-- The moving-frame endpoint is the current of the actual ordinary heat output. -/
theorem phaseHeatCurrent_eq_ordinaryHeatDensity {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
    (t : ℝ) (ht : t ∈ Ioo a b) :
    let ht' := Ioo_subset_Icc_self ht
    let g := ordinaryHeatDensity (F.law a) (t-a)
      (compactTestL2 ((F.law a).prod (stdGaussian E)) f hf.continuous hc)
    phaseHeatCurrent F hf hc hheat t =
      inner ℝ (visibleCorrector (heatedLaw (F.law a) (t-a)) (F.potential t) (F.potential_C2 t)
        (F.integrable t ht') ((hheat t ht').symm.trans (F.gibbs_law t ht'))
        (F.lower t) 1 (F.lower_pos t ht') (F.hessian_lower t ht')
        (by simpa only [one_mul] using F.hessian_upper t ht') g) g := by
  dsimp only
  rw [phaseHeatCurrent_eq_physical F hf hc hheat t ht]
  apply visibleCorrector_inner_congr_measure _ _ (hheat t (Ioo_subset_Icc_self ht))
  have hg := compactPhaseHeatQuotient_eq_ordinaryHeatDensity F hf hc t
    (Ioo_subset_Icc_self ht) (hheat t (Ioo_subset_Icc_self ht))
  have hg' := hg.filter_mono (le_of_eq (congrArg
    (fun μ : Measure E => ae (μ.prod (stdGaussian E))) (hheat t (Ioo_subset_Icc_self ht))))
  exact (compactPhaseHeatQuotient_memLp F hf hc hheat t (Ioo_subset_Icc_self ht)).1.coeFn_toLp.trans hg'.symm

/-- The physical identification includes the initial endpoint, where the
reference flow and its Jacobian are exactly the identity. -/
theorem phaseHeatCurrent_eq_physical_Ico {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
    (t : ℝ) (ht : t ∈ Ico a b) :
    let ht' : t ∈ Icc a b := ⟨ht.1,ht.2.le⟩
    let q := (compactPhaseHeatQuotient_memLp F hf hc hheat t ht').1.toLp _
    phaseHeatCurrent F hf hc hheat t = inner ℝ (phaseVisibleCorrector F t ht' q) q := by
  rcases ht.1.eq_or_lt with rfl | hat
  · dsimp only
    have hq : (compactPhaseHeatQuotient_memLp F hf hc hheat a ⟨le_rfl,F.ordered⟩).1.toLp _ =
        compactTestL2 ((F.law a).prod (stdGaussian E)) f hf.continuous hc := by
      apply Lp.ext
      filter_upwards [(compactPhaseHeatQuotient_memLp F hf hc hheat a ⟨le_rfl,F.ordered⟩).1.coeFn_toLp,
        (compactTest_memLp ((F.law a).prod (stdGaussian E)) f hf.continuous hc).coeFn_toLp] with z h1 h2
      change (compactTestL2 ((F.law a).prod (stdGaussian E)) f hf.continuous hc) z = f z at h2
      rw [h1,h2]
      exact compactHeatQuotient_initial F (fun x => f (x,z.2)) z.1
    rw [hq]
    exact phaseHeatCurrent_initial F hf hc hheat
  · exact phaseHeatCurrent_eq_physical F hf hc hheat t ⟨hat,ht.2⟩

theorem phaseHeatCurrent_eq_ordinaryHeatDensity_Ico {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
    (t : ℝ) (ht : t ∈ Ico a b) :
    let ht' : t ∈ Icc a b := ⟨ht.1,ht.2.le⟩
    let g := ordinaryHeatDensity (F.law a) (t-a)
      (compactTestL2 ((F.law a).prod (stdGaussian E)) f hf.continuous hc)
    phaseHeatCurrent F hf hc hheat t =
      inner ℝ (visibleCorrector (heatedLaw (F.law a) (t-a)) (F.potential t) (F.potential_C2 t)
        (F.integrable t ht') ((hheat t ht').symm.trans (F.gibbs_law t ht'))
        (F.lower t) 1 (F.lower_pos t ht') (F.hessian_lower t ht')
        (by simpa only [one_mul] using F.hessian_upper t ht') g) g := by
  dsimp only
  rw [phaseHeatCurrent_eq_physical_Ico F hf hc hheat t ht]
  apply visibleCorrector_inner_congr_measure _ _ (hheat t ⟨ht.1,ht.2.le⟩)
  have hg := compactPhaseHeatQuotient_eq_ordinaryHeatDensity F hf hc t
    ⟨ht.1,ht.2.le⟩ (hheat t ⟨ht.1,ht.2.le⟩)
  have hg' := hg.filter_mono (le_of_eq (congrArg
    (fun μ : Measure E => ae (μ.prod (stdGaussian E))) (hheat t ⟨ht.1,ht.2.le⟩)))
  exact (compactPhaseHeatQuotient_memLp F hf hc hheat t ⟨ht.1,ht.2.le⟩).1.coeFn_toLp.trans hg'.symm

end AcceleratedLogConcave.Kinetic.Reheating
