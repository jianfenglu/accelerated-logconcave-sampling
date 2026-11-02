import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.ClockTransportFamily
import AcceleratedLogConcave.Kinetic.ReferenceFlow.TransportBudget
import AcceleratedLogConcave.Kinetic.Mixing.SourceCollision
import AcceleratedLogConcave.Kinetic.Mixing.IntervalBounded
import AcceleratedLogConcave.Kinetic.Mixing.TransportClock
import AcceleratedLogConcave.Kinetic.Mixing.CenteredDiscrete
import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.PhaseCorrectorPairing
import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.InitialCorrector

/-! The actual source-parameter discrete phase transition. The clock is uniform
on [0,1/2], and its physical tape is the constructed split/flow/dormant/reheat/OU
tape. Analytic contraction is assembled below from its actual components. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set InnerProductSpace
open scoped Topology RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic
open Analysis.Poisson Reheating ConditionalContraction
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Literal fixed-clock observable channel with the source return variance. -/
def sourceClockChannel {μ : Measure E} [IsProbabilityMeasure μ] {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ell Γ : ℝ) (hΓ : 0 ≤ Γ)
    (κ : Icc (0:ℝ) (1/2) → Kernel (GaussianPhase E) E)
    [∀ t, IsMarkovKernel (κ t)]
    (hκ : ∀ t, ConditionallyInvariant (stdGaussian E) (κ t))
    (t : Icc (0:ℝ) (1/2)) :
    Lp ℝ 2 (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E)) →L[ℝ]
      Lp ℝ 2 (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E)) :=
  returningClockChannel (clockTransportFamily H hA hR) ell t
    (1/2) (Real.sqrt 3/2) source_split_coefficients (κ t) (hκ t)
    (A*(t:ℝ)^2) Γ hΓ (clockTransportFamily_heat_return H hA hR t t.property)

/-- The actual observable transition, averaged over the independent source clock. -/
def sourcePhaseOperator {μ : Measure E} [IsProbabilityMeasure μ] {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ell Γ : ℝ) (hΓ : 0 ≤ Γ)
    (κ : Icc (0:ℝ) (1/2) → Kernel (GaussianPhase E) E)
    [∀ t, IsMarkovKernel (κ t)]
    (hκ : ∀ t, ConditionallyInvariant (stdGaussian E) (κ t))
    (hI : ∀ f, Integrable (fun t => sourceClockChannel H hA hR ell Γ hΓ κ hκ t f)
      (boundedClockLaw (1/2) (by norm_num))) :
    Lp ℝ 2 (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E)) →L[ℝ]
      Lp ℝ 2 (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E)) :=
  discretePhaseOperator (by norm_num) (clockTransportFamily H hA hR) ell
    (1/2) (Real.sqrt 3/2) source_split_coefficients κ hκ (fun t => A*(t:ℝ)^2)
    Γ hΓ (fun t => clockTransportFamily_heat_return H hA hR t t.property) hI

/-- The relative-density transition is the genuine Hilbert adjoint. -/
def sourcePhaseDensity {μ : Measure E} [IsProbabilityMeasure μ] {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ell Γ : ℝ) (hΓ : 0 ≤ Γ)
    (κ : Icc (0:ℝ) (1/2) → Kernel (GaussianPhase E) E)
    [∀ t, IsMarkovKernel (κ t)]
    (hκ : ∀ t, ConditionallyInvariant (stdGaussian E) (κ t))
    (hI : ∀ f, Integrable (fun t => sourceClockChannel H hA hR ell Γ hΓ κ hκ t f)
      (boundedClockLaw (1/2) (by norm_num))) :=
  (sourcePhaseOperator H hA hR ell Γ hΓ κ hκ hI).adjoint

/-- The actual source observable operator restricted to centered visible inputs. -/
def sourceCenteredPhaseOperator {μ : Measure E} [IsProbabilityMeasure μ] {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ell Γ : ℝ) (hΓ : 0 ≤ Γ)
    (κ : Icc (0:ℝ) (1/2) → Kernel (GaussianPhase E) E)
    [∀ t, IsMarkovKernel (κ t)]
    (hκ : ∀ t, ConditionallyInvariant (stdGaussian E) (κ t))
    (hI : ∀ f, Integrable (fun t => sourceClockChannel H hA hR ell Γ hΓ κ hκ t f)
      (boundedClockLaw (1/2) (by norm_num))) :=
  centeredDiscretePhaseOperator (by norm_num) (clockTransportFamily H hA hR) ell
    (1/2) (Real.sqrt 3/2) source_split_coefficients κ hκ (fun t => A*(t:ℝ)^2)
    Γ hΓ (fun t => clockTransportFamily_heat_return H hA hR t t.property) hI

/-- The actual source density operator restricted to centered visible inputs. -/
def sourceCenteredPhaseDensity {μ : Measure E} [IsProbabilityMeasure μ] {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ell Γ : ℝ) (hΓ : 0 ≤ Γ)
    (κ : Icc (0:ℝ) (1/2) → Kernel (GaussianPhase E) E)
    [∀ t, IsMarkovKernel (κ t)]
    (hκ : ∀ t, ConditionallyInvariant (stdGaussian E) (κ t))
    (hI : ∀ f, Integrable (fun t => sourceClockChannel H hA hR ell Γ hΓ κ hκ t f)
      (boundedClockLaw (1/2) (by norm_num))) :=
  centeredDiscretePhaseDensity (by norm_num) (clockTransportFamily H hA hR) ell
    (1/2) (Real.sqrt 3/2) source_split_coefficients κ hκ (fun t => A*(t:ℝ)^2)
    Γ hΓ (fun t => clockTransportFamily_heat_return H hA hR t t.property) hI

/-- The source modified energy uses the genuine initial physical corrector. -/
def sourceCorrector {μ : Measure E} {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R) :=
  phaseVisibleCorrector (clockTransportFamily H hA hR) 0 ⟨le_rfl,by norm_num⟩

theorem sourceClockChannel_norm_le {μ : Measure E} [IsProbabilityMeasure μ] {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ell Γ : ℝ) (hΓ : 0 ≤ Γ)
    (κ : Icc (0:ℝ) (1/2) → Kernel (GaussianPhase E) E)
    [∀ t, IsMarkovKernel (κ t)]
    (hκ : ∀ t, ConditionallyInvariant (stdGaussian E) (κ t))
    (t : Icc (0:ℝ) (1/2)) : ‖sourceClockChannel H hA hR ell Γ hΓ κ hκ t‖ ≤ 1 :=
  returningClockChannel_norm_le (clockTransportFamily H hA hR) ell t
    (1/2) (Real.sqrt 3/2) source_split_coefficients (κ t) (hκ t)
    (A*(t:ℝ)^2) Γ hΓ (clockTransportFamily_heat_return H hA hR t t.property)

theorem sourceCorrector_energy_bounds {μ : Measure E} {A R m : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (hm : ∀ v ∈ Icc (3*A/4) A, H.source.lower v = m)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθq : θ ≤ 1/4)
    (f : Lp ℝ 2 (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E))) :
    (3/8:ℝ)*‖f‖^2 ≤ quadraticEnergy (sourceCorrector H hA hR) (θ*Real.sqrt m) f ∧
      quadraticEnergy (sourceCorrector H hA hR) (θ*Real.sqrt m) f ≤ (5/8:ℝ)*‖f‖^2 := by
  let F := clockTransportFamily H hA hR
  have hm0 : F.lower 0 = m := clockTransportFamily_lower_eq H hA hR hm 0 (by constructor <;> norm_num)
  have hb := visibleCorrector_energy_bounds_quarter (F.law 0) (F.potential 0) (F.potential_C2 0)
    (F.integrable 0 F.leftTime.property) (F.gibbs_law 0 F.leftTime.property) (F.lower 0) 1
    (F.lower_pos 0 F.leftTime.property) (F.hessian_lower 0 F.leftTime.property)
    (by simpa only [one_mul] using F.hessian_upper 0 F.leftTime.property) θ hθ hθq f
  change (3/8:ℝ)*‖f‖^2 ≤ quadraticEnergy (sourceCorrector H hA hR) (θ*Real.sqrt (F.lower 0)) f ∧
    quadraticEnergy (sourceCorrector H hA hR) (θ*Real.sqrt (F.lower 0)) f ≤ (5/8:ℝ)*‖f‖^2 at hb
  rw [hm0] at hb
  exact hb

/-- The visible initial energy is the actual full phase energy of the hidden lift. -/
theorem sourceCorrector_initial_energy {μ : Measure E} {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ε : ℝ)
    (f : Lp ℝ 2 (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E))) :
    quadraticEnergy ((clockTransportFamily H hA hR).corrector 0) ε
      (Kinetic.hiddenEmbedding ((clockTransportFamily H hA hR).law 0) f) =
      quadraticEnergy (sourceCorrector H hA hR) ε f := by
  rw [corrector_initial_eq_physical]
  let F := clockTransportFamily H hA hR
  exact (visibleCorrector_energy_eq (F.law 0) (F.potential 0) (F.potential_C2 0)
    (F.integrable 0 F.leftTime.property) (F.gibbs_law 0 F.leftTime.property) (F.lower 0) 1
    (F.lower_pos 0 F.leftTime.property) (F.hessian_lower 0 F.leftTime.property)
    (by simpa only [one_mul] using F.hessian_upper 0 F.leftTime.property) ε f).symm

/-- Adjoining the independent hidden Gaussian preserves the actual scalar mean. -/
theorem mean_hiddenEmbedding (ν : Measure E) [IsProbabilityMeasure ν]
    (f : Lp ℝ 2 (ν.prod (stdGaussian E))) :
    mean (gaussianPhaseMeasure ν) (Kinetic.hiddenEmbedding ν f) = mean (ν.prod (stdGaussian E)) f := by
  rw [mean_apply,mean_apply]
  calc
    _ = ∫ z : GaussianPhase E, f z.1 ∂(ν.prod (stdGaussian E)).prod (stdGaussian E) :=
      integral_congr_ae (Lp.coeFn_compMeasurePreserving f (measurePreserving_fst (ν := stdGaussian E)))
    _ = _ := by simp [integral_fun_fst]

/-- Actual physical and fixed-frame energies agree, including the initial time. -/
theorem physicalFrameEnergy_eq {a b : ℝ} (F : ReferencePoissonFamily E a b)
    (ell s n : ℝ) (hsn : s^2+n^2=1) (ε t : ℝ) (ht : t ∈ Ico a b)
    (f : Lp ℝ 2 (gaussianPhaseMeasure (F.law a))) :
    quadraticEnergy (F.corrector t) ε (physicalFrameDensity F ell s n hsn t f) =
      quadraticEnergy (F.physicalCorrector ⟨t,ht.1,ht.2.le⟩) ε
        (physicalDensityTransport F ell s n hsn ⟨t,ht.1,ht.2.le⟩ f) := by
  rcases ht.1.eq_or_lt with he | he
  · subst t
    rw [physicalFrameDensity_initial]
    change quadraticEnergy (F.corrector a) ε f =
      quadraticEnergy (F.physicalCorrector F.leftTime) ε
        (physicalDensityTransport F ell s n hsn F.leftTime f)
    rw [physicalDensityTransport_initial, corrector_initial_eq_physical]
  · rw [physicalFrameDensity_interior F ell s n hsn t ⟨he,ht.2⟩,
      F.corrector_eq_physical t ⟨he,ht.2⟩]
    unfold quadraticEnergy
    simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.symm_apply_apply,
      LinearIsometryEquiv.norm_map, LinearIsometryEquiv.inner_map_map]

/-- Source curvature gives uniform energy bounds along the actual transport. -/
theorem sourcePhysicalFrameEnergy_bounds {μ : Measure E} {A R m : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (hm : ∀ v ∈ Icc (3*A/4) A, H.source.lower v = m)
    (ell θ : ℝ) (hθ : 0 ≤ θ) (hθq : θ ≤ 1/4)
    (f : Lp ℝ 2 (gaussianPhaseMeasure ((clockTransportFamily H hA hR).law 0)))
    (t : ℝ) (ht : t ∈ Ico (0:ℝ) (1/2)) :
    (3/8:ℝ)*‖f‖^2 ≤ quadraticEnergy ((clockTransportFamily H hA hR).corrector t)
      (θ*Real.sqrt m) (physicalFrameDensity (clockTransportFamily H hA hR) ell
        (1/2) (Real.sqrt 3/2) source_split_coefficients t f) ∧
    quadraticEnergy ((clockTransportFamily H hA hR).corrector t)
      (θ*Real.sqrt m) (physicalFrameDensity (clockTransportFamily H hA hR) ell
        (1/2) (Real.sqrt 3/2) source_split_coefficients t f) ≤ (5/8:ℝ)*‖f‖^2 := by
  let F := clockTransportFamily H hA hR
  let τ : Icc (0:ℝ) (1/2) := ⟨t,ht.1,ht.2.le⟩
  let g := physicalDensityTransport F ell (1/2) (Real.sqrt 3/2) source_split_coefficients τ f
  have hb := gaussianCorrectedEnergy_bounds_quarter (F.law t) (F.potential t) (F.potential_C2 t)
    (F.integrable t τ.property) (F.gibbs_law t τ.property) (F.lower t) 1
    (F.lower_pos t τ.property) (F.hessian_lower t τ.property)
    (by simpa only [one_mul] using F.hessian_upper t τ.property) θ hθ hθq g
  change (3/8:ℝ)*‖g‖^2 ≤ quadraticEnergy (F.physicalCorrector τ) (θ*Real.sqrt (F.lower t)) g ∧
    quadraticEnergy (F.physicalCorrector τ) (θ*Real.sqrt (F.lower t)) g ≤ (5/8:ℝ)*‖g‖^2 at hb
  rw [clockTransportFamily_lower_eq H hA hR hm t τ.property] at hb
  have hn : ‖g‖ = ‖f‖ := (physicalDensityTransport F ell (1/2) (Real.sqrt 3/2)
    source_split_coefficients τ).norm_map f
  rw [hn] at hb
  rw [physicalFrameEnergy_eq _ _ _ _ _ _ _ ht f]
  exact hb

/-- The exact multiplicative factor supplied by the uniform half-clock. -/
def sourceContractionFactor (θ m h : ℝ) : ℝ :=
  (1 + (Real.sqrt 2 * θ / 64) * (Real.sqrt m * h))⁻¹

theorem sourceContractionFactor_nonneg (θ m h : ℝ) (hθ : 0 ≤ θ) (hh : 0 ≤ h) :
    0 ≤ sourceContractionFactor θ m h := by unfold sourceContractionFactor; positivity

theorem sourceContractionFactor_lt_one (θ m h : ℝ) (hθ : 0 < θ) (hm : 0 < m) (hh : 0 < h) :
    sourceContractionFactor θ m h < 1 := by
  unfold sourceContractionFactor
  apply (inv_lt_one₀ (by positivity)).mpr
  have : 0 < (Real.sqrt 2 * θ / 64) * (Real.sqrt m * h) := by positivity
  linarith

/-- One step of the actual independently clock-averaged relative-density
transition contracts its genuine modified energy. Transport and ordinary heat
current estimates are conclusions of the imported analytic construction. The
only conditional analytic input is W12 for the actual dormant joint. -/
theorem sourcePhaseDensity_energy_contraction {μ : Measure E} [IsProbabilityMeasure μ]
    {h R m θ C : ℝ} (hh0 : 0 < h)
    (H : VarianceHeatFamily μ (3*(2*h^2)/4) R) (hR : 2*h^2 < R)
    (hm : ∀ v ∈ Icc (3*(2*h^2)/4) (2*h^2), H.source.lower v = m)
    (hm0 : 0 < m) (hm1 : m ≤ 1) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ (Real.sqrt 2/32)/32) (hC : 0 ≤ C)
    (hh : h ≤ 1/4) (hhC : h ≤ (Real.sqrt 2/32)/(8*(C/2+200)))
    (κ : Icc (0:ℝ) (1/2) → Kernel (GaussianPhase E) E)
    [∀ t, IsMarkovKernel (κ t)]
    (hκ : ∀ t, ConditionallyInvariant (stdGaussian E) (κ t))
    (hW : ∀ t, physicalDormantW12 (clockTransportFamily H (by positivity) hR)
      t (κ t) (hκ t) C (2*h^2))
    (hI : ∀ f, Integrable (fun t => sourceClockChannel H (by positivity) hR
      (Real.sqrt 2*h) (Real.sqrt m*h) (by positivity) κ hκ t f)
      (boundedClockLaw (1/2) (by norm_num)))
    (hIa : ∀ f, Integrable (fun t => (sourceClockChannel H (by positivity) hR
      (Real.sqrt 2*h) (Real.sqrt m*h) (by positivity) κ hκ t).adjoint f)
      (boundedClockLaw (1/2) (by norm_num)))
    (f : centered (((clockTransportFamily H (by positivity) hR).law 0).prod (stdGaussian E))) :
    quadraticEnergy (sourceCorrector H (by positivity) hR) (θ*Real.sqrt m)
      (sourcePhaseDensity H (by positivity) hR (Real.sqrt 2*h) (Real.sqrt m*h)
        (by positivity) κ hκ hI f) ≤
      sourceContractionFactor θ m h *
        quadraticEnergy (sourceCorrector H (by positivity) hR) (θ*Real.sqrt m) f := by
  have hA : 0 < 2*h^2 := by positivity
  let F := clockTransportFamily H hA hR
  let ell := Real.sqrt 2*h
  let Γ := Real.sqrt m*h
  let ε := θ*Real.sqrt m
  let Aop := sourceCorrector H hA hR
  let g : Lp ℝ 2 (gaussianPhaseMeasure (F.law 0)) := Kinetic.hiddenEmbedding (F.law 0) f
  have hg : mean (gaussianPhaseMeasure (F.law 0)) g = 0 :=
    (mean_hiddenEmbedding (F.law 0) f).trans f.property
  let gc : centered (gaussianPhaseMeasure (F.law 0)) := ⟨g,hg⟩
  have hgn : ‖g‖ = ‖(f : Lp ℝ 2 ((F.law 0).prod (stdGaussian E)))‖ :=
    (Kinetic.hiddenEmbedding (F.law 0)).norm_map f
  have hγ : Real.sqrt m ≤ 1 := (Real.sqrt_le_one).mpr hm1
  have hparam (t : ℝ) (ht : t ∈ Icc (0:ℝ) (1/2)) :=
    source_parameter_admissibility h (Real.sqrt m) θ t hh0.le hh
      (Real.sqrt_nonneg m) hγ hθ0 hθ ht.1 ht.2
  have hs2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hs0 := Real.sqrt_nonneg (2:ℝ)
  have hsmax : Real.sqrt 2 ≤ 2 := by nlinarith
  have hθq : θ ≤ 1/4 := by linarith
  have hθr : θ ≤ (192*Real.sqrt 2*(1/2:ℝ))⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ (by positivity : 0 < 192*Real.sqrt 2*(1/2:ℝ))).mpr
    have hx := mul_le_mul_of_nonneg_right hθ hs0
    nlinarith
  have hθc : θ ≤ (Real.sqrt 2*(1/2:ℝ)/16)/32 := by linarith
  have hhC' : h ≤ (Real.sqrt 2*(1/2:ℝ)/16)/(8*(C/2+200)) := by
    convert hhC using 1
    ring
  have hpos (v) : 0 ≤ quadraticEnergy Aop ε v :=
    (by positivity : 0 ≤ (3/8:ℝ)*‖v‖^2).trans
      (sourceCorrector_energy_bounds H hA hR hm θ hθ0 hθq v).1
  have hup (v) : quadraticEnergy Aop ε v ≤ ‖v‖^2 :=
    (sourceCorrector_energy_bounds H hA hR hm θ hθ0 hθq v).2.trans (by nlinarith [sq_nonneg ‖v‖])
  let Etr := fun t => quadraticEnergy (F.corrector t) ε
    (physicalFrameDensity F ell (1/2) (Real.sqrt 3/2) source_split_coefficients t g)
  let Rmicro := fun t => ‖physicalFrameMicro F ell (1/2) (Real.sqrt 3/2)
    source_split_coefficients t g‖^2
  have hEI : IntervalIntegrable Etr volume 0 (1/2) := by
    apply intervalIntegrable_of_continuousOn_Ioo_bounded (C := (5/8:ℝ)*‖g‖^2) (by norm_num)
    · exact (physicalFrameEnergy_continuousOn F ell (1/2) (Real.sqrt 3/2)
        source_split_coefficients ε g).mono Ioo_subset_Ico_self
    · intro t ht
      have hb := sourcePhysicalFrameEnergy_bounds H hA hR hm ell θ hθ0 hθq g t ⟨ht.1.le,ht.2⟩
      have hn : 0 ≤ Etr t := (by positivity : 0 ≤ (3/8:ℝ)*‖g‖^2).trans hb.1
      rw [Real.norm_eq_abs, abs_of_nonneg hn]
      exact hb.2
  have hRI : IntervalIntegrable Rmicro volume 0 (1/2) :=
    physicalFrameMicro_intervalIntegrable F ell (1/2) (Real.sqrt 3/2) source_split_coefficients g 0 (1/2)
  have hRmicro (t) (_ht : t ∈ Icc (0:ℝ) (1/2)) : 0 ≤ Rmicro t := sq_nonneg _
  have hbudget : ScalarTransportEnergyBudget (1/2) (quadraticEnergy Aop ε f)
      (‖(f : Lp ℝ 2 ((F.law 0).prod (stdGaussian E)))‖^2) (Real.sqrt 2*θ*Γ) Etr Rmicro := by
    intro t ht
    have hb := physicalTransportEnergy_integrated_L2 F ell ε (by positivity) (by positivity) t ht
      (fun u hu => by
        rw [clockTransportFamily_scale H hA hR u ⟨hu.1,hu.2.trans ht.2.le⟩]
        exact (hparam u ⟨hu.1,hu.2.trans ht.2.le⟩).2.2.2.2.2.2.1) gc
    change Etr t ≤ quadraticEnergy (F.corrector 0) ε g - ε*ell*(t-0)/8*‖g‖^2 +
      3*ε*ell*(∫ u in 0..t, Rmicro u) at hb
    rw [sourceCorrector_initial_energy H hA hR ε f, hgn] at hb
    dsimp only [ε,ell,Γ] at hb ⊢
    dsimp only [Etr,Rmicro] at hb ⊢
    convert hb using 1
    ring
  have hcollision (t : ℝ) (ht : t ∈ Ico (0:ℝ) (1/2)) :
      quadraticEnergy Aop ε
        ((sourceClockChannel H hA hR ell Γ (by positivity) κ hκ
          (clockTime (1/2) (by norm_num) t)).adjoint f) ≤
        Etr t - Γ*Rmicro t/32 + (8*θ^2*Γ+2*(C/2+200)*θ*h*Γ)*‖(f : Lp ℝ 2 ((F.law 0).prod (stdGaussian E)))‖^2 := by
    have ht' : t ∈ Icc (0:ℝ) (1/2) := ⟨ht.1,ht.2.le⟩
    have hct : clockTime (1/2) (by norm_num) t = ⟨t,ht'⟩ :=
      Subtype.ext (clockTime_eq (1/2) (by norm_num) t ht')
    rw [hct]
    have hc := sourceClock_collision_le H hA hR hm ell t ht' (κ ⟨t,ht'⟩) (hκ ⟨t,ht'⟩)
      Γ (by positivity) (hparam t ht').2.1 θ hθ0 C (hW ⟨t,ht'⟩)
      (hparam t ht').2.2.2.2.2.2.2 (hparam t ht').2.2.2.1 f
    dsimp only at hc
    have he : Etr t = quadraticEnergy (F.physicalCorrector ⟨t,ht'⟩) ε
        (physicalDensityTransport F ell (1/2) (Real.sqrt 3/2) source_split_coefficients ⟨t,ht'⟩ g) :=
      physicalFrameEnergy_eq F ell (1/2) (Real.sqrt 3/2) source_split_coefficients ε t ht g
    have hr : Rmicro t = ‖physicalDensityTransport F ell (1/2) (Real.sqrt 3/2) source_split_coefficients ⟨t,ht'⟩ g -
        gaussianPositionProjection (F.law t)
          (physicalDensityTransport F ell (1/2) (Real.sqrt 3/2) source_split_coefficients ⟨t,ht'⟩ g)‖^2 := by
      dsimp only [Rmicro]
      rw [physicalFrameMicro_apply,physicalFrameDensity_Ico F ell (1/2) (Real.sqrt 3/2)
        source_split_coefficients t ht,phaseUnitary_micro_norm]
    rw [he,hr]
    convert hc using 1 <;> simp only [Γ,ε,Aop,sourceCorrector,sourceClockChannel]
    first | rfl | ring
  have hhfinal := discretePhaseDensity_transport_clock_contraction (by norm_num : (0:ℝ)<1/2)
    F ell (1/2) (Real.sqrt 3/2) source_split_coefficients κ hκ (fun t => 2*h^2*(t:ℝ)^2)
    Γ (by positivity) (fun t => clockTransportFamily_heat_return H hA hR t t.property)
    hI hIa Aop ε hpos hup f θ (C/2+200) h hθ0 (by linarith) hθr hθc hhC'
    Etr Rmicro hEI hRI hRmicro hbudget hcollision
  convert hhfinal using 1 <;>
    simp only [sourceContractionFactor,Γ,Aop,ε,ell,sourcePhaseDensity,sourcePhaseOperator] <;>
      first | rfl | ring

/-- Both genuine adjoint transitions have the same iterated ordinary L2 rate.
The energy contraction is used for densities; test functions inherit this norm
bound through the proved Hilbert-adjoint identity. -/
theorem sourcePhase_mixing {μ : Measure E} [IsProbabilityMeasure μ]
    {h R m θ C : ℝ} (hh0 : 0 < h)
    (H : VarianceHeatFamily μ (3*(2*h^2)/4) R) (hR : 2*h^2 < R)
    (hm : ∀ v ∈ Icc (3*(2*h^2)/4) (2*h^2), H.source.lower v = m)
    (hm0 : 0 < m) (hm1 : m ≤ 1) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ (Real.sqrt 2/32)/32) (hC : 0 ≤ C)
    (hh : h ≤ 1/4) (hhC : h ≤ (Real.sqrt 2/32)/(8*(C/2+200)))
    (κ : Icc (0:ℝ) (1/2) → Kernel (GaussianPhase E) E)
    [∀ t, IsMarkovKernel (κ t)]
    (hκ : ∀ t, ConditionallyInvariant (stdGaussian E) (κ t))
    (hW : ∀ t, physicalDormantW12 (clockTransportFamily H (by positivity) hR)
      t (κ t) (hκ t) C (2*h^2))
    (hI : ∀ f, Integrable (fun t => sourceClockChannel H (by positivity) hR
      (Real.sqrt 2*h) (Real.sqrt m*h) (by positivity) κ hκ t f)
      (boundedClockLaw (1/2) (by norm_num)))
    (hIa : ∀ f, Integrable (fun t => (sourceClockChannel H (by positivity) hR
      (Real.sqrt 2*h) (Real.sqrt m*h) (by positivity) κ hκ t).adjoint f)
      (boundedClockLaw (1/2) (by norm_num)))
    (k : ℕ) :
    ‖sourceCenteredPhaseDensity H (by positivity) hR (Real.sqrt 2*h) (Real.sqrt m*h)
      (by positivity) κ hκ hI ^ k‖ ≤ Real.sqrt ((5/3:ℝ)*(sourceContractionFactor θ m h)^k) ∧
    ‖sourceCenteredPhaseOperator H (by positivity) hR (Real.sqrt 2*h) (Real.sqrt m*h)
      (by positivity) κ hκ hI ^ k‖ ≤ Real.sqrt ((5/3:ℝ)*(sourceContractionFactor θ m h)^k) := by
  have hA : 0 < 2*h^2 := by positivity
  let F := clockTransportFamily H hA hR
  let energy := fun f : centered ((F.law 0).prod (stdGaussian E)) =>
    quadraticEnergy (sourceCorrector H hA hR) (θ*Real.sqrt m) f
  have hθq : θ ≤ 1/4 := by
    have hs2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
    have hs0 := Real.sqrt_nonneg (2:ℝ)
    have hsmax : Real.sqrt 2 ≤ 2 := by nlinarith
    linarith
  have hstep (f : centered ((F.law 0).prod (stdGaussian E))) :=
    sourcePhaseDensity_energy_contraction hh0 H hR hm hm0 hm1 hθ0 hθ hC hh hhC κ hκ hW hI hIa f
  have hb := centeredDiscretePhase_mixing_of_energy (by norm_num : (0:ℝ)<1/2) F
    (Real.sqrt 2*h) (1/2) (Real.sqrt 3/2) source_split_coefficients κ hκ
    (fun t => 2*h^2*(t:ℝ)^2) (Real.sqrt m*h) (by positivity)
    (fun t => clockTransportFamily_heat_return H hA hR t t.property) hI
    energy (3/8) (5/8) (sourceContractionFactor θ m h) (by norm_num) (by norm_num)
    (sourceContractionFactor_nonneg θ m h hθ0 hh0.le)
    (fun f => (sourceCorrector_energy_bounds H hA hR hm θ hθ0 hθq f).1)
    (fun f => (sourceCorrector_energy_bounds H hA hR hm θ hθ0 hθq f).2)
    hstep k
  norm_num only [show (5/8:ℝ)/(3/8) = 5/3 by norm_num] at hb
  exact hb

/-- The curvature parameter gives exactly the manuscript's dimensionless rate. -/
theorem source_rate_eq (κ h : ℝ) :
    Real.sqrt ((κ+2*h^2)⁻¹)*h = h/Real.sqrt (κ+2*h^2) := by
  rw [Real.sqrt_inv]
  ring

/-- Rewriting the proved factor with the source curvature value. -/
theorem sourceContractionFactor_source_curvature (θ κ h : ℝ) :
    sourceContractionFactor θ ((κ+2*h^2)⁻¹) h =
      (1+(Real.sqrt 2*θ/64)*(h/Real.sqrt (κ+2*h^2)))⁻¹ := by
  unfold sourceContractionFactor
  rw [source_rate_eq]

end AcceleratedLogConcave.Kinetic
