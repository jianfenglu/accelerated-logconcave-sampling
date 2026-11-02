import AcceleratedLogConcave.Kinetic.Mixing.PhysicalFactorization
import AcceleratedLogConcave.Kinetic.ConditionalContraction.CollisionHeat
import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.ClockTransportFamily

/-! Actual returning-clock collision. Its ordinary heat-current estimate comes
from the same variance-indexed source family. Only dormant W12 is an analytic
input; all channels, losses, and the returned-law energy are constructed. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set InnerProductSpace
namespace AcceleratedLogConcave.Kinetic
open Analysis.Poisson Reheating ConditionalContraction
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Equal target laws give the same genuine channel-adjoint corrector energy. -/
private theorem channel_energy_congr_measure (μ ν : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (he : μ = ν)
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {η : Measure Ω} {ξ : Measure X} {p : Ω → X} {q : Ω → E×E}
    (hp : MeasurePreserving p η ξ)
    (hqμ : MeasurePreserving q η (μ.prod (stdGaussian E)))
    (hqν : MeasurePreserving q η (ν.prod (stdGaussian E)))
    (V : E → ℝ) (hV : ContDiff ℝ 2 V) (hI : Integrable (fun x => Real.exp (-V x)))
    (hμ : μ = volume.tilted (fun x => -V x)) (hν : ν = volume.tilted (fun x => -V x))
    (m L : ℝ) (hm : 0 < m)
    (hl : ∀ x v, m*‖v‖^2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hu : ∀ x v, fderiv ℝ (fderiv ℝ V) x v v ≤ L*‖v‖^2)
    (ε : ℝ) (f : Lp ℝ 2 ξ) :
    quadraticEnergy (visibleCorrector μ V hV hI hμ m L hm hl hu) ε
      ((referenceChannel hp hqμ).adjoint f) =
    quadraticEnergy (visibleCorrector ν V hV hI hν m L hm hl hu) ε
      ((referenceChannel hp hqν).adjoint f) := by
  subst ν
  rfl

/-- W12 for the actual dormant joint law in physical coordinates. -/
def physicalDormantW12 {a b : ℝ} (F : ReferencePoissonFamily E a b) (t : Icc a b)
    (κ : Kernel (GaussianPhase E) E) [IsMarkovKernel κ]
    (hκ : ConditionallyInvariant (stdGaussian E) κ) (C δ : ℝ) : Prop :=
  DormantW12 (F.law t)
    (physicalDormantOld_preserving (1/2) (Real.sqrt 3/2) source_split_coefficients (F.law t) κ)
    (physicalDormantNew_preserving (1/2) (Real.sqrt 3/2) source_split_coefficients (F.law t) κ hκ)
    (F.potential t) (F.potential_C2 t) (F.integrable t t.property) (F.gibbs_law t t.property)
    (F.lower t) 1 (F.lower_pos t t.property) (F.hessian_lower t t.property)
    (by simpa only [one_mul] using F.hessian_upper t t.property) C δ

/-- The named current intermediate used only to connect the proved collision
algebra to a returning family. It is discharged below for actual source clocks. -/
def returningOrdinaryCurrent {a b : ℝ} (F : ReferencePoissonFamily E a b)
    (t : Icc a b) (τ : ℝ) (hreturn : heatedLaw (F.law t) τ = F.law a) : Prop :=
  OrdinaryHeatCurrentBound (F.law t) τ (F.potential t) (F.potential a)
    (F.potential_C2 t) (F.potential_C2 a) (F.integrable t t.property)
    (F.integrable a F.leftTime.property) (F.gibbs_law t t.property)
    (hreturn.trans (F.gibbs_law a F.leftTime.property))
    (F.lower t) (F.lower a) 1 (F.lower_pos t t.property)
    (F.lower_pos a F.leftTime.property) (F.hessian_lower t t.property)
    (by simpa only [one_mul] using F.hessian_upper t t.property)
    (F.hessian_lower a F.leftTime.property)
    (by simpa only [one_mul] using F.hessian_upper a F.leftTime.property)

/-- Actual returning-channel adjoint energy, with the current intermediate
explicit only in this reusable algebraic bridge. -/
theorem returningClock_collision_le_of_current {a b : ℝ} (F : ReferencePoissonFamily E a b)
    (ell : ℝ) (t : Icc a b)
    (κ : Kernel (GaussianPhase E) E) [IsMarkovKernel κ]
    (hκ : ConditionallyInvariant (stdGaussian E) κ)
    (τ Γ : ℝ) (hτ : 0 ≤ τ) (hΓ : 0 ≤ Γ) (hΓ' : Γ ≤ 1/2)
    (hreturn : heatedLaw (F.law t) τ = F.law a)
    (θ : ℝ) (hθ : 0 ≤ θ) (C δ : ℝ)
    (hW : physicalDormantW12 F t κ hκ C δ)
    (hcurrent : returningOrdinaryCurrent F t τ hreturn)
    (hsmall : (θ*Real.sqrt (F.lower t))*Real.sqrt τ ≤ 1/24)
    (hε : θ*Real.sqrt (F.lower t) ≤ 1) (hδ : τ ≤ δ)
    (f : Lp ℝ 2 ((F.law a).prod (stdGaussian E))) :
    let g := physicalDensityTransport F ell (1/2) (Real.sqrt 3/2) source_split_coefficients t
      (Kinetic.hiddenEmbedding (F.law a) f)
    quadraticEnergy (phaseVisibleCorrector F a F.leftTime.property) (θ*Real.sqrt (F.lower t))
      ((returningClockChannel F ell t (1/2) (Real.sqrt 3/2) source_split_coefficients
        κ hκ τ Γ hΓ hreturn).adjoint f) ≤
      quadraticEnergy (F.physicalCorrector t) (θ*Real.sqrt (F.lower t)) g -
        (Γ/32)*‖g-gaussianPositionProjection (F.law t) g‖^2 +
        (8*θ^2*Γ+(C/2+200)*θ*Real.sqrt (F.lower t)*δ)*‖f‖^2 := by
  dsimp only
  let g := physicalDensityTransport F ell (1/2) (Real.sqrt 3/2) source_split_coefficients t
    (Kinetic.hiddenEmbedding (F.law a) f)
  let hp := physicalDormantOld_preserving (1/2) (Real.sqrt 3/2) source_split_coefficients (F.law t) κ
  let hq := physicalDormantNew_preserving (1/2) (Real.sqrt 3/2) source_split_coefficients (F.law t) κ hκ
  have h := collision_energy_source_le_of_ordinary_current (F.law t) τ
    (F.potential t) (F.potential a) (F.potential_C2 t) (F.potential_C2 a)
    (F.integrable t t.property) (F.integrable a F.leftTime.property)
    (F.gibbs_law t t.property) (hreturn.trans (F.gibbs_law a F.leftTime.property))
    (F.lower t) (F.lower a) 1 (F.lower_pos t t.property)
    (F.lower_pos a F.leftTime.property) (F.hessian_lower t t.property)
    (by simpa only [one_mul] using F.hessian_upper t t.property)
    (F.hessian_lower a F.leftTime.property)
    (by simpa only [one_mul] using F.hessian_upper a F.leftTime.property)
    hp hq (physicalDormant_position (1/2) (Real.sqrt 3/2) source_split_coefficients)
    hτ Γ hΓ hΓ' θ hθ C δ hW hcurrent hsmall hε hδ g
  have hg : ‖g‖ = ‖f‖ := (physicalDensityTransport F ell (1/2) (Real.sqrt 3/2)
    source_split_coefficients t).norm_map _ |>.trans ((Kinetic.hiddenEmbedding (F.law a)).norm_map f)
  rw [hg] at h
  have hout : collisionDensity (F.law t) τ hp hq Γ hΓ g =
      fixedClockDensity F ell t (1/2) (Real.sqrt 3/2) source_split_coefficients κ hκ τ Γ hΓ f := by
    exact (fixedClockDensity_physical_factorization F ell t κ hκ τ Γ hΓ f).symm
  rw [hout] at h
  have he := channel_energy_congr_measure (heatedLaw (F.law t) τ) (F.law a) hreturn
    (fixedClockInput_measurePreserving F ell t (1/2) (Real.sqrt 3/2) source_split_coefficients κ)
    (fixedClockOutput_measurePreserving F t (1/2) (Real.sqrt 3/2) source_split_coefficients κ hκ τ Γ hΓ)
    (by
      rw [← hreturn]
      exact fixedClockOutput_measurePreserving F t (1/2)
        (Real.sqrt 3/2) source_split_coefficients κ hκ τ Γ hΓ)
    (F.potential a) (F.potential_C2 a) (F.integrable a F.leftTime.property)
    (hreturn.trans (F.gibbs_law a F.leftTime.property)) (F.gibbs_law a F.leftTime.property)
    (F.lower a) 1 (F.lower_pos a F.leftTime.property) (F.hessian_lower a F.leftTime.property)
    (by simpa only [one_mul] using F.hessian_upper a F.leftTime.property)
    (θ*Real.sqrt (F.lower t)) f
  exact he ▸ h

/-- The actual source heat family discharges the ordinary current obligation at
 every clock, including the initial clock of zero elapsed reheating. -/
theorem sourceClock_ordinaryCurrent {μ : Measure E} [IsProbabilityMeasure μ] {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ρ : ℝ) (hρ : ρ ∈ Icc (0:ℝ) (1/2)) :
    returningOrdinaryCurrent (clockTransportFamily H hA hR) ⟨ρ,hρ⟩ (A*ρ^2)
      (clockTransportFamily_heat_return H hA hR ρ hρ) := by
  have h := ordinaryHeatCurrentBound_of_heat_family (clockReheatFamily H hA hR ρ hρ)
    (clockReheatFamily_heat H hA hR ρ hρ) (clockReheatFamily_scale H hA hR ρ hρ)
    (A*ρ^2) (clockReheatFamily_endpoint hA hR hρ)
  unfold returningOrdinaryCurrent
  simpa only [sub_zero, clockReheatFamily_initial_eq_transport_law,
    clockReheatFamily_initial_eq_transport_potential, clockReheatFamily_final_eq_transport_potential,
    clockReheatFamily_initial_eq_transport_lower, clockReheatFamily_final_eq_transport_lower] using h

/-- One fixed curvature witness on the executed variance interval gives one
energy parameter across all clocks. The larger endpoint `R` provides regularity
room only; its curvature witness need not equal `m` beyond `A`. -/
theorem clockTransportFamily_lower_eq {μ : Measure E} {A R m : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (hm : ∀ v ∈ Icc (3*A/4) A, H.source.lower v = m)
    (ρ : ℝ) (hρ : ρ ∈ Icc (0:ℝ) (1/2)) :
    (clockTransportFamily H hA hR).lower ρ = m := by
  apply hm
  exact ⟨(VarianceHeatFamily.clock_segment hA hR hρ).1.1, by
    nlinarith [mul_nonneg hA.le (sq_nonneg ρ)]⟩

/-- Source-faithful collision bound for the actual returning-clock density
operator. There is no heat-current or collision-estimate premise. The sole
remaining analytic input is W12 for the prescribed physical dormant joint. -/
theorem sourceClock_collision_le {μ : Measure E} [IsProbabilityMeasure μ] {A R m : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (hm : ∀ v ∈ Icc (3*A/4) A, H.source.lower v = m)
    (ell ρ : ℝ) (hρ : ρ ∈ Icc (0:ℝ) (1/2))
    (κ : Kernel (GaussianPhase E) E) [IsMarkovKernel κ]
    (hκ : ConditionallyInvariant (stdGaussian E) κ)
    (Γ : ℝ) (hΓ : 0 ≤ Γ) (hΓ' : Γ ≤ 1/2)
    (θ : ℝ) (hθ : 0 ≤ θ) (C : ℝ)
    (hW : physicalDormantW12 (clockTransportFamily H hA hR) ⟨ρ,hρ⟩ κ hκ C A)
    (hsmall : (θ*Real.sqrt m)*Real.sqrt (A*ρ^2) ≤ 1/24)
    (hε : θ*Real.sqrt m ≤ 1)
    (f : Lp ℝ 2 (((clockTransportFamily H hA hR).law 0).prod (stdGaussian E))) :
    let T := clockTransportFamily H hA hR
    let g := physicalDensityTransport T ell (1/2) (Real.sqrt 3/2) source_split_coefficients ⟨ρ,hρ⟩
      (Kinetic.hiddenEmbedding (T.law 0) f)
    quadraticEnergy (phaseVisibleCorrector T 0 T.leftTime.property) (θ*Real.sqrt m)
      ((returningClockChannel T ell ⟨ρ,hρ⟩ (1/2) (Real.sqrt 3/2) source_split_coefficients
        κ hκ (A*ρ^2) Γ hΓ (clockTransportFamily_heat_return H hA hR ρ hρ)).adjoint f) ≤
      quadraticEnergy (T.physicalCorrector ⟨ρ,hρ⟩) (θ*Real.sqrt m) g -
        (Γ/32)*‖g-gaussianPositionProjection (T.law ρ) g‖^2 +
        (8*θ^2*Γ+(C/2+200)*θ*Real.sqrt m*A)*‖f‖^2 := by
  have hl := clockTransportFamily_lower_eq H hA hR hm ρ hρ
  have hsmall' : (θ*Real.sqrt ((clockTransportFamily H hA hR).lower ρ))*
      Real.sqrt (A*ρ^2) ≤ 1/24 := by simpa only [hl] using hsmall
  have hε' : θ*Real.sqrt ((clockTransportFamily H hA hR).lower ρ) ≤ 1 := by
    simpa only [hl] using hε
  have hδ : A*ρ^2 ≤ A := by
    have hs : ρ^2 ≤ 1 := by nlinarith [hρ.1,hρ.2]
    nlinarith [mul_le_mul_of_nonneg_left hs hA.le]
  have h := returningClock_collision_le_of_current (clockTransportFamily H hA hR) ell ⟨ρ,hρ⟩
    κ hκ (A*ρ^2) Γ (mul_nonneg hA.le (sq_nonneg ρ)) hΓ hΓ'
    (clockTransportFamily_heat_return H hA hR ρ hρ) θ hθ C A hW
    (sourceClock_ordinaryCurrent H hA hR ρ hρ) hsmall' hε' hδ f
  simpa only [hl] using h

end AcceleratedLogConcave.Kinetic
