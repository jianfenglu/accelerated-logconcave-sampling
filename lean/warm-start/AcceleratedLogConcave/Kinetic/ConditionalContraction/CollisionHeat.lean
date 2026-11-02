import AcceleratedLogConcave.Kinetic.ConditionalContraction.Collision
import AcceleratedLogConcave.Kinetic.Reheating

/-! Actual collision energy with the ordinary heat-current obligation discharged.
Only the separately scheduled dormant coupling estimate W12 remains explicit. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.ConditionalContraction
open Analysis.Poisson Reheating
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The named ordinary heat intermediate follows from the actual smooth heat
family and its genuine Poisson correctors. -/
theorem ordinaryHeatCurrentBound_of_heat_family {a b : ℝ} (F : ReferencePoissonFamily E a b)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
    (hscale : ∀ t ∈ Ioo a b, F.scale t = -(1/2:ℝ)) (t : ℝ) (ht : t ∈ Ico a b) :
    OrdinaryHeatCurrentBound (F.law a) (t-a) (F.potential a) (F.potential t)
      (F.potential_C2 a) (F.potential_C2 t) (F.integrable a F.leftTime.property)
      (F.integrable t ⟨ht.1,ht.2.le⟩) (F.gibbs_law a F.leftTime.property)
      ((hheat t ⟨ht.1,ht.2.le⟩).symm.trans (F.gibbs_law t ⟨ht.1,ht.2.le⟩))
      (F.lower a) (F.lower t) 1 (F.lower_pos a F.leftTime.property)
      (F.lower_pos t ⟨ht.1,ht.2.le⟩) (F.hessian_lower a F.leftTime.property)
      (by simpa only [one_mul] using F.hessian_upper a F.leftTime.property)
      (F.hessian_lower t ⟨ht.1,ht.2.le⟩)
      (by simpa only [one_mul] using F.hessian_upper t ⟨ht.1,ht.2.le⟩) := by
  intro g
  exact ordinaryHeatDensity_current_le F hheat hscale t ht g

/-- The complete physical collision estimate. The heat-current estimate is
proved; the explicitly named dormant W12 estimate remains a downstream input. -/
theorem collision_energy_le {a b : ℝ} (F : ReferencePoissonFamily E a b)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
    (hscale : ∀ t ∈ Ioo a b, F.scale t = -(1/2:ℝ)) (t : ℝ) (ht : t ∈ Ico a b)
    {Ω : Type*} [MeasurableSpace Ω] {η : Measure Ω} {p q : Ω → GaussianPhase E}
    (hp : MeasurePreserving p η (gaussianPhaseMeasure (F.law a)))
    (hq : MeasurePreserving q η (gaussianPhaseMeasure (F.law a)))
    (hpos : ∀ z, (p z).1.1 = (q z).1.1)
    (Γ : ℝ) (hΓ : 0 ≤ Γ) (hΓ' : Γ ≤ 1/2)
    (θ : ℝ) (hθ : 0 ≤ θ) (C δ : ℝ)
    (hW : DormantW12 (F.law a) hp hq (F.potential a) (F.potential_C2 a)
      (F.integrable a F.leftTime.property) (F.gibbs_law a F.leftTime.property)
      (F.lower a) 1 (F.lower_pos a F.leftTime.property) (F.hessian_lower a F.leftTime.property)
      (by simpa only [one_mul] using F.hessian_upper a F.leftTime.property) C δ)
    (hsmall : (θ*Real.sqrt (F.lower a))*Real.sqrt (t-a) ≤ 1/24)
    (f : Lp ℝ 2 (gaussianPhaseMeasure (F.law a))) :
    quadraticEnergy (reheatingTargetCorrector F hheat t ⟨ht.1,ht.2.le⟩)
      (θ*Real.sqrt (F.lower a)) (collisionDensity (F.law a) (t-a) hp hq Γ hΓ f) ≤
      quadraticEnergy (F.physicalCorrector F.leftTime) (θ*Real.sqrt (F.lower a)) f -
        (Γ/32)*‖f-gaussianPositionProjection (F.law a) f‖^2 +
        (8*θ^2*Γ + (C/2)*(θ*Real.sqrt (F.lower a))*δ +
          100*((θ*Real.sqrt (F.lower a))+(θ*Real.sqrt (F.lower a))^2)*(t-a))*‖f‖^2 := by
  exact collision_energy_le_of_ordinary_current (F.law a) (t-a) (F.potential a) (F.potential t)
    (F.potential_C2 a) (F.potential_C2 t) (F.integrable a F.leftTime.property)
    (F.integrable t ⟨ht.1,ht.2.le⟩) (F.gibbs_law a F.leftTime.property)
    ((hheat t ⟨ht.1,ht.2.le⟩).symm.trans (F.gibbs_law t ⟨ht.1,ht.2.le⟩))
    (F.lower a) (F.lower t) 1 (F.lower_pos a F.leftTime.property)
    (F.lower_pos t ⟨ht.1,ht.2.le⟩) (F.hessian_lower a F.leftTime.property)
    (by simpa only [one_mul] using F.hessian_upper a F.leftTime.property)
    (F.hessian_lower t ⟨ht.1,ht.2.le⟩)
    (by simpa only [one_mul] using F.hessian_upper t ⟨ht.1,ht.2.le⟩)
    hp hq hpos (sub_nonneg.mpr ht.1) Γ hΓ hΓ' θ hθ C δ hW
    (ordinaryHeatCurrentBound_of_heat_family F hheat hscale t ht) hsmall f

/-- Source-scale collision energy with the explicit coefficient `C/2+200`;
ordinary heat current is fully discharged by the actual heat family. -/
theorem collision_energy_source_le {a b : ℝ} (F : ReferencePoissonFamily E a b)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
    (hscale : ∀ t ∈ Ioo a b, F.scale t = -(1/2:ℝ)) (t : ℝ) (ht : t ∈ Ico a b)
    {Ω : Type*} [MeasurableSpace Ω] {η : Measure Ω} {p q : Ω → GaussianPhase E}
    (hp : MeasurePreserving p η (gaussianPhaseMeasure (F.law a)))
    (hq : MeasurePreserving q η (gaussianPhaseMeasure (F.law a)))
    (hpos : ∀ z, (p z).1.1 = (q z).1.1)
    (Γ : ℝ) (hΓ : 0 ≤ Γ) (hΓ' : Γ ≤ 1/2)
    (θ : ℝ) (hθ : 0 ≤ θ) (C δ : ℝ)
    (hW : DormantW12 (F.law a) hp hq (F.potential a) (F.potential_C2 a)
      (F.integrable a F.leftTime.property) (F.gibbs_law a F.leftTime.property)
      (F.lower a) 1 (F.lower_pos a F.leftTime.property) (F.hessian_lower a F.leftTime.property)
      (by simpa only [one_mul] using F.hessian_upper a F.leftTime.property) C δ)
    (hsmall : (θ*Real.sqrt (F.lower a))*Real.sqrt (t-a) ≤ 1/24)
    (hε : θ*Real.sqrt (F.lower a) ≤ 1) (hδ : t-a ≤ δ)
    (f : Lp ℝ 2 (gaussianPhaseMeasure (F.law a))) :
    quadraticEnergy (reheatingTargetCorrector F hheat t ⟨ht.1,ht.2.le⟩)
      (θ*Real.sqrt (F.lower a)) (collisionDensity (F.law a) (t-a) hp hq Γ hΓ f) ≤
      quadraticEnergy (F.physicalCorrector F.leftTime) (θ*Real.sqrt (F.lower a)) f -
        (Γ/32)*‖f-gaussianPositionProjection (F.law a) f‖^2 +
        (8*θ^2*Γ + (C/2+200)*θ*Real.sqrt (F.lower a)*δ)*‖f‖^2 := by
  exact collision_energy_source_le_of_ordinary_current (F.law a) (t-a) (F.potential a) (F.potential t)
    (F.potential_C2 a) (F.potential_C2 t) (F.integrable a F.leftTime.property)
    (F.integrable t ⟨ht.1,ht.2.le⟩) (F.gibbs_law a F.leftTime.property)
    ((hheat t ⟨ht.1,ht.2.le⟩).symm.trans (F.gibbs_law t ⟨ht.1,ht.2.le⟩))
    (F.lower a) (F.lower t) 1 (F.lower_pos a F.leftTime.property)
    (F.lower_pos t ⟨ht.1,ht.2.le⟩) (F.hessian_lower a F.leftTime.property)
    (by simpa only [one_mul] using F.hessian_upper a F.leftTime.property)
    (F.hessian_lower t ⟨ht.1,ht.2.le⟩)
    (by simpa only [one_mul] using F.hessian_upper t ⟨ht.1,ht.2.le⟩)
    hp hq hpos (sub_nonneg.mpr ht.1) Γ hΓ hΓ' θ hθ C δ hW
    (ordinaryHeatCurrentBound_of_heat_family F hheat hscale t ht) hsmall hε hδ f

end AcceleratedLogConcave.Kinetic.ConditionalContraction
