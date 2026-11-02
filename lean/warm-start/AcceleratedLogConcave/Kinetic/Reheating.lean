import AcceleratedLogConcave.Kinetic.Reheating.Current
import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.OrdinaryCurrent

/-! Actual correlated Gaussian reheating and its modified-energy estimate.
The ordinary heat-current obligation is discharged by the genuine compact-core
heat evolution and continuity extension to arbitrary L2 input. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The physical target corrector on the actual heated observation law. -/
def reheatingTargetCorrector {a b : ℝ} (F : ReferencePoissonFamily E a b)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
    (t : ℝ) (ht : t ∈ Icc a b) :
    Lp ℝ 2 ((heatedLaw (F.law a) (t-a)).prod (stdGaussian E)) →L[ℝ]
      Lp ℝ 2 ((heatedLaw (F.law a) (t-a)).prod (stdGaussian E)) :=
  visibleCorrector (heatedLaw (F.law a) (t-a)) (F.potential t) (F.potential_C2 t)
    (F.integrable t ht) ((hheat t ht).symm.trans (F.gibbs_law t ht))
    (F.lower t) 1 (F.lower_pos t ht) (F.hessian_lower t ht)
    (by simpa only [one_mul] using F.hessian_upper t ht)

/-- The actual correlated reheating current for every phase L2 input, with the
source constants 7 and 3 and no assumed current estimate. -/
theorem reheating_current_le {a b : ℝ} (F : ReferencePoissonFamily E a b)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
    (hscale : ∀ t ∈ Ioo a b, F.scale t = -(1/2:ℝ))
    (t : ℝ) (ht : t ∈ Ico a b) (g : Lp ℝ 2 (gaussianPhaseMeasure (F.law a))) :
    let v := reheatingDensity (F.law a) (t-a) g
    let D := ‖g‖^2-‖v‖^2
    |inner ℝ (reheatingTargetCorrector F hheat t ⟨ht.1,ht.2.le⟩ v) v -
      inner ℝ (F.physicalCorrector F.leftTime g) g| ≤
      ((t-a)/4)*‖g‖^2 + 7*Real.sqrt ((t-a)*D)*‖g‖ + 3*Real.sqrt (t-a)*D := by
  apply reheating_current_le_of_ordinary_current (F.law a) (t-a) (sub_nonneg.mpr ht.1)
    (F.potential a) (F.potential t) (F.potential_C2 a) (F.potential_C2 t)
    (F.integrable a F.leftTime.property) (F.integrable t ⟨ht.1,ht.2.le⟩)
    (F.gibbs_law a F.leftTime.property)
    ((hheat t ⟨ht.1,ht.2.le⟩).symm.trans (F.gibbs_law t ⟨ht.1,ht.2.le⟩))
    (F.lower a) (F.lower t) 1 (F.lower_pos a F.leftTime.property)
    (F.lower_pos t ⟨ht.1,ht.2.le⟩) (F.hessian_lower a F.leftTime.property)
    (by simpa only [one_mul] using F.hessian_upper a F.leftTime.property)
    (F.hessian_lower t ⟨ht.1,ht.2.le⟩)
    (by simpa only [one_mul] using F.hessian_upper t ⟨ht.1,ht.2.le⟩) _ g
  intro v
  exact ordinaryHeatDensity_current_le F hheat hscale t ht v

/-- Source reheating energy with `C_H = 100`, proved for the actual correlated
Gaussian channel and actual weighted Poisson correctors. The target time is
inside the supplied smooth source window. -/
theorem reheating_energy_le {a b : ℝ} (F : ReferencePoissonFamily E a b)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
    (hscale : ∀ t ∈ Ioo a b, F.scale t = -(1/2:ℝ))
    (t : ℝ) (ht : t ∈ Ico a b)
    (ε : ℝ) (hε : 0 ≤ ε) (hsmall : ε*Real.sqrt (t-a) ≤ 1/24)
    (g : Lp ℝ 2 (gaussianPhaseMeasure (F.law a))) :
    quadraticEnergy (reheatingTargetCorrector F hheat t ⟨ht.1,ht.2.le⟩) ε
      (reheatingDensity (F.law a) (t-a) g) ≤
      quadraticEnergy (F.physicalCorrector F.leftTime) ε g -
        (‖g‖^2-‖reheatingDensity (F.law a) (t-a) g‖^2)/4 +
        100*(ε+ε^2)*(t-a)*‖g‖^2 := by
  apply reheating_energy_le_of_ordinary_current (F.law a) (t-a) (sub_nonneg.mpr ht.1)
    (F.potential a) (F.potential t) (F.potential_C2 a) (F.potential_C2 t)
    (F.integrable a F.leftTime.property) (F.integrable t ⟨ht.1,ht.2.le⟩)
    (F.gibbs_law a F.leftTime.property)
    ((hheat t ⟨ht.1,ht.2.le⟩).symm.trans (F.gibbs_law t ⟨ht.1,ht.2.le⟩))
    (F.lower a) (F.lower t) 1 (F.lower_pos a F.leftTime.property)
    (F.lower_pos t ⟨ht.1,ht.2.le⟩) (F.hessian_lower a F.leftTime.property)
    (by simpa only [one_mul] using F.hessian_upper a F.leftTime.property)
    (F.hessian_lower t ⟨ht.1,ht.2.le⟩)
    (by simpa only [one_mul] using F.hessian_upper t ⟨ht.1,ht.2.le⟩) _ ε hε hsmall g
  intro v
  exact ordinaryHeatDensity_current_le F hheat hscale t ht v

end AcceleratedLogConcave.Kinetic.Reheating
