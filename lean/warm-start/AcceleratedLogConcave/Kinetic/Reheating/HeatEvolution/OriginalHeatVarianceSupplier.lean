import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.VarianceFamily
import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.OriginalHeatLaw
import AcceleratedLogConcave.Gibbs.HeatContinuityEquation

/-!

-/
noncomputable section
open MeasureTheory Set
namespace AcceleratedLogConcave.Kinetic.Reheating
open Gibbs
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

def originalVarianceHeatFamily {F : E → ℝ} {κ A R : ℝ}
    (hF : ContDiff ℝ 2 F) (hκ : 0 < κ) (hA : 0 < A) (hR : A < R)
    (hlo : ∀ z v, κ⁻¹ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v)
    (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ ‖v‖ ^ 2) :
    VarianceHeatFamily (volume.tilted (fun x => -F x)) (3 * A / 4) R where
  source := (originalHeatEvolutionData_of_hessian_lower hF (inv_pos.mpr hκ) hA hlo).toLocal
    hF hκ hA hR hlo hup
  scale_eq := fun _ _ => rfl
  heat_law := original_heat_law_envelope hF (inv_pos.mpr hκ) hA hlo

theorem originalVarianceHeatFamily_lower_eq {F : E → ℝ} {κ A R : ℝ}
    (hF : ContDiff ℝ 2 F) (hκ : 0 < κ) (hA : 0 < A) (hR : A < R)
    (hlo : ∀ z v, κ⁻¹ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v)
    (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ ‖v‖ ^ 2)
    (t : ℝ) (ht : t ∈ Icc (3 * A / 4) A) :
    (originalVarianceHeatFamily hF hκ hA hR hlo hup).source.lower t = (κ + A)⁻¹ :=
  OriginalHeatEvolutionData.toLocal_lower_eq _ hF hκ hA hR hlo hup t ht

end AcceleratedLogConcave.Kinetic.Reheating
