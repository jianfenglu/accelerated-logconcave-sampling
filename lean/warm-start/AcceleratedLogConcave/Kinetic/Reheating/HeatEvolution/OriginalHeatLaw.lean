import AcceleratedLogConcave.Kinetic.Reheating.HeatChannel
import AcceleratedLogConcave.Gibbs.HeatLawIdentification

/-!

-/
noncomputable section
open MeasureTheory Set
namespace AcceleratedLogConcave.Kinetic.Reheating
open Gibbs
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem original_heat_law {F : E → ℝ} {m t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v)
    (hI : Integrable (fun z => Real.exp (-F z))) :
    volume.tilted (fun x => -heatPotential F t x) =
      heatedLaw (volume.tilted (fun x => -F x)) t := by
  simpa only [heatedLaw] using
    tilted_heatPotential_eq_gaussian_product_map hF hm ht hlo hI

theorem original_heat_law_envelope {F : E → ℝ} {m A R : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 < m) (hA : 0 < A)
    (hlo : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v) :
    ∀ t ∈ Icc (3 * A / 4) R,
      volume.tilted (fun x => -heatPotential F t x) =
        heatedLaw (volume.tilted (fun x => -F x)) t := by
  simpa only [heatedLaw] using
    tilted_heatPotential_eq_gaussian_product_map_envelope hF hm hA hlo

end AcceleratedLogConcave.Kinetic.Reheating
