import AcceleratedLogConcave.Gibbs.ProductTilt
import AcceleratedLogConcave.Numerics.CenterMeanPhaseCoordinates
import AcceleratedLogConcave.Kinetic.Reheating.GaussianPoincare
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Original phase Gibbs law with an explicitly transported Haar reference.
No product-norm volume is silently identified with Hilbert normed volume. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Conditional CenteringFlowLp
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))
local notation "P" => WithLp 2 (E × E)

/-- The actual continuous linear change from product coordinates to Euclidean phase coordinates. -/
def phaseProductEquiv : (E × E) ≃L[ℝ] EP :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.trans
    phaseCoordinateEquiv.symm.toContinuousLinearEquiv

@[simp] theorem phaseProductEquiv_apply (p : E × E) :
    phaseProductEquiv p = phaseCoordinateEquiv.symm (WithLp.toLp 2 p) := rfl

@[simp] theorem phaseProductEquiv_symm_apply (z : EP) :
    phaseProductEquiv.symm z = (phasePosition z, phaseMomentum z) := rfl

/-- Reference Haar is the explicitly transported product of the two marginal Haar measures. -/
def phaseHaar : Measure EP :=
  ((volume : Measure E).prod (volume : Measure E)).map phaseProductEquiv

instance phaseHaar_isAddHaarMeasure : (phaseHaar (D := D)).IsAddHaarMeasure := by
  unfold phaseHaar
  exact phaseProductEquiv.isAddHaarMeasure_map _

/-- The original stationary seed law, merely expressed in Euclidean coordinates. -/
def phaseSeedLaw (d : Data (Fin D)) : Measure EP :=
  (seedMeasure d).map phaseCoordinateEquiv.symm

instance phaseSeedLaw_probability (d : Data (Fin D)) : IsProbabilityMeasure (phaseSeedLaw d) := by
  unfold phaseSeedLaw
  infer_instance

theorem phaseSeedLaw_eq_productMap (d : Data (Fin D)) :
    phaseSeedLaw d = ((interpolationLaw d.F d.x d.r d.b).prod (stdGaussian E)).map
      phaseProductEquiv := by
  unfold phaseSeedLaw seedMeasure KernelFlowLp.seedMeasure Kinetic.coupledPhaseMeasure
  rw [Measure.map_map phaseCoordinateEquiv.symm.continuous.measurable
    (show Measurable (WithLp.toLp 2 : E × E → WithLp 2 (E × E)) from
      (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.continuous.measurable)]
  rfl

@[simp] theorem phasePotential_product (d : Data (Fin D)) (p : E × E) :
    phasePotential d (phaseProductEquiv p) =
      interpolationPotential d.F d.x d.r d.b p.1 + ‖p.2‖^2/2 := by
  have he : phaseCoordinateEquiv (phaseProductEquiv p) = WithLp.toLp 2 p :=
    phaseCoordinateEquiv.apply_symm_apply _
  unfold phasePotential phasePosition phaseMomentum
  rw [he]

/-- Actual normalized Gibbs-law identity, from the two actual marginal laws. -/
theorem phaseSeedLaw_eq_tilted (d : Data (Fin D)) :
    phaseSeedLaw d = phaseHaar.tilted (fun z => -phasePotential d z) := by
  rw [phaseSeedLaw_eq_productMap,
    interpolationLaw_eq_tilted d.hF d.hlo d.x d.r (by linarith [d.hb]) d.hb1,
    Kinetic.Reheating.stdGaussian_eq_quadratic_tilted]
  rw [Gibbs.prod_tilted (volume : Measure E) (volume : Measure E)
    (fun y : E => -interpolationPotential d.F d.x d.r d.b y)
    (fun x : E => -(‖x‖^2/2))
    ((contDiff_interpolationPotential d.hF d.hlo d.hup d.x d.r
      (by linarith [d.hb]) d.hb1).continuous.neg.measurable)
    (((continuous_norm.pow 2).div_const 2).neg.measurable)]
  have hm := Gibbs.map_tilted_equiv phaseProductEquiv.toHomeomorph.toMeasurableEquiv
    ((volume : Measure E).prod (volume : Measure E))
    (fun p : E × E => -interpolationPotential d.F d.x d.r d.b p.1 + -(‖p.2‖^2/2))
  have hpot : (fun y : EP =>
      -interpolationPotential d.F d.x d.r d.b
        (phaseProductEquiv.toHomeomorph.toMeasurableEquiv.symm y).1 +
      -(‖(phaseProductEquiv.toHomeomorph.toMeasurableEquiv.symm y).2‖^2/2)) =
      (fun z => -phasePotential d z) := by
    funext z
    change -(interpolationPotential d.F d.x d.r d.b (phasePosition z)) +
      -(‖phaseMomentum z‖^2/2) = -phasePotential d z
    simp only [phasePotential]
    ring
  rw [hpot] at hm
  exact hm

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
