import AcceleratedLogConcave.Numerics.CenterMeanFirstEnergy
import AcceleratedLogConcave.Numerics.CenterMeanStationaryFTC

/-! Actual first derivative of the original centered-mean L² curve, not merely
an almost-everywhere or pointwise trajectory derivative. -/
noncomputable section
open MeasureTheory
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Conditional CenteringFlowLp
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "P" => Centering.Phase E

def firstLp (d : Data ι) (s : ℝ) (hs : 0 < s) (t : ℝ) : Lp E 2 (seedMeasure d) :=
  CenterMeanStationaryLp.orbit d s hs ((sourceFirst_memLp d s).toLp (sourceFirst d s)) t

theorem continuous_firstLp (d : Data ι) (s : ℝ) (hs : 0 < s) :
    Continuous (firstLp d s hs) :=
  CenterMeanStationaryLp.continuous_orbit d s hs _

theorem hasDerivAt_centeredMeanLp (d : Data ι) (s : ℝ) (hs : 0 < s) (t : ℝ) :
    HasDerivAt (centeredMeanLp d s hs) (firstLp d s hs t) t := by
  let f : P → E := fun z => M d z.fst - meanOffset d
  have hf : MemLp f 2 (seedMeasure d) := by
    have hm := (memLp_two_conditionalMean d.hF d.hell d.hlo d.hup d.x d.hr
      d.hb d.hb1 d.hsmall).comp_measurePreserving (position_preserving d)
    exact hm.sub (memLp_const (meanOffset d))
  have h := CenterMeanStationaryLp.hasDerivAt_orbit_of_source d s hs f (sourceFirst d s)
    hf (sourceFirst_memLp d s) (continuous_sourceFirst d s)
    (fun u z => hasDerivAt_centeredMean d s hs u z) t
  exact h

theorem norm_firstLp_sq_le (d : Data ι) (s : ℝ) (hs : 0 < s) (t : ℝ) :
    ‖firstLp d s hs t‖^2 ≤ (firstEnergyScale d s)^2 * (Module.finrank ℝ E : ℝ) := by
  change ‖CenterMeanStationaryLp.orbit d s hs _ t‖^2 ≤ _
  rw [CenterMeanStationaryLp.norm_orbit, Analysis.DominatedLp.norm_sq_toLp]
  exact integral_sourceFirst_norm_sq_le d s

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
