import AcceleratedLogConcave.Numerics.CenterMeanStationaryLp
import AcceleratedLogConcave.Analysis.StationaryLpFTC
import AcceleratedLogConcave.Analysis.DominatedLp

/-! Actual stationary-source derivative lift. The energy in this theorem is used
only to justify differentiation, not as a numerical W12 derivative budget. -/
noncomputable section
open MeasureTheory
namespace AcceleratedLogConcave.Numerics.CenterMeanStationaryLp
open Conditional CenteringFlowLp
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "P" => Centering.Phase E

/-- A pointwise source generator identity lifts to the genuine common-source L²
orbit as soon as the two source observables have finite second moment. -/
theorem hasDerivAt_orbit_of_source (d : Data ι) (s : ℝ) (hs : 0 < s)
    (f g : P → E) (hf : MemLp f 2 (seedMeasure d)) (hg : MemLp g 2 (seedMeasure d))
    (hgc : Continuous g)
    (hd : ∀ t z, HasDerivAt (fun a => f (phase d s hs a z))
      (g (phase d s hs t z)) t) (t : ℝ) :
    HasDerivAt (orbit d s hs (hf.toLp f)) (orbit d s hs (hg.toLp g) t) t := by
  have hfg (u : ℝ) : MemLp (fun z => f (phase d s hs u z)) 2 (seedMeasure d) :=
    hf.comp_measurePreserving (phase_preserving d s hs u)
  have hgg (u : ℝ) : MemLp (fun z => g (phase d s hs u z)) 2 (seedMeasure d) :=
    hg.comp_measurePreserving (phase_preserving d s hs u)
  have he (u : ℝ) : (∫ z, ‖g (phase d s hs u z)‖^2 ∂seedMeasure d) =
      ‖hg.toLp g‖^2 := by
    rw [← Analysis.DominatedLp.norm_sq_toLp (hgg u)]
    change ‖orbit d s hs (hg.toLp g) u‖^2 = _
    rw [norm_orbit]
  have hh := Analysis.StationaryLpFTC.hasDerivAt_toLp_of_energy
    (fun u z => f (phase d s hs u z)) (fun u z => g (phase d s hs u z))
    (hgc.comp (continuous_phase d s hs)) hfg hgg
    (continuous_orbit d s hs (hg.toLp g)) (sq_nonneg ‖hg.toLp g‖)
    (fun u => (he u).le) hd t
  exact hh

end AcceleratedLogConcave.Numerics.CenterMeanStationaryLp
