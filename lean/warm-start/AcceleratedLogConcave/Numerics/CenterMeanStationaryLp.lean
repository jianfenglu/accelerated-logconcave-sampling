import AcceleratedLogConcave.Numerics.CenteringFlowLp
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-! Strong continuity of the actual stationary centering action on L².
This removes the need for an extra-order pointwise domination premise when
lifting a finite, already integrable source-observable jet ladder. -/
noncomputable section
open MeasureTheory
namespace AcceleratedLogConcave.Numerics.CenterMeanStationaryLp
open Conditional CenteringFlowLp
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "P" => Centering.Phase E

def phaseMap (d : Data ι) (s : ℝ) (hs : 0 < s) (t : ℝ) : C(P,P) :=
  ⟨phase d s hs t, (continuous_phase d s hs).comp (continuous_const.prodMk continuous_id)⟩

theorem continuous_phaseMap (d : Data ι) (s : ℝ) (hs : 0 < s) :
    Continuous (phaseMap d s hs) :=
  ContinuousMap.continuous_of_continuous_uncurry _ (continuous_phase d s hs)

def orbit (d : Data ι) (s : ℝ) (hs : 0 < s)
    (f : Lp E 2 (seedMeasure d)) (t : ℝ) : Lp E 2 (seedMeasure d) :=
  Lp.compMeasurePreserving (phaseMap d s hs t) (phase_preserving d s hs t) f

theorem continuous_orbit (d : Data ι) (s : ℝ) (hs : 0 < s)
    (f : Lp E 2 (seedMeasure d)) : Continuous (orbit d s hs f) := by
  exact continuous_const.compMeasurePreservingLp (continuous_phaseMap d s hs)
    (phase_preserving d s hs) (by norm_num)

theorem norm_orbit (d : Data ι) (s : ℝ) (hs : 0 < s)
    (f : Lp E 2 (seedMeasure d)) (t : ℝ) : ‖orbit d s hs f t‖ = ‖f‖ := by
  exact Lp.norm_compMeasurePreserving _ _

end AcceleratedLogConcave.Numerics.CenterMeanStationaryLp
