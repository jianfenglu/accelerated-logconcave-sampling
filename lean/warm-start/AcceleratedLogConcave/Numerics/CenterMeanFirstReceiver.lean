import AcceleratedLogConcave.Numerics.CenterMeanFirstLp
import AcceleratedLogConcave.Numerics.MeanFlowLp

/-! Actual common-seed first derivative. This is not the m ≥ 2 Regularity supplier. -/
noncomputable section
open MeasureTheory
namespace AcceleratedLogConcave.Numerics.MeanFlowLp
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

def centerMeanFirstLp (d : Data ι m) (t : ℝ) : Lp E 2 (seedMeasure d) :=
  phasePullback d (CenterMeanSecondJetSource.firstLp (kernelData d)
    (d.sigma/2) (half_pos d.hsigma) t)

theorem continuous_centerMeanFirstLp (d : Data ι m) : Continuous (centerMeanFirstLp d) :=
  (phasePullback d).continuous.comp
    (CenterMeanSecondJetSource.continuous_firstLp (kernelData d)
      (d.sigma/2) (half_pos d.hsigma))

theorem hasDerivAt_centerMeanLp (d : Data ι m) (t : ℝ) :
    HasDerivAt (centerMeanLp d) (centerMeanFirstLp d t) t := by
  have h := ((phasePullback d).hasFDerivAt.comp_hasDerivAt t
    (CenterMeanSecondJetSource.hasDerivAt_centeredMeanLp (kernelData d)
      (d.sigma/2) (half_pos d.hsigma) t)).add_const (offsetLp d)
  convert h using 1
  · exact funext (centerMeanLp_eq d)
  · rfl

theorem norm_centerMeanFirstLp_sq_le (d : Data ι m) (t : ℝ) :
    ‖centerMeanFirstLp d t‖^2 ≤
      (CenterMeanSecondJetSource.firstEnergyScale (kernelData d) (d.sigma/2))^2 *
        (Module.finrank ℝ E : ℝ) := by
  simpa [centerMeanFirstLp,phasePullback] using
    CenterMeanSecondJetSource.norm_firstLp_sq_le (kernelData d)
      (d.sigma/2) (half_pos d.hsigma) t

end AcceleratedLogConcave.Numerics.MeanFlowLp
