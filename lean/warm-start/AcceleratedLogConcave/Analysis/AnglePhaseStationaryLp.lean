import AcceleratedLogConcave.Analysis.AnglePhaseStationary
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-! Strong L² continuity of the actual Gaussian angle group. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Analysis.AnglePhase
open Numerics.CenterMeanSecondJetSource
variable {D : ℕ}
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))

theorem continuous_rotationOrbit (q : ℝ) :
    Continuous (fun p : ℝ × EP => rotationOrbit (D := D) q p.2 p.1) := by
  unfold rotationOrbit AngleGaussianPhase.phase Kinetic.gaussianRotate
  fun_prop

def rotationMap (q t : ℝ) : C(EP,EP) :=
  ⟨fun z => rotationOrbit (D := D) q z t, by
    unfold rotationOrbit AngleGaussianPhase.phase Kinetic.gaussianRotate
    fun_prop⟩

theorem continuous_rotationMap (q : ℝ) : Continuous (rotationMap (D := D) q) :=
  ContinuousMap.continuous_of_continuous_uncurry _ (continuous_rotationOrbit (D := D) q)

def gaussianLpOrbit (q : ℝ) (f : Lp EP 2 (stdGaussian EP)) (t : ℝ) :
    Lp EP 2 (stdGaussian EP) :=
  Lp.compMeasurePreserving (rotationMap (D := D) q t) (rotationOrbit_preserving (D := D) q t) f

theorem continuous_gaussianLpOrbit (q : ℝ) (f : Lp EP 2 (stdGaussian EP)) :
    Continuous (gaussianLpOrbit (D := D) q f) := by
  exact continuous_const.compMeasurePreservingLp (continuous_rotationMap (D := D) q)
    (rotationOrbit_preserving (D := D) q) (by norm_num)

theorem norm_gaussianLpOrbit (q : ℝ) (f : Lp EP 2 (stdGaussian EP)) (t : ℝ) :
    ‖gaussianLpOrbit (D := D) q f t‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f (rotationOrbit_preserving (D := D) q t)
end AcceleratedLogConcave.Analysis.AnglePhase
