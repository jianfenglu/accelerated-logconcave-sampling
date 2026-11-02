import AcceleratedLogConcave.Analysis.AnglePhaseColumns
import AcceleratedLogConcave.Tensor.PhaseSourceJetInduction

/-! Literal normalized displacement gradient, not an assumed phase observable.
The unused momentum output coordinates are exactly zero. -/
noncomputable section
open scoped ContDiff
namespace AcceleratedLogConcave.Analysis.AnglePhase
open Tensor Tensor.AdjointReduction Tensor.CoordinateReduction Tensor.PhaseExpression
open Tensor.PhaseGeneratorIdentification Numerics.CenterMeanSecondJetSource
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))

def displacementCoordinate (T : E → E) (M : E) (q a : ℝ) (i : Fin (D+D)) (z : EP) : ℝ :=
  match finSumFinEquiv.symm i with
  | .inl j => a⁻¹ * inner ℝ (EuclideanSpace.basisFun (Fin D) ℝ j)
      (T (M+q • phasePosition z) - (M+q • phasePosition z))
  | .inr _ => 0

theorem smooth_displacementCoordinate (T : E → E) (hT : ContDiff ℝ ∞ T)
    (M : E) (q a : ℝ) (i : Fin (D+D)) :
    ContDiff ℝ ∞ (displacementCoordinate T M q a i) := by
  have hs : ContDiff ℝ ∞ (fun z : EP => M+q • phasePosition z) :=
    contDiff_const.add ((smooth_phasePosition (D := D)).const_smul q)
  unfold displacementCoordinate
  cases finSumFinEquiv.symm i with
  | inl j => exact contDiff_const.mul (contDiff_const.inner ℝ ((hT.comp hs).sub hs))
  | inr j => exact contDiff_const

def angleCoefficients (T : E → E) (M : E) (q a : ℝ) :
    CoefficientEnvironment signature (D+D) := fun c z => WithLp.toLp 2 (fun u : Fin 2 → Fin (D+D) =>
  match c with
  | .transport => rotationEntry (u 0) (u 1) z
  | .scoreHessian => if u 0 = u 1 then 1 else 0
  | .observableGradient => dir (coordinateDirection (D+D) (u 1))
      (displacementCoordinate T M q a (u 0)) z
  | .positionProjection => if u 0 = u 1 then 1 else 0)

theorem smooth_angleCoefficients (T : E → E) (hT : ContDiff ℝ ∞ T)
    (M : E) (q a : ℝ) : ∀ c u,
    ContDiff ℝ ∞ (fun z => angleCoefficients T M q a c z u) := by
  intro c u
  cases c with
  | transport => exact contDiff_const
  | scoreHessian => exact contDiff_const
  | observableGradient => exact contDiff_dir (smooth_displacementCoordinate T hT M q a _) _
  | positionProjection => exact contDiff_const

theorem angleCoefficients_skew (T : E → E) (M : E) (q a : ℝ)
    (z : EP) (i j : Fin (D+D)) :
    transportEntry (angleCoefficients T M q a) i j z =
      -transportEntry (angleCoefficients T M q a) j i z := by
  exact rotationEntry_skew z i j

theorem angleCoefficients_gradient (T : E → E) (M : E) (q a : ℝ)
    (i j : Fin (D+D)) :
    sectionValue (angleCoefficients T M q a) Kinetic.Reheating.gaussianPotential F ![i,j] =
      dir (coordinateDirection (D+D) j) (displacementCoordinate T M q a i) := by
  rfl
end AcceleratedLogConcave.Analysis.AnglePhase
