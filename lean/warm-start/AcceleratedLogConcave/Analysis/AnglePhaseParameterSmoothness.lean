import AcceleratedLogConcave.Analysis.AnglePhaseCoefficients
import AcceleratedLogConcave.Analysis.GaussianPhaseEnvironment
import AcceleratedLogConcave.Tensor.PhaseParametricSmoothness

/-! Actual displacement phase coefficients are jointly smooth in the passive
midpoint and active Gaussian phase. This supplies product-law measurability. -/
noncomputable section
open scoped ContDiff
namespace AcceleratedLogConcave.Analysis.AnglePhase
open Tensor Tensor.AdjointReduction Tensor.PhaseParametricSmoothness
open Tensor.PhaseSourceJetInduction Numerics.CenterMeanSecondJetSource
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))

theorem smooth_parameter_displacementCoordinate (T : E → E) (hT : ContDiff ℝ ∞ T)
    (q a : ℝ) (i : Fin (D+D)) :
    ContDiff ℝ ∞ (fun p : E × EP => displacementCoordinate T p.1 q a i p.2) := by
  have hs : ContDiff ℝ ∞ (fun p : E × EP => p.1+q • phasePosition p.2) :=
    contDiff_fst.add (((smooth_phasePosition (D := D)).comp contDiff_snd).const_smul q)
  unfold displacementCoordinate
  cases finSumFinEquiv.symm i with
  | inl j => exact contDiff_const.mul (contDiff_const.inner ℝ ((hT.comp hs).sub hs))
  | inr j => exact contDiff_const

theorem smooth_parameter_angleCoefficients (T : E → E) (hT : ContDiff ℝ ∞ T)
    (q a : ℝ) : ∀ c u,
    ContDiff ℝ ∞ (fun p : E × EP => angleCoefficients T p.1 q a c p.2 u) := by
  intro c u
  cases c with
  | transport => exact contDiff_const
  | scoreHessian => exact contDiff_const
  | observableGradient =>
    exact contDiff_parameter_dir (f := fun M => displacementCoordinate T M q a (u (0 : Fin 2)))
      (smooth_parameter_displacementCoordinate T hT q a (u (0 : Fin 2))) _
  | positionProjection => exact contDiff_const

theorem smooth_parameter_angleVector (T : E → E) (hT : ContDiff ℝ ∞ T)
    (q a : ℝ) (e : Expr PhaseExpression.signature 1) :
    ContDiff ℝ ∞ (fun p : E × EP => vectorSection (angleCoefficients T p.1 q a)
      Kinetic.Reheating.gaussianPotential e p.2) := by
  exact contDiff_parameter_vectorSection (fun M => angleCoefficients T M q a)
    (fun _ : E => Kinetic.Reheating.gaussianPotential)
    (smooth_parameter_angleCoefficients T hT q a)
    (Kinetic.Reheating.gaussianPotential_smooth.comp contDiff_snd) e
end AcceleratedLogConcave.Analysis.AnglePhase
