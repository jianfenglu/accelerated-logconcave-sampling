import AcceleratedLogConcave.Numerics.CenterMeanPhaseCalculus

/-! NEW reconstruction: true transported-kernel coordinate chain rule.
The derivative direction and the two matrix indices remain distinct. -/
noncomputable section
open scoped ContDiff
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Conditional CenteringFlowLp
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))
local notation "e" => EuclideanSpace.basisFun (Fin D) ℝ
local notation "ep" => EuclideanSpace.basisFun (Fin (D+D)) ℝ

theorem phaseKernelEntry_derivative (d : Data (Fin D)) (z v : EP) (i j : Fin D) :
    fderiv ℝ (fun w : EP => inner ℝ (e i) (K d (phasePosition w) (e j))) z v =
      fderiv ℝ (fun y => inner ℝ (e i) (K d y (e j))) (phasePosition z) (phasePosition v) := by
  have hK := Transport.contDiff_infty_transportedSteinKernelTranspose d.hF d.hell d.hlo d.hup
    d.x d.hr d.hb d.hb1 d.hsmall
  have hf : Differentiable ℝ (fun y : E => inner ℝ (e i) (K d y (e j))) := (contDiff_const.inner ℝ (hK.clm_apply contDiff_const)).differentiable (by simp)
  exact congrArg (fun L : EP →L[ℝ] ℝ => L v)
    (((hf (phasePosition z)).hasFDerivAt.comp z (phasePositionCLM (D := D)).hasFDerivAt).fderiv)

theorem phaseKernelEntry_position_derivative (d : Data (Fin D)) (z : EP) (i j k : Fin D) :
    fderiv ℝ (fun w : EP => inner ℝ (e i) (K d (phasePosition w) (e j))) z
      (ep (finSumFinEquiv (.inl k))) =
      fderiv ℝ (fun y => inner ℝ (e i) (K d y (e j))) (phasePosition z) (e k) := by
  rw [phaseKernelEntry_derivative, phasePosition_position_basis]

theorem phaseKernelEntry_momentum_derivative (d : Data (Fin D)) (z : EP) (i j k : Fin D) :
    fderiv ℝ (fun w : EP => inner ℝ (e i) (K d (phasePosition w) (e j))) z
      (ep (finSumFinEquiv (.inr k))) = 0 := by
  rw [phaseKernelEntry_derivative, phasePosition_momentum_basis, map_zero]

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
