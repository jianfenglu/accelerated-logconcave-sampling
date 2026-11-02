import AcceleratedLogConcave.Numerics.CenterMeanPhaseCoordinates

/-! NEW reconstruction: derivatives of the actual phase potential and projections. -/
noncomputable section
open scoped ContDiff
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Conditional CenteringFlowLp
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))
local notation "e" => EuclideanSpace.basisFun (Fin D) ℝ
local notation "ep" => EuclideanSpace.basisFun (Fin (D+D)) ℝ

def phasePositionCLM : EP →L[ℝ] E :=
  (WithLp.fstL 2 ℝ E E).comp phaseCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap

def phaseMomentumCLM : EP →L[ℝ] E :=
  (WithLp.sndL 2 ℝ E E).comp phaseCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem phasePositionCLM_apply (z : EP) : phasePositionCLM z = phasePosition z := rfl
@[simp] theorem phaseMomentumCLM_apply (z : EP) : phaseMomentumCLM z = phaseMomentum z := rfl

@[simp] theorem phasePosition_position_basis (i : Fin D) :
    phasePosition (ep (finSumFinEquiv (.inl i))) = e i := by
  ext j
  simp [phasePosition_apply, EuclideanSpace.basisFun_apply]

@[simp] theorem phasePosition_momentum_basis (i : Fin D) :
    phasePosition (ep (finSumFinEquiv (.inr i))) = 0 := by
  ext j
  simp [phasePosition_apply, EuclideanSpace.basisFun_apply]
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_addNat] at hv
  omega

@[simp] theorem phaseMomentum_position_basis (i : Fin D) :
    phaseMomentum (ep (finSumFinEquiv (.inl i))) = 0 := by
  ext j
  simp [phaseMomentum_apply, EuclideanSpace.basisFun_apply]
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_addNat] at hv
  omega

@[simp] theorem phaseMomentum_momentum_basis (i : Fin D) :
    phaseMomentum (ep (finSumFinEquiv (.inr i))) = e i := by
  ext j
  simp [phaseMomentum_apply, EuclideanSpace.basisFun_apply]

theorem fderiv_phasePotential (d : Data (Fin D)) (z v : EP) :
    fderiv ℝ (phasePotential d) z v =
      inner ℝ (sourceScore d (phasePosition z)) (phasePosition v) +
      inner ℝ (phaseMomentum z) (phaseMomentum v) := by
  have hp := ((contDiff_interpolationPotential d.hF d.hlo d.hup d.x d.r
    (by linarith [d.hb]) d.hb1).differentiable (by simp) (phasePosition z)).hasFDerivAt
  have hm := (phaseMomentumCLM (D := D)).hasFDerivAt (x := z)
  have h := (hp.comp z (phasePositionCLM (D := D)).hasFDerivAt).add (hm.norm_sq.mul_const (2⁻¹ : ℝ))
  have hh := congrArg (fun L : EP →L[ℝ] ℝ => L v) h.fderiv
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    smul_apply,
    innerSL_apply_apply, smul_eq_mul, phasePositionCLM_apply, phaseMomentumCLM_apply] at hh
  change fderiv ℝ (phasePotential d) z v = _ at hh
  have hd : fderiv ℝ (interpolationPotential d.F d.x d.r d.b) (phasePosition z) (phasePosition v) =
      inner ℝ (sourceScore d (phasePosition z)) (phasePosition v) := by
    rw [← inner_gradient_left,
      gradient_interpolationPotential d.hF d.hlo d.hup d.x d.r (by linarith [d.hb]) d.hb1]
    rfl
  rw [hd] at hh
  simpa using hh

theorem phasePotential_position_derivative (d : Data (Fin D)) (z : EP) (i : Fin D) :
    fderiv ℝ (phasePotential d) z (ep (finSumFinEquiv (.inl i))) =
      inner ℝ (sourceScore d (phasePosition z)) (e i) := by
  simp only [fderiv_phasePotential, phasePosition_position_basis, phaseMomentum_position_basis, inner_zero_right, add_zero]

theorem phasePotential_momentum_derivative (d : Data (Fin D)) (z : EP) (i : Fin D) :
    fderiv ℝ (phasePotential d) z (ep (finSumFinEquiv (.inr i))) =
      inner ℝ (phaseMomentum z) (e i) := by
  simp only [fderiv_phasePotential, phasePosition_momentum_basis, phaseMomentum_momentum_basis, inner_zero_right, zero_add]

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
