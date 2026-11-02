import AcceleratedLogConcave.Numerics.CenterMeanSteinColumns
import AcceleratedLogConcave.Tensor.PhaseGeneratorIdentification
import AcceleratedLogConcave.Conditional.InterpolationTilted

/-! The literal phase-coordinate skew block. The centering normalization is
separate from its as-yet-unproved all-order quantitative coefficient budgets. -/
noncomputable section
open scoped ContDiff
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Conditional CenteringFlowLp
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))
local notation "P" => WithLp 2 (E × E)
local notation "e" => EuclideanSpace.basisFun (Fin D) ℝ

def phaseCoordinateEquiv : EP ≃ₗᵢ[ℝ] P :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finSumFinEquiv.symm : Fin (D+D) ≃ Fin D ⊕ Fin D)).trans
    (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin D ⊕ Fin D => ℝ))

def phasePosition (z : EP) : E := (phaseCoordinateEquiv z).ofLp.1
def phaseMomentum (z : EP) : E := (phaseCoordinateEquiv z).ofLp.2

@[simp] theorem phasePosition_apply (z : EP) (i : Fin D) :
    phasePosition z i = z (finSumFinEquiv (Sum.inl i)) := rfl
@[simp] theorem phaseMomentum_apply (z : EP) (i : Fin D) :
    phaseMomentum z i = z (finSumFinEquiv (Sum.inr i)) := rfl

theorem smooth_phasePosition : ContDiff ℝ ∞ (phasePosition (D := D)) :=
  (WithLp.fstL 2 ℝ E E).contDiff.comp phaseCoordinateEquiv.toContinuousLinearEquiv.contDiff

theorem smooth_phaseMomentum : ContDiff ℝ ∞ (phaseMomentum (D := D)) :=
  (WithLp.sndL 2 ℝ E E).contDiff.comp phaseCoordinateEquiv.toContinuousLinearEquiv.contDiff

/-- The sign is fixed by δ_y K=M-u: top-right K and bottom-left minus its transpose. -/
def skewBlockEntry (A : E →L[ℝ] E) : (Fin D ⊕ Fin D) → (Fin D ⊕ Fin D) → ℝ
  | .inl _, .inl _ => 0
  | .inl i, .inr j => inner ℝ (e i) (A (e j))
  | .inr i, .inl j => -inner ℝ (e j) (A (e i))
  | .inr _, .inr _ => 0

theorem skewBlockEntry_skew (A : E →L[ℝ] E) (i j : Fin D ⊕ Fin D) :
    skewBlockEntry A i j = -skewBlockEntry A j i := by
  cases i <;> cases j <;> simp [skewBlockEntry]

def phaseTransportEntry (d : Data (Fin D)) (ellScale : ℝ) (i j : Fin (D+D)) (z : EP) : ℝ :=
  ellScale⁻¹ * skewBlockEntry (K d (phasePosition z))
    (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)

theorem phaseTransportEntry_skew (d : Data (Fin D)) (ellScale : ℝ) (z : EP) (i j : Fin (D+D)) :
    phaseTransportEntry d ellScale i j z = -phaseTransportEntry d ellScale j i z := by
  unfold phaseTransportEntry
  rw [skewBlockEntry_skew]
  ring

def phasePotential (d : Data (Fin D)) (z : EP) : ℝ :=
  interpolationPotential d.F d.x d.r d.b (phasePosition z) + ‖phaseMomentum z‖^2/2

theorem smooth_phasePotential (d : Data (Fin D)) : ContDiff ℝ ∞ (phasePotential d) := by
  exact ((contDiff_interpolationPotential d.hF d.hlo d.hup d.x d.r
    (by linarith [d.hb]) d.hb1).comp smooth_phasePosition).add
      ((contDiff_norm_sq ℝ).comp smooth_phaseMomentum |>.div_const 2)

theorem smooth_phaseTransportEntry (d : Data (Fin D)) (ellScale : ℝ) (i j : Fin (D+D)) :
    ContDiff ℝ ∞ (phaseTransportEntry d ellScale i j) := by
  have hK : ContDiff ℝ ∞ (fun z : EP => K d (phasePosition z)) :=
    (Transport.contDiff_infty_transportedSteinKernelTranspose d.hF d.hell d.hlo d.hup
      d.x d.hr d.hb d.hb1 d.hsmall).comp smooth_phasePosition
  have hv (k l : Fin D) : ContDiff ℝ ∞ (fun z : EP => inner ℝ (e k) (K d (phasePosition z) (e l))) :=
    contDiff_const.inner ℝ (hK.clm_apply contDiff_const)
  unfold phaseTransportEntry
  cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
    simp only [skewBlockEntry]
  all_goals first | exact contDiff_const | exact contDiff_const.mul (hv _ _) |
    exact contDiff_const.mul (hv _ _).neg

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
