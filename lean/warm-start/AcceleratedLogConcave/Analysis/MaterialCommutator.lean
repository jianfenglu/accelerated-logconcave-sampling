import AcceleratedLogConcave.Analysis.ODEObservableJet
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Differential commutator for a material derivative and a constant spatial
direction. The correction is the derivative of the velocity, with its sign
explicit. This is the local calculus step behind warm-start material jets. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Analysis
variable {P A : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup A] [NormedSpace ℝ A]

def materialDerivative (V : P → P) (f : P → A) (p : P) : A := fderiv ℝ f p (V p)
def directionalDerivative (w : P) (f : P → A) (p : P) : A := fderiv ℝ f p w

/-- [D,∂w] f = -Df(DV w); second-derivative symmetry is explicit. -/
theorem material_directional_commutator {f : P → A} {V : P → P} {p : P}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) p)
    (hV : DifferentiableAt ℝ V p) (hs : IsSymmSndFDerivAt ℝ f p) (w : P) :
    materialDerivative V (directionalDerivative w f) p =
      directionalDerivative w (materialDerivative V f) p -
        fderiv ℝ f p (fderiv ℝ V p w) := by
  have h₁ := (hf.hasFDerivAt.clm_apply (hasFDerivAt_const w p)).fderiv
  have h₂ := (hf.hasFDerivAt.clm_apply hV.hasFDerivAt).fderiv
  change fderiv ℝ (fun q => fderiv ℝ f q w) p (V p) =
    fderiv ℝ (fun q => fderiv ℝ f q (V q)) p w - fderiv ℝ f p (fderiv ℝ V p w)
  rw [h₁, h₂]
  simpa only [add_apply, ContinuousLinearMap.comp_apply,
    zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply, add_sub_cancel_left] using hs.eq (V p) w

end AcceleratedLogConcave.Analysis
