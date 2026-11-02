import AcceleratedLogConcave.Kinetic.MomentumSplit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! The Gaussian angle clock is an actual stationary complete flow.
Its vector field is constant-skew, not an assumed invariant dynamics. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Analysis.AngleGaussianPhase
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def phase (q z : ℝ) (p : E × E) : E × E :=
  Kinetic.gaussianRotate (Real.cos (z/q)) (Real.sin (z/q)) p

theorem phase_preserving (q z : ℝ) :
    MeasurePreserving (phase (E := E) q z)
      ((stdGaussian E).prod (stdGaussian E)) ((stdGaussian E).prod (stdGaussian E)) := by
  exact Kinetic.gaussianRotate_measurePreserving (E := E) _ _ (Real.cos_sq_add_sin_sq _)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem phase_zero (q : ℝ) (p : E × E) : phase q 0 p = p := by
  simp [phase, Kinetic.gaussianRotate]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem phase_add (q z t : ℝ) (p : E × E) :
    phase q (z+t) p = phase q z (phase q t p) := by
  apply Prod.ext <;>
    simp only [phase,Kinetic.gaussianRotate,add_div,Real.cos_add,Real.sin_add,
      smul_add,add_smul,sub_smul,smul_smul,neg_smul] <;> module

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem hasDerivAt_phase_fst (q z : ℝ) (p : E × E) :
    HasDerivAt (fun t => (phase q t p).1) (q⁻¹ • (phase q z p).2) z := by
  have hc := ((hasDerivAt_id z).div_const q).cos
  have hs := ((hasDerivAt_id z).div_const q).sin
  convert (hc.smul_const p.1).add (hs.smul_const p.2) using 1 <;>
    first | rfl | (simp only [phase,Kinetic.gaussianRotate,smul_add,smul_smul,id_eq,one_div]; module)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem hasDerivAt_phase_snd (q z : ℝ) (p : E × E) :
    HasDerivAt (fun t => (phase q t p).2) ((-q⁻¹) • (phase q z p).1) z := by
  have hc := ((hasDerivAt_id z).div_const q).cos
  have hs := ((hasDerivAt_id z).div_const q).sin
  convert ((hs.neg).smul_const p.1).add (hc.smul_const p.2) using 1 <;>
    first | rfl | (simp only [phase,Kinetic.gaussianRotate,smul_add,smul_smul,id_eq,one_div]; module)
end AcceleratedLogConcave.Analysis.AngleGaussianPhase
