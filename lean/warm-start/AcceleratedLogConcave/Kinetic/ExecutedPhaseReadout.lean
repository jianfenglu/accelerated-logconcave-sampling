import AcceleratedLogConcave.Kinetic.Mixing.DiscretePhase

/-! Exact physical rotation/reheating readout identities. The retained finite
program separately returns a normalized latent correction; no equality with its
output, child laws, or an exact-flow coordinate relation is asserted here. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Kinetic
open Reheating ConditionalContraction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem rotate_position (s n : ℝ) (hsn : s^2+n^2=1)
    (z : GaussianPhase E) :
    (phaseRotate s n hsn z).1.1 = z.1.1 := by rfl
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem rotate_momentum (s n : ℝ) (hsn : s^2+n^2=1)
    (z : GaussianPhase E) :
    (phaseRotate s n hsn z).1.2 = s • z.1.2 + n • z.2 := by rfl
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem rotate_hidden (s n : ℝ) (hsn : s^2+n^2=1)
    (z : GaussianPhase E) :
    (phaseRotate s n hsn z).2 = (-n) • z.1.2 + s • z.2 := by
  exact congrArg Prod.snd
    (gaussianRotateHomeomorph_apply (E := E) s n hsn (z.1.2,z.2))


omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem phaseRotate_reheat_cancel (s n α : ℝ) (hsn : s^2+n^2=1)
    (z : GaussianPhase E) (G : E) :
    z.1.1 + α • (n • (phaseRotate s n hsn z).2 + s • G) =
      (z.1.1 - α • z.1.2) +
        α • (s • (phaseRotate s n hsn z).1.2 + s • G) := by
  have hsq : s*s+n*n=1 := by nlinarith [hsn]
  have hr : z.1.2 + n • (phaseRotate s n hsn z).2 =
      s • (phaseRotate s n hsn z).1.2 := by
    rw [rotate_hidden s n hsn z, rotate_momentum s n hsn z]
    calc
      z.1.2 + n • ((-n) • z.1.2 + s • z.2) =
          (s*s+n*n) • z.1.2 + n • ((-n) • z.1.2 + s • z.2) := by
            rw [hsq, one_smul]
      _ = s • (s • z.1.2 + n • z.2) := by module
  calc
    z.1.1 + α • (n • (phaseRotate s n hsn z).2 + s • G) =
        (z.1.1 - α • z.1.2) +
          α • ((z.1.2 + n • (phaseRotate s n hsn z).2) + s • G) := by module
    _ = _ := by rw [hr]


omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The actual fixed-clock output's first coordinate has an exact comoving
readout; the final OU refresh affects only the second coordinate. -/
theorem fixedClockOutput_position_comoving (s n : ℝ) (hsn : s^2+n^2=1)
    (τ Γ : ℝ) (z : ((GaussianPhase E × E) × E) × E) :
    let pre := dormantNewState z.1.1
    let rot := phaseRotate (E := E) s n hsn pre
    (fixedClockOutput (E := E) s n hsn τ Γ z).1 =
      (pre.1.1 - Real.sqrt τ • pre.1.2) +
        Real.sqrt τ • (s • rot.1.2 + s • z.1.2) := by
  dsimp [fixedClockOutput, correlatedHeatObservation]
  exact phaseRotate_reheat_cancel s n (Real.sqrt τ) hsn
    (dormantNewState z.1.1) z.1.2


omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Under the exact flow-coordinate relation, the physical position readout is
based at the entering position rather than the terminal transported one. -/
theorem fixedClockOutput_position_from_initial (s n : ℝ)
    (hsn : s^2+n^2=1) (τ Γ : ℝ)
    (z : ((GaussianPhase E × E) × E) × E) (x : E)
    (hposition : (dormantNewState z.1.1).1.1 =
      x + Real.sqrt τ • (dormantNewState z.1.1).1.2) :
    let rot := phaseRotate (E := E) s n hsn (dormantNewState z.1.1)
    (fixedClockOutput (E := E) s n hsn τ Γ z).1 =
      x + Real.sqrt τ • (s • rot.1.2 + s • z.1.2) := by
  rw [fixedClockOutput_position_comoving, hposition]
  module


/-- For the source specialization `A=ℓ²`, the reheat standard deviation is
exactly `ℓ R` at every permitted stopping clock. -/
theorem source_reheat_scale (ell : ℝ) (hell : 0 ≤ ell)
    (R : Set.Icc (0:ℝ) (1/2)) :
    Real.sqrt (ell^2 * (R:ℝ)^2) = ell * (R:ℝ) := by
  rw [← mul_pow, Real.sqrt_sq_eq_abs, abs_of_nonneg]
  exact mul_nonneg hell R.property.1

end AcceleratedLogConcave.Kinetic
