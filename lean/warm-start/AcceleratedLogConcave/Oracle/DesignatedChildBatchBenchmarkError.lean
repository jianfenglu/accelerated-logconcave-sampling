import AcceleratedLogConcave.Oracle.DesignatedChildBatchErrorTransfer

/-! Benchmark evaluation on the original literal designated-child tape at
its benchmark center. The true stored iterate may differ. This uses the same
transformed source tape as the executable final evaluator and keeps Pi. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.DesignatedChildBatchBenchmarkError
open AffineLowering TapeLowering NoisyLayer CanonicalTapeLaw CanonicalTapeMeasurability
open DesignatedChildBatchCoupling DesignatedChildAbsorbedLaw
open DesignatedChildBatchErrorTransfer
set_option backward.isDefEq.respectTransparency false
local instance canonicalTapeSpace (d : ℕ) (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
variable {d N C : ℕ} {Γ : Ctx} (B : Data N C Γ)
  {H W : Type*} [MeasurableSpace H] [MeasurableSpace W]
  (center : Fin N → H → Point d) (observe : W → H × (∀ i, Raw d B i))

/-- The lower program executes the ACTUAL compiler-transformed tape, unchanged
uniform/residual inventory and original stored Pi, at center+rho comparison. -/
def sourceError (i : Fin N) (G : Point d → Point d) (u : H → Point d) (width : ℝ)
    (z : W × (Fin N → Point d)) : Point d :=
  let raw := (observe z.1).2 i
  let hu := tapeSeed (B.child i).program (B.child i).enumeration (B.slot i)
    (B.old i) (B.designated i) (B.auxiliary i) raw.2.2
  (show Point d from (run (B.child i).program G
    ⟨(B.child i).coefficient,center i (observe z.1).1+B.rho i • raw.1,raw.2.1⟩ Env.empty
    (transformedSourceTape (B.child i).program (B.child i).enumeration
      (CovarianceSetup.childRoot (B.rho i) (B.radius i) (B.child i).shiftVector) hu.1 hu.2)).value) -
    (u (observe z.1).1+width • z.2 i)

omit [MeasurableSpace H] [MeasurableSpace W] in
theorem sourceError_eq_lower (i : Fin N) (G : Point d → Point d) (u : H → Point d) (width : ℝ)
    (hshift : ChildAbsorption.QueryShift (B.child i).program (B.child i).enumeration
      (B.child i).coefficient (B.radius i) (B.child i).shiftVector)
    (z : W × (Fin N → Point d)) :
    sourceError B center observe i G u width z =
      lowerError B center i G u width (lowerProjection B observe i z) := by
  have h := DesignatedChildRunShift.run_completedSource (B.child i).program (B.child i).enumeration
    (B.slot i) (B.old i) (B.designated i) (B.auxiliary i)
    (B.rho i) (B.radius i) B.Ds (B.child i).shiftVector (B.child i).coefficient
    (B.rho_nonneg i) (B.radius_pos i) B.Ds_pos (B.shift_budget i) (B.small i)
    hshift G (center i (observe z.1).1) ((observe z.1).2 i)
  dsimp only at h
  dsimp only [sourceError]
  erw [← h]
  rfl

variable (L : PrimitiveLaws d) (hL : L.pointDraw = stdGaussian (Point d))
  (J : Lower L B) (hcenter : ∀ i, Measurable (center i))
  (μ : Measure W) [IsProbabilityMeasure μ] (ν : Measure H) [IsProbabilityMeasure ν]
  (hobs : Measurable observe)
  (hprojection : μ.map observe = ν.prod (Measure.pi (rawLaw L B)))

include hprojection in
theorem source_error_memLp (i : Fin N) (G : Point d → Point d) (u : H → Point d) (width : ℝ)
    (hshift : ChildAbsorption.QueryShift (B.child i).program (B.child i).enumeration
      (B.child i).coefficient (B.radius i) (B.child i).shiftVector)
    (herr : MemLp (lowerError B center i G u width) 2
      (ν ⊗ₘ (J.joint i).comap (center i) (hcenter i))) :
    MemLp (sourceError B center observe i G u width) 2
      (observedLaw L hL B J center hcenter μ observe hobs) := by
  have he : sourceError B center observe i G u width =
      fun z => lowerError B center i G u width (lowerProjection B observe i z) := by
    funext z
    exact sourceError_eq_lower B center observe i G u width hshift z
  rw [he]
  exact observed_error_memLp L hL B J center hcenter μ ν observe hobs hprojection
    i (lowerError B center i G u width) herr

include hprojection in
theorem source_error_square_integral (i : Fin N) (G : Point d → Point d) (u : H → Point d) (width : ℝ)
    (hshift : ChildAbsorption.QueryShift (B.child i).program (B.child i).enumeration
      (B.child i).coefficient (B.radius i) (B.child i).shiftVector)
    (herr : MemLp (lowerError B center i G u width) 2
      (ν ⊗ₘ (J.joint i).comap (center i) (hcenter i))) :
    (∫ z, ‖sourceError B center observe i G u width z‖^2
      ∂observedLaw L hL B J center hcenter μ observe hobs) =
      ∫ h, ∫ z, ‖DesignatedChildRunShift.lowerError (B.child i).program G (B.child i).coefficient
        (center i h) (u h) width z‖^2 ∂J.joint i (center i h) ∂ν := by
  have he : sourceError B center observe i G u width =
      fun z => lowerError B center i G u width (lowerProjection B observe i z) := by
    funext z
    exact sourceError_eq_lower B center observe i G u width hshift z
  rw [he]
  exact observed_error_square_integral L hL B J center hcenter μ ν observe hobs hprojection
    i (lowerError B center i G u width) herr

end AcceleratedLogConcave.Oracle.DesignatedChildBatchBenchmarkError
