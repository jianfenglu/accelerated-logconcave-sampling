import AcceleratedLogConcave.Kinetic.MomentumSplit
import AcceleratedLogConcave.Kinetic.ReferenceFlow.ConjugateDrift

/-! The exact continuous linear coordinate changes from (x,Y,H) to (x,P,E),
and the actual full and pure-heat vector fields in physical phase coordinates. -/
noncomputable section
open Function InnerProductSpace
namespace AcceleratedLogConcave.Kinetic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def gaussianSplitLinearEquiv (s n : ℝ) (hsn : s^2+n^2=1) : (E × E) ≃L[ℝ] (E × E) where
  toLinearEquiv :=
    { toEquiv := (gaussianSplitHomeomorph s n hsn).toEquiv
      map_add' := by
        intro z w
        apply Prod.ext
        · change s • (z.1 + w.1) + n • (z.2 + w.2) =
            (s • z.1 + n • z.2) + (s • w.1 + n • w.2)
          module
        · change n • (z.1 + w.1) + (-s) • (z.2 + w.2) =
            (n • z.1 + (-s) • z.2) + (n • w.1 + (-s) • w.2)
          module
      map_smul' := by
        intro c z
        apply Prod.ext
        · change s • (c • z.1) + n • (c • z.2) = c • (s • z.1 + n • z.2)
          module
        · change n • (c • z.1) + (-s) • (c • z.2) = c • (n • z.1 + (-s) • z.2)
          module }
  continuous_toFun := (gaussianSplitHomeomorph s n hsn).continuous
  continuous_invFun := (gaussianSplitHomeomorph s n hsn).symm.continuous

def gaussianRotateLinearEquiv (s n : ℝ) (hsn : s^2+n^2=1) : (E × E) ≃L[ℝ] (E × E) :=
  (gaussianSplitLinearEquiv s n hsn).trans
    ((ContinuousLinearEquiv.refl ℝ E).prodCongr (ContinuousLinearEquiv.neg ℝ))

def phaseRotateLinearEquiv (s n : ℝ) (hsn : s^2+n^2=1) : GaussianPhase E ≃L[ℝ] GaussianPhase E :=
  (ContinuousLinearEquiv.prodAssoc ℝ E E E).trans
    (((ContinuousLinearEquiv.refl ℝ E).prodCongr (gaussianRotateLinearEquiv s n hsn)).trans
      (ContinuousLinearEquiv.prodAssoc ℝ E E E).symm)

/-- Convert the coupled Hilbert pair and dormant coordinate to physical phase. -/
def physicalPhaseCoordinates (s n : ℝ) (hsn : s^2+n^2=1) :
    (CoupledPhase E × E) ≃L[ℝ] GaussianPhase E :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ E E).prodCongr (ContinuousLinearEquiv.refl ℝ E)).trans
    (phaseRotateLinearEquiv s n hsn)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem physicalPhaseCoordinates_apply (s n : ℝ) (hsn : s^2+n^2=1) (z : CoupledPhase E × E) :
    physicalPhaseCoordinates s n hsn z =
      ((z.1.fst, s • z.1.snd + n • z.2), (-n) • z.1.snd + s • z.2) := by
  apply Prod.ext
  · rfl
  · change -(n • z.1.snd + (-s) • z.2) = _
    module

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem physicalPhaseCoordinates_symm_apply (s n : ℝ) (hsn : s^2+n^2=1) (z : GaussianPhase E) :
    (physicalPhaseCoordinates s n hsn).symm z =
      (WithLp.toLp 2 (z.1.1,s • z.1.2 - n • z.2), n • z.1.2 + s • z.2) := by
  apply Prod.ext
  · apply (WithLp.prodContinuousLinearEquiv 2 ℝ E E).injective
    apply Prod.ext
    · rfl
    · change s • z.1.2 + n • (-z.2) = s • z.1.2 - n • z.2
      module
  · change n • z.1.2 + (-s) • (-z.2) = n • z.1.2 + s • z.2
    module

def physicalPhaseDrift (U : ℝ → E → ℝ) (ell : ℝ) (c : ℝ → ℝ)
    (s n : ℝ) (hsn : s^2+n^2=1) : ℝ → GaussianPhase E → GaussianPhase E :=
  conjugateDrift (physicalPhaseCoordinates s n hsn) (extendDrift (coupledDrift U ell c))

omit [MeasurableSpace E] [BorelSpace E] in
theorem physicalPhaseDrift_apply (U : ℝ → E → ℝ) (ell : ℝ) (c : ℝ → ℝ)
    (s n : ℝ) (hsn : s^2+n^2=1) (t : ℝ) (z : GaussianPhase E) :
    physicalPhaseDrift U ell c s n hsn t z =
      ((ell • (s • z.1.2 - n • z.2) - c t • gradient (U t) z.1.1,
        (-ell*s) • gradient (U t) z.1.1), (ell*n) • gradient (U t) z.1.1) := by
  unfold physicalPhaseDrift conjugateDrift
  rw [physicalPhaseCoordinates_symm_apply, physicalPhaseCoordinates_apply]
  simp only [extendDrift, coupledDrift]
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · change s • (-ell • gradient (U t) z.1.1) + n • (0 : E) =
        (-ell*s) • gradient (U t) z.1.1
      module
  · change (-n) • (-ell • gradient (U t) z.1.1) + s • (0 : E) =
      (ell*n) • gradient (U t) z.1.1
    module

omit [MeasurableSpace E] [BorelSpace E] in
/-- The pure-heat frame cancels exactly the reverse-heat part of the drift. -/
theorem physicalPhaseDrift_difference (U : ℝ → E → ℝ) (ell : ℝ) (c : ℝ → ℝ)
    (s n : ℝ) (hsn : s^2+n^2=1) (t : ℝ) (z : GaussianPhase E) :
    physicalPhaseDrift U 0 c s n hsn t z - physicalPhaseDrift U ell c s n hsn t z =
      -ell • ((s • z.1.2 - n • z.2, -s • gradient (U t) z.1.1),
        n • gradient (U t) z.1.1) := by
  rw [physicalPhaseDrift_apply, physicalPhaseDrift_apply]
  ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd] <;> module

end AcceleratedLogConcave.Kinetic
