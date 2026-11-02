import AcceleratedLogConcave.Kinetic.Reheating.OUGaussian
import AcceleratedLogConcave.Kinetic.PhasePullback

/-! The actual common Gaussian split before drawing the clock and the source
rotation after the dormant collision. Both preserve the full reference law. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace WithLp
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic
open Reheating GaussianFin Analysis.Poisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The common pre-clock split: (P,E0) maps to (sP+nE0,nP-sE0). -/
def gaussianSplit (s n : ℝ) (z : E × E) : E × E :=
  (s • z.1 + n • z.2, n • z.1 + (-s) • z.2)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem gaussianSplit_involutive (s n : ℝ) (hsn : s ^ 2 + n ^ 2 = 1) :
    Function.Involutive (gaussianSplit (E := E) s n) := by
  intro z
  apply Prod.ext
  · change s • (s • z.1 + n • z.2) + n • (n • z.1 + (-s) • z.2) = z.1
    calc
      _ = (s * s + n * n) • z.1 := by module
      _ = z.1 := by rw [show s * s + n * n = 1 by nlinarith, one_smul]
  · change n • (s • z.1 + n • z.2) + (-s) • (n • z.1 + (-s) • z.2) = z.2
    calc
      _ = (s * s + n * n) • z.2 := by module
      _ = z.2 := by rw [show s * s + n * n = 1 by nlinarith, one_smul]

/-- Exact Gaussian product invariance, transported from the proved coordinate
rotation law. The two output coordinates remain independent Gaussians. -/
theorem gaussianSplit_measurePreserving (s n : ℝ) (hsn : s ^ 2 + n ^ 2 = 1) :
    MeasurePreserving (gaussianSplit (E := E) s n)
      ((stdGaussian E).prod (stdGaussian E)) ((stdGaussian E).prod (stdGaussian E)) := by
  let e := gaussianCoordinates E
  have he := gaussianCoordinates_measurePreserving E
  have hrot : MeasurePreserving (rotCLM (n := Module.finrank ℝ E) s n)
      ((γFin (Module.finrank ℝ E)).prod (γFin (Module.finrank ℝ E)))
      ((γFin (Module.finrank ℝ E)).prod (γFin (Module.finrank ℝ E))) :=
    ⟨(rotCLM s n).continuous.measurable, rotCLM_map_coeff s n hsn⟩
  have hh := (he.prod he).comp (hrot.comp ((he.symm e).prod (he.symm e)))
  convert hh using 1
  funext z
  apply Prod.ext
  · change s • z.1 + n • z.2 = gaussianCoordinates E
      (mixCLM s n (e.symm z.1, e.symm z.2))
    rw [gaussianCoordinates_mix]
    simp only [e, MeasurableEquiv.apply_symm_apply]
  · change n • z.1 + (-s) • z.2 = gaussianCoordinates E
      (mixCLM n (-s) (e.symm z.1, e.symm z.2))
    rw [gaussianCoordinates_mix]
    simp only [e, MeasurableEquiv.apply_symm_apply]

/-- The actual final source rotation: P'=sY+nH and E'=-nY+sH. -/
def gaussianRotate (s n : ℝ) (z : E × E) : E × E :=
  (s • z.1 + n • z.2, (-n) • z.1 + s • z.2)

theorem gaussianRotate_measurePreserving (s n : ℝ) (hsn : s ^ 2 + n ^ 2 = 1) :
    MeasurePreserving (gaussianRotate (E := E) s n)
      ((stdGaussian E).prod (stdGaussian E)) ((stdGaussian E).prod (stdGaussian E)) := by
  have hn : MeasurePreserving (fun x : E => -x) (stdGaussian E) (stdGaussian E) :=
    ⟨continuous_neg.measurable, stdGaussian_map (LinearIsometryEquiv.neg ℝ)⟩
  have hh := ((MeasurePreserving.id (stdGaussian E)).prod hn).comp
    (gaussianSplit_measurePreserving (E := E) s n hsn)
  convert hh using 1
  funext z
  apply Prod.ext
  · rfl
  · change (-n) • z.1 + s • z.2 = -(n • z.1 + (-s) • z.2)
    module

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- At the initial clock time the visible momentum is exactly the supplied P;
only the unused hidden Gaussian changes sign. -/
theorem gaussianRotate_split (s n : ℝ) (hsn : s ^ 2 + n ^ 2 = 1) (z : E × E) :
    gaussianRotate s n (gaussianSplit s n z) = (z.1, -z.2) := by
  have hh := gaussianSplit_involutive (E := E) s n hsn z
  apply Prod.ext
  · simpa only [gaussianRotate, gaussianSplit] using congrArg (fun w : E × E => w.1) hh
  · calc
      _ = -((gaussianSplit s n (gaussianSplit s n z)).2) := by
        change (-n) • (s • z.1 + n • z.2) + s • (n • z.1 + (-s) • z.2) =
          -(n • (s • z.1 + n • z.2) + (-s) • (n • z.1 + (-s) • z.2))
        module
      _ = -z.2 := congrArg Neg.neg (congrArg (fun w : E × E => w.2) hh)

/-- The split is an actual continuous involution. -/
def gaussianSplitHomeomorph (s n : ℝ) (hsn : s ^ 2 + n ^ 2 = 1) : (E × E) ≃ₜ (E × E) where
  toFun := gaussianSplit s n
  invFun := gaussianSplit s n
  left_inv := gaussianSplit_involutive s n hsn
  right_inv := gaussianSplit_involutive s n hsn
  continuous_toFun := by unfold gaussianSplit; fun_prop
  continuous_invFun := by unfold gaussianSplit; fun_prop

/-- The final rotation is the split followed by negation of its hidden output. -/
def gaussianRotateHomeomorph (s n : ℝ) (hsn : s ^ 2 + n ^ 2 = 1) : (E × E) ≃ₜ (E × E) :=
  (gaussianSplitHomeomorph s n hsn).trans
    ((Homeomorph.refl E).prodCongr (LinearIsometryEquiv.neg ℝ : E ≃ₗᵢ[ℝ] E).toHomeomorph)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem gaussianRotateHomeomorph_apply (s n : ℝ) (hsn : s ^ 2 + n ^ 2 = 1) (z : E × E) :
    gaussianRotateHomeomorph s n hsn z = gaussianRotate s n z := by
  apply Prod.ext
  · rfl
  · change -(n • z.1 + (-s) • z.2) = (-n) • z.1 + s • z.2
    module

/-- Lift a momentum-pair transformation while retaining position exactly. -/
def phaseMomentumMap (f : E × E → E × E) (z : GaussianPhase E) : GaussianPhase E :=
  ((z.1.1, (f (z.1.2, z.2)).1), (f (z.1.2, z.2)).2)

omit [BorelSpace E] in
theorem phaseMomentumMap_measurePreserving (μ : Measure E) [SFinite μ]
    (f : E × E → E × E)
    (hf : MeasurePreserving f ((stdGaussian E).prod (stdGaussian E))
      ((stdGaussian E).prod (stdGaussian E))) :
    MeasurePreserving (phaseMomentumMap f) (gaussianPhaseMeasure μ) (gaussianPhaseMeasure μ) := by
  have ha := measurePreserving_prodAssoc μ (stdGaussian E) (stdGaussian E)
  exact (ha.symm MeasurableEquiv.prodAssoc).comp
    (((MeasurePreserving.id μ).prod hf).comp ha)

/-- Actual full-phase split preserving the reference product. -/
def phaseSplit (s n : ℝ) (hsn : s ^ 2 + n ^ 2 = 1) : GaussianPhase E ≃ₜ GaussianPhase E :=
  (Homeomorph.prodAssoc E E E).trans
    (((Homeomorph.refl E).prodCongr (gaussianSplitHomeomorph s n hsn)).trans
      (Homeomorph.prodAssoc E E E).symm)

/-- Actual full-phase final rotation. -/
def phaseRotate (s n : ℝ) (hsn : s ^ 2 + n ^ 2 = 1) : GaussianPhase E ≃ₜ GaussianPhase E :=
  (Homeomorph.prodAssoc E E E).trans
    (((Homeomorph.refl E).prodCongr (gaussianRotateHomeomorph s n hsn)).trans
      (Homeomorph.prodAssoc E E E).symm)

theorem phaseSplit_measurePreserving (μ : Measure E) [SFinite μ] (s n : ℝ) (hsn : s ^ 2 + n ^ 2 = 1) :
    MeasurePreserving (phaseSplit (E := E) s n hsn)
      (gaussianPhaseMeasure μ) (gaussianPhaseMeasure μ) :=
  phaseMomentumMap_measurePreserving μ _ (gaussianSplit_measurePreserving s n hsn)

theorem phaseRotate_measurePreserving (μ : Measure E) [SFinite μ] (s n : ℝ) (hsn : s ^ 2 + n ^ 2 = 1) :
    MeasurePreserving (phaseRotate (E := E) s n hsn)
      (gaussianPhaseMeasure μ) (gaussianPhaseMeasure μ) := by
  have he : (phaseRotate (E := E) s n hsn : GaussianPhase E → GaussianPhase E) =
      phaseMomentumMap (gaussianRotate s n) := by
    funext z
    change ((z.1.1, (gaussianRotateHomeomorph s n hsn (z.1.2, z.2)).1),
      (gaussianRotateHomeomorph s n hsn (z.1.2, z.2)).2) = _
    rw [gaussianRotateHomeomorph_apply]
    rfl
  rw [he]
  exact phaseMomentumMap_measurePreserving μ _ (gaussianRotate_measurePreserving s n hsn)

/-- Actual L2 unitary taking the final (P,E) coordinates back to (Y,H). -/
def phaseRotationPullback (μ : Measure E) [SFinite μ] (s n : ℝ) (hsn : s ^ 2 + n ^ 2 = 1) :
    Lp ℝ 2 (gaussianPhaseMeasure μ) ≃ₗᵢ[ℝ] Lp ℝ 2 (gaussianPhaseMeasure μ) :=
  pullback (phaseRotate (E := E) s n hsn).toMeasurableEquiv
    (phaseRotate_measurePreserving μ s n hsn)

/-- The manuscript's fixed split coefficients satisfy exact orthogonality. -/
theorem source_split_coefficients : (1 / 2 : ℝ) ^ 2 + (Real.sqrt 3 / 2) ^ 2 = 1 := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  nlinarith

end AcceleratedLogConcave.Kinetic
