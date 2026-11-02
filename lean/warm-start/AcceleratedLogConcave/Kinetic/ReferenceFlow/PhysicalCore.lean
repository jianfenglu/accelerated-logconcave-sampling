import AcceleratedLogConcave.Kinetic.ReferenceFlow.PhaseCoordinates
import AcceleratedLogConcave.Kinetic.ReferenceFlow
import AcceleratedLogConcave.Kinetic.ReferenceCorrector

/-! Strong differentiation of the actual physical-phase transported compact core.
The full and pure-heat fields are constructed from the same Gibbs family. -/
noncomputable section
open Set Function MeasureTheory InnerProductSpace
open scoped NNReal
open OAI.LogConcaveSampling.GlobalODE
namespace AcceleratedLogConcave.Kinetic
open Analysis.Poisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {a b : ℝ} (F : ReferencePoissonFamily E a b) (ell s n : ℝ) (hsn : s^2+n^2=1)

 theorem physicalDrift_continuous :
    Continuous (uncurry (physicalPhaseDrift F.potential ell F.scale s n hsn)) :=
  conjugateDrift_continuous _ (extendDrift_continuous
    (coupledDrift_continuous F.potential ell F.scale F.gradient_continuous F.scale_continuous))

 theorem physicalDrift_lipschitz (t : ℝ) (ht : t ∈ Icc a b) :
    LipschitzWith (conjugateLipschitzConstant (physicalPhaseCoordinates (E := E) s n hsn)
      (2 * ‖ell‖₊ + F.scaleBound)) (physicalPhaseDrift F.potential ell F.scale s n hsn t) :=
  conjugateDrift_lipschitz _ (extendDrift_lipschitz
    (coupledDrift_lipschitz F.potential ell F.scale t (F.potential_C2 t)
      (F.hessian_nonneg t ht) (F.hessian_upper t ht) F.scaleBound (F.scale_bounded t ht)))

def physicalDriftDerivative := conjugateDriftDerivative (physicalPhaseCoordinates (E := E) s n hsn)
  (extendDriftDerivative (Y := E) (coupledDriftDerivative F.potential ell F.scale))

 theorem physicalDriftDerivative_continuous :
    Continuous (uncurry (physicalDriftDerivative F ell s n hsn)) :=
  conjugateDriftDerivative_continuous _ (extendDriftDerivative_continuous
    (coupledDriftDerivative_continuous F.potential ell F.scale F.hessian_continuous F.scale_continuous))

 theorem physicalDrift_hasFDerivAt (t : ℝ) (z : GaussianPhase E) :
    HasFDerivAt (physicalPhaseDrift F.potential ell F.scale s n hsn t)
      (physicalDriftDerivative F ell s n hsn t z) z :=
  conjugateDrift_hasFDerivAt _ (extendDrift_hasFDerivAt
    (fun u x => coupledDrift_hasFDerivAt F.potential ell F.scale u x (F.potential_C2 u))) t z

/-- Actual transported test, viewed in the pure-heat flow frame. -/
def physicalMovingCore (T : Icc a b) (φ : GaussianPhase E → ℝ) :=
  movingFrameCore F.ordered (physicalDrift_continuous F ell s n hsn)
    (physicalDrift_continuous F 0 s n hsn) (physicalDrift_lipschitz F ell s n hsn)
    (physicalDrift_lipschitz F 0 s n hsn) T φ

/-- Its actual L2 class under the initial reference phase law. -/
def physicalMovingCoreLp (T : Icc a b) {φ : GaussianPhase E → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) :=
  movingFrameCoreLp F.ordered (physicalDrift_continuous F ell s n hsn)
    (physicalDrift_continuous F 0 s n hsn) (physicalDrift_lipschitz F ell s n hsn)
    (physicalDrift_lipschitz F 0 s n hsn) (gaussianPhaseMeasure (F.law a)) T hφ hc

 theorem physicalMovingCoreLp_hasDerivAt (T : Icc a b) {φ : GaussianPhase E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (t : ℝ) (ht : t ∈ Ioo a b) :
    ∃ d : Lp ℝ 2 (gaussianPhaseMeasure (F.law a)),
      HasDerivAt (physicalMovingCoreLp F ell s n hsn T hφ.continuous hc) d t ∧
      ∀ᵐ z ∂gaussianPhaseMeasure (F.law a),
        d z = fderiv ℝ (physicalMovingCore F ell s n hsn T φ) (t,z) (1,0) := by
  let hd := movingFrameCore_derivative_memLp F.ordered
    (physicalDrift_continuous F ell s n hsn) (physicalDrift_continuous F 0 s n hsn)
    (physicalDrift_lipschitz F ell s n hsn) (physicalDrift_lipschitz F 0 s n hsn)
    (physicalDriftDerivative_continuous F ell s n hsn) (physicalDriftDerivative_continuous F 0 s n hsn)
    (physicalDrift_hasFDerivAt F ell s n hsn) (physicalDrift_hasFDerivAt F 0 s n hsn)
    (gaussianPhaseMeasure (F.law a)) T hφ hc t ht
  refine ⟨hd.toLp _, ?_, hd.coeFn_toLp⟩
  exact movingFrameCoreLp_hasDerivAt F.ordered
    (physicalDrift_continuous F ell s n hsn) (physicalDrift_continuous F 0 s n hsn)
    (physicalDrift_lipschitz F ell s n hsn) (physicalDrift_lipschitz F 0 s n hsn)
    (physicalDriftDerivative_continuous F ell s n hsn) (physicalDriftDerivative_continuous F 0 s n hsn)
    (physicalDrift_hasFDerivAt F ell s n hsn) (physicalDrift_hasFDerivAt F 0 s n hsn)
    (gaussianPhaseMeasure (F.law a)) T hφ hc t ht

/-- The quadratic corrector has a genuine derivative along the constructed
transported core; no differentiability premise on an abstract density is needed. -/
theorem physicalMovingCore_corrector_hasDerivAt (T : Icc a b) {φ : GaussianPhase E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (t : ℝ) (ht : t ∈ Ioo a b) :
    ∃ d : Lp ℝ 2 (gaussianPhaseMeasure (F.law a)),
      HasDerivAt (physicalMovingCoreLp F ell s n hsn T hφ.continuous hc) d t ∧
      HasDerivAt (fun u => inner ℝ
        (physicalMovingCoreLp F ell s n hsn T hφ.continuous hc u)
        (F.corrector u (physicalMovingCoreLp F ell s n hsn T hφ.continuous hc u)))
        (inner ℝ d (F.corrector t (physicalMovingCoreLp F ell s n hsn T hφ.continuous hc t)) +
         inner ℝ (physicalMovingCoreLp F ell s n hsn T hφ.continuous hc t) (F.corrector t d) +
         inner ℝ (physicalMovingCoreLp F ell s n hsn T hφ.continuous hc t)
           (F.materialCorrector t ht (physicalMovingCoreLp F ell s n hsn T hφ.continuous hc t))) t := by
  obtain ⟨d, hd, _⟩ := physicalMovingCoreLp_hasDerivAt F ell s n hsn T hφ hc t ht
  exact ⟨d, hd, F.corrector_quadratic_hasDerivAt t ht _ d hd⟩

end AcceleratedLogConcave.Kinetic
