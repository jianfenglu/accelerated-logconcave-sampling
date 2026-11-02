import AcceleratedLogConcave.Kinetic.ReferenceFlow.TransportIntegral
import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.Bounds

/-! The transported initial compact test is exactly its original L2 class. -/
noncomputable section
open Set MeasureTheory
open OAI.LogConcaveSampling.GlobalODE
namespace AcceleratedLogConcave.Kinetic
open Analysis.Poisson Reheating
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {a b : ℝ} (F : ReferencePoissonFamily E a b) (ell s n : ℝ) (hsn : s^2+n^2=1)

theorem physicalMovingCore_initial (φ : GaussianPhase E → ℝ) (z : GaussianPhase E) :
    physicalMovingCore F ell s n hsn F.leftTime φ (a,z) = φ z := by
  unfold physicalMovingCore movingFrameCore
  rw [backwardTest_eq]
  simp only [spaceTimeForward]
  rw [projIcc_of_mem F.ordered (show a ∈ Icc a b from ⟨le_rfl,F.ordered⟩)]
  change φ (flow (physicalDrift_lipschitz F ell s n hsn)
    (physicalDrift_continuous F ell s n hsn) F.leftTime
      (flow (physicalDrift_lipschitz F 0 s n hsn)
        (physicalDrift_continuous F 0 s n hsn) F.leftTime z a) a) = φ z
  have hzero := flow_initial (physicalDrift_lipschitz F 0 s n hsn)
    (physicalDrift_continuous F 0 s n hsn) F.leftTime z
  change flow (physicalDrift_lipschitz F 0 s n hsn)
    (physicalDrift_continuous F 0 s n hsn) F.leftTime z a = z at hzero
  rw [hzero]
  exact congrArg φ (flow_initial (physicalDrift_lipschitz F ell s n hsn)
    (physicalDrift_continuous F ell s n hsn) F.leftTime z)

theorem physicalMovingCoreLp_initial {φ : GaussianPhase E → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    physicalMovingCoreLp F ell s n hsn F.leftTime hφ hc a =
      compactTestL2 (gaussianPhaseMeasure (F.law a)) φ hφ hc := by
  apply Lp.ext
  filter_upwards [(movingFrameCore_memLp F.ordered
      (physicalDrift_continuous F ell s n hsn) (physicalDrift_continuous F 0 s n hsn)
      (physicalDrift_lipschitz F ell s n hsn) (physicalDrift_lipschitz F 0 s n hsn)
      (gaussianPhaseMeasure (F.law a)) F.leftTime hφ hc a).coeFn_toLp,
    (compactTest_memLp (gaussianPhaseMeasure (F.law a)) φ hφ hc).coeFn_toLp] with z hz hφz
  change physicalMovingCoreLp F ell s n hsn F.leftTime hφ hc a z = _ at hz ⊢
  change compactTestL2 (gaussianPhaseMeasure (F.law a)) φ hφ hc z = φ z at hφz
  rw [hz,hφz]
  exact physicalMovingCore_initial F ell s n hsn φ z

end AcceleratedLogConcave.Kinetic
