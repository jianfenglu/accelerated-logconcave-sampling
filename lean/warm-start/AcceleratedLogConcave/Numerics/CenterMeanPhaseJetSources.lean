import AcceleratedLogConcave.Numerics.CenterMeanPhaseMomentTransfer
import AcceleratedLogConcave.Numerics.CenterMeanPhaseOriginalSourceIdentity
import AcceleratedLogConcave.Tensor.PhaseVectorSourceRegularity

/-! Actual projected and physically scaled source-jet ladder. Its L² membership
comes from the primitive split supplier and actual Gibbs moments, never from a
hypothesis asserting the desired source energies. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Conditional CenteringFlowLp Tensor Tensor.PhaseExpression Tensor.PhaseSourceJetInduction
open Tensor.CoordinateReduction Tensor.PhaseGeneratorIdentification Tensor.Ordered.Graph
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))
local notation "P" => WithLp 2 (E × E)

def phaseSourceJet (d : Data (Fin D)) (L a s : ℝ) (k : ℕ) (z : EP) : E :=
  (a*(L/s)^(k+1)) • phasePositionCLM
    (vectorSection (phaseCoefficients d L a) (phasePotential d) (jet F k) z)

def seedSourceJet (d : Data (Fin D)) (L a s : ℝ) (k : ℕ) (z : P) : E :=
  phaseSourceJet d L a s k (phaseCoordinateEquiv.symm z)

theorem phaseSourceJet_contDiff (d : Data (Fin D)) (L a s : ℝ) (k : ℕ) :
    ContDiff ℝ ∞ (phaseSourceJet d L a s k) := by
  change ContDiff ℝ ∞ (fun z => (a*(L/s)^(k+1)) • phasePositionCLM
    (vectorSection (phaseCoefficients d L a) (phasePotential d) (jet F k) z))
  exact (contDiff_const : ContDiff ℝ ∞ (fun _ : EP => a*(L/s)^(k+1))).smul
    (phasePositionCLM.contDiff.comp
      (contDiff_vectorSection _ _ (phaseCoefficients_smooth d L a)
        (smooth_phasePotential d) (jet F k)))

theorem seedSourceJet_contDiff (d : Data (Fin D)) (L a s : ℝ) (k : ℕ) :
    ContDiff ℝ ∞ (seedSourceJet d L a s k) :=
  (phaseSourceJet_contDiff d L a s k).comp
    phaseCoordinateEquiv.symm.toContinuousLinearEquiv.contDiff

theorem phaseSourceJet_memLp (d : Data (Fin D)) (L a s : ℝ) {c R : ℝ}
    (hb : PhasePrimitiveBudgets (phaseCoefficients d L a) (phasePotential d) c R) (k : ℕ) :
    MemLp (phaseSourceJet d L a s k) 2 (phaseSeedLaw d) := by
  have h := memLp_vectorSection (phaseEnvironmentOfSplitBudgets d L a hb) (jet F k)
  rw [phaseEnvironmentOfSplitBudgets_law] at h
  dsimp only [phaseEnvironmentOfSplitBudgets,actualPhaseAnalyticEnvironmentOfBudgets,
    actualPhaseGibbsEnvironment] at h
  exact (h.continuousLinearMap_comp phasePositionCLM).const_smul (a*(L/s)^(k+1))

theorem seedSourceJet_memLp (d : Data (Fin D)) (L a s : ℝ) {c R : ℝ}
    (hb : PhasePrimitiveBudgets (phaseCoefficients d L a) (phasePotential d) c R) (k : ℕ) :
    MemLp (seedSourceJet d L a s k) 2 (seedMeasure d) := by
  have hm : MeasurePreserving phaseCoordinateEquiv.symm (seedMeasure d) (phaseSeedLaw d) :=
    ⟨phaseCoordinateEquiv.symm.continuous.measurable,rfl⟩
  exact (phaseSourceJet_memLp d L a s hb k).comp_measurePreserving hm

theorem hasDerivAt_phaseOrbit_generator (d : Data (Fin D)) (L a s : ℝ)
    (hL : L ≠ 0) (hs : 0 < s) (z : EP) (t : ℝ) :
    HasDerivAt (phaseOrbit d s hs z)
      ((L/s) • SkewCoordinateGenerator.velocity (coordinateDirection (D+D))
        (transportEntry (phaseCoefficients d L a)) (phasePotential d)
        (phaseOrbit d s hs z t)) t := by
  have hdir : coordinateDirection (D+D) = EuclideanSpace.basisFun (Fin (D+D)) ℝ := by
    funext i
    simp [coordinateDirection,EuclideanSpace.basisFun_apply,EuclideanSpace.single]
  have he : transportEntry (phaseCoefficients d L a) = phaseTransportEntry d L :=
    funext fun i => funext fun j => phaseCoefficients_transport d L a i j
  have hZ := hasDerivAt_phaseOrbit d s hs z t
  rw [phaseVelocity_eq_normalized_generator d L s hL (ne_of_gt hs)] at hZ
  rw [← hdir,← he] at hZ
  exact hZ

theorem hasDerivAt_phaseSourceJet (d : Data (Fin D)) (L a s : ℝ)
    (hL : L ≠ 0) (hs : 0 < s) (k : ℕ) (z : EP) (t : ℝ) :
    HasDerivAt (fun u => phaseSourceJet d L a s k (phaseOrbit d s hs z u))
      (phaseSourceJet d L a s (k+1) (phaseOrbit d s hs z t)) t := by
  have hZ := hasDerivAt_phaseOrbit_generator d L a s hL hs z t
  have hv := hasDerivAt_vectorSection_along (phaseCoefficients d L a) (phasePotential d)
    (phaseCoefficients_smooth d L a) (smooth_phasePotential d)
    (fun x i j => phaseTransportEntry_skew d L x i j) (jet F k) hZ
  have hp := phasePositionCLM.hasFDerivAt.comp_hasDerivAt t hv
  have h := hp.const_smul (a*(L/s)^(k+1))
  convert h using 1
  · funext u
    rfl
  · simp only [phaseSourceJet,jet,map_smul,smul_smul,pow_succ,mul_assoc]

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
