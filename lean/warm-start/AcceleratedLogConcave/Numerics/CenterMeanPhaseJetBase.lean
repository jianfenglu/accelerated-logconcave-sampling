import AcceleratedLogConcave.Numerics.CenterMeanPhaseJetLp
import AcceleratedLogConcave.Numerics.CenterMeanFirstLp
import AcceleratedLogConcave.Tensor.PhaseVectorSourceJets

/-! Literal base identification of the connected source ladder with the actual
centered-mean L² derivative. Nonzero observable normalization is explicit. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Conditional CenteringFlowLp Tensor Tensor.PhaseExpression Tensor.PhaseSourceJetInduction
open Tensor.CoordinateReduction Tensor.Ordered.Graph
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))
local notation "P" => WithLp 2 (E × E)
local notation "ep" => EuclideanSpace.basisFun (Fin (D+D)) ℝ

@[simp] theorem phasePositionCLM_embed (y : E) :
    phasePositionCLM (phaseEmbedPosition y) = y := by
  simp [phasePositionCLM_apply,phaseEmbedPosition_apply,phasePosition]

theorem phaseObservable_recover (d : Data (Fin D)) (a : ℝ) (ha : a ≠ 0) (z : EP) :
    a • phasePositionCLM (phaseObservable d a z) = M d (phasePosition z) - meanOffset d := by
  rw [phaseObservable,map_smul,phasePositionCLM_embed,smul_smul,mul_inv_cancel₀ ha,one_smul]

theorem seedSourceJet_zero_eq (d : Data (Fin D)) (L a s : ℝ)
    (hL : L ≠ 0) (ha : a ≠ 0) (hs : 0 < s) (z : P) :
    seedSourceJet d L a s 0 z = sourceFirst d s z := by
  have hΨ (i : Fin (D+D)) : ContDiff ℝ ∞ (fun x => phaseObservable d a x i) := by
    simpa only [EuclideanSpace.basisFun_inner] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : EP => ep i)).inner ℝ (smooth_phaseObservable d a)
  have hv := hasDerivAt_sourceVector_along (phaseCoefficients d L a) (phasePotential d)
    (phaseObservable d a) (phaseCoefficients_smooth d L a) hΨ
    (fun x i j => phaseTransportEntry_skew d L x i j) F
    (phaseCoefficients_observable_gradient d L a)
    (hasDerivAt_phaseOrbit_generator d L a s hL hs (phaseCoordinateEquiv.symm z) 0)
  have hp := (phasePositionCLM.hasFDerivAt.comp_hasDerivAt 0 hv).const_smul a
  have hh : HasDerivAt (fun t => centeredMean d s hs t z) (seedSourceJet d L a s 0 z) 0 := by
    convert hp using 1
    · funext t
      change centeredMean d s hs t z = a • phasePositionCLM
        (phaseObservable d a (phaseOrbit d s hs (phaseCoordinateEquiv.symm z) t))
      rw [phaseObservable_recover d a ha]
      simp [centeredMean,position,phasePosition,phaseOrbit,M]
    · simp [seedSourceJet,phaseSourceJet,phaseOrbit,phase_initial,jet,map_smul,smul_smul]
  have he := hh.unique (hasDerivAt_centeredMean d s hs 0 z)
  simpa only [first,sourceFirst,position,momentum,phase_initial] using he

theorem sourceJetLp_zero_eq_firstLp (d : Data (Fin D)) (L a s : ℝ)
    (hL : L ≠ 0) (ha : a ≠ 0) (hs : 0 < s) {c R : ℝ}
    (hb : PhasePrimitiveBudgets (phaseCoefficients d L a) (phasePotential d) c R) :
    sourceJetLp d L a s hs hb 0 = firstLp d s hs := by
  have he : seedSourceJet d L a s 0 = sourceFirst d s :=
    funext (seedSourceJet_zero_eq d L a s hL ha hs)
  have hLp := MemLp.toLp_congr (seedSourceJet_memLp d L a s hb 0)
    (sourceFirst_memLp d s) (Filter.Eventually.of_forall (fun z => congrFun he z))
  funext t
  exact congrArg (fun f => CenterMeanStationaryLp.orbit d s hs f t) hLp

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
