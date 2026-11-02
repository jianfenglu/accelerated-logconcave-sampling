import AcceleratedLogConcave.Analysis.ActualAngleSourcePullback

/-! New common-seed L² quotient pullback with its exact physical amplitude. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ContDiff
namespace AcceleratedLogConcave.Numerics.MeanFlowLp
open Conditional Analysis.AnglePhase CenterMeanSecondJetSource AffineGraph
variable {D m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))

theorem continuous_parameterDisplacement_actual (d : Data (Fin D) m) (k : d.G.Kernel)
    (a : ℝ) : Continuous (parameterDisplacement (angleEndpoint d k) (d.G.rotationScale k) a) := by
  change Continuous (fun p : E × EP => a⁻¹ • angleEmbed
    (angleEndpoint d k (p.1+d.G.rotationScale k • phasePositionCLM p.2) -
      (p.1+d.G.rotationScale k • phasePositionCLM p.2)))
  have hT := (contDiff_angleEndpoint d k).continuous
  exact (angleEmbed.continuous.comp ((hT.comp
    (continuous_fst.add ((phasePositionCLM.continuous.comp continuous_snd).const_smul (d.G.rotationScale k)))).sub
    (continuous_fst.add ((phasePositionCLM.continuous.comp continuous_snd).const_smul (d.G.rotationScale k))))).const_smul a⁻¹

theorem parameterDisplacement_memLp_original_data (d : Data (Fin D) m) (j : Fin m)
    (k : d.G.Kernel) (a : ℝ) :
    MemLp (parameterDisplacement (angleEndpoint d k) (d.G.rotationScale k) a) 2
      ((angleMidpointLaw d k).prod (stdGaussian EP)) := by
  have hp := angleSeedCoordinates_preserving d j k
  rw [← hp.map_eq]
  apply (memLp_map_measure_iff
    (continuous_parameterDisplacement_actual d k a).aestronglyMeasurable hp.aemeasurable).mpr
  have he := ((action_memLp d j k 0).continuousLinearMap_comp angleEmbed).const_smul a⁻¹
  convert he using 1
  funext w
  have h := parameterDisplacement_actual_seed d j k a 0 w
  simpa only [parameterRotation,rotationOrbit_zero,Prod.mk.eta,Function.comp_def,Pi.smul_apply] using h

def angleLpPullback (d : Data (Fin D) m) (j : Fin m) (k : d.G.Kernel) (a : ℝ) :
    Lp EP 2 ((angleMidpointLaw d k).prod (stdGaussian EP)) →L[ℝ] Lp E 2 (seedMeasure d) :=
  a • ((phasePositionCLM.compLpL 2 (seedMeasure d)).comp
    (Lp.compMeasurePreservingₗᵢ ℝ (angleSeedCoordinates d j k)
      (angleSeedCoordinates_preserving d j k)).toContinuousLinearMap)

theorem phasePositionCLM_angleEmbed (v : E) : phasePositionCLM (angleEmbed v) = v := by
  simp [phasePositionCLM,angleEmbed_apply]

theorem norm_phasePositionCLM_apply_le (z : EP) : ‖phasePositionCLM z‖ ≤ ‖z‖ := by
  change ‖(phaseCoordinateEquiv z).fst‖ ≤ ‖z‖
  simpa only [LinearIsometryEquiv.norm_map] using WithLp.norm_fst_le E (phaseCoordinateEquiv z)

theorem norm_phasePositionCLM_le_one : ‖(phasePositionCLM : EP →L[ℝ] E)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by intro z; simpa using norm_phasePositionCLM_apply_le z)

theorem norm_angleLpPullback_apply_le (d : Data (Fin D) m) (j : Fin m) (k : d.G.Kernel)
    (a : ℝ) (f : Lp EP 2 ((angleMidpointLaw d k).prod (stdGaussian EP))) :
    ‖angleLpPullback d j k a f‖ ≤ ‖a‖ * ‖f‖ := by
  simp only [angleLpPullback,smul_apply,ContinuousLinearMap.comp_apply,norm_smul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg a)
  apply (ContinuousLinearMap.norm_compLp_le _ _).trans
  change ‖phasePositionCLM‖ * ‖(Lp.compMeasurePreservingₗᵢ ℝ (angleSeedCoordinates d j k)
    (angleSeedCoordinates_preserving d j k)) f‖ ≤ ‖f‖
  rw [LinearIsometry.norm_map]
  exact (mul_le_mul_of_nonneg_right norm_phasePositionCLM_le_one (norm_nonneg f)).trans_eq (one_mul _)

theorem actionLp_eq_angleLpPullback (d : Data (Fin D) m) (j : Fin m)
    (k : d.G.Kernel) (a : ℝ) (ha : a ≠ 0) (t : ℝ) :
    actionLp d j k t = angleLpPullback d j k a
      (displacementLp (angleMidpointLaw d k) (angleEndpoint d k) (d.G.rotationScale k) a
        (parameterDisplacement_memLp_original_data d j k a) t) := by
  let f := parameterDisplacement (angleEndpoint d k) (d.G.rotationScale k) a
  have hf := parameterDisplacement_memLp_original_data d j k a
  have hrot := hf.comp_measurePreserving (parameterRotation_preserving (angleMidpointLaw d k) (d.G.rotationScale k) t)
  have hp := hrot.comp_measurePreserving (angleSeedCoordinates_preserving d j k)
  apply Lp.ext
  have h1 := (action_memLp d j k t).coeFn_toLp
  have h2 := hp.coeFn_toLp
  have h3 := (phasePositionCLM : EP →L[ℝ] E).coeFn_compLp (hp.toLp _)
  have h4 := Lp.coeFn_smul a ((phasePositionCLM : EP →L[ℝ] E).compLp (hp.toLp _))
  filter_upwards [h1,h2,h3,h4] with w hw1 hw2 hw3 hw4
  change actionLp d j k t w = (a • (phasePositionCLM.compLp (hp.toLp _))) w
  change ((action_memLp d j k t).toLp _) w = _
  rw [hw1,hw4]
  change action d j k t w = a • (phasePositionCLM.compLp (hp.toLp _)) w
  rw [hw3,hw2]
  change action d j k t w = a • phasePositionCLM
    (parameterDisplacement _ _ _ (parameterRotation _ _ (angleSeedCoordinates d j k w)))
  rw [parameterDisplacement_actual_seed,map_smul,phasePositionCLM_angleEmbed,smul_smul,mul_inv_cancel₀ ha,one_smul]
end AcceleratedLogConcave.Numerics.MeanFlowLp
