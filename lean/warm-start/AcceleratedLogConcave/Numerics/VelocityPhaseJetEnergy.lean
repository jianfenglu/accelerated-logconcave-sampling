import AcceleratedLogConcave.Numerics.CenterMeanPhaseJetEnergy
import AcceleratedLogConcave.Numerics.VelocityPhaseJetLp

/-! Exact physical scaling and one square-root-dimension budget for the
connected source ladder, conditional on genuine primitive split bounds. -/
noncomputable section
open MeasureTheory
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Conditional CenteringFlowLp Tensor Tensor.PhaseExpression Tensor.PhaseSourceJetInduction
open Tensor.AdjointReduction Tensor.Ordered.Graph
variable {D : ℕ}
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))

def velocityJetEnergyScale (L s c R : ℝ) (k : ℕ) : ℝ :=
  2*((L/s)^(k+1))^2 * PhaseBudget.Q c (5*(k+1)+1) * R^(-2*(2*(k:ℝ)+1))

theorem velocityJetEnergyScale_nonneg (L s : ℝ) {c R : ℝ}
    (hc : 0 ≤ c) (hR : 0 ≤ R) (k : ℕ) : 0 ≤ velocityJetEnergyScale L s c R k :=
  mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (PhaseBudget.Q_nonneg hc _)) (Real.rpow_nonneg hR _)

theorem integral_phaseVelocityJet_norm_sq_le (d : Data (Fin D)) (L a s : ℝ) {c R : ℝ}
    (hc : 1 ≤ c) (hR : 0 < R) (hR1 : R ≤ 1)
    (hb : PhasePrimitiveBudgets (phaseCoefficients d L a) (phasePotential d) c R) (k : ℕ) :
    (∫ z, ‖phaseVelocityJet d L a s k z‖^2 ∂phaseSeedLaw d) ≤
      (D:ℝ)*velocityJetEnergyScale L s c R k := by
  let v := vectorSection (phaseCoefficients d L a) (phasePotential d) (jet Tensor.PhaseExpression.P k)
  have hv : MemLp v 2 (phaseSeedLaw d) := by
    have h := memLp_vectorSection (phaseEnvironmentOfSplitBudgets d L a hb) (jet Tensor.PhaseExpression.P k)
    rw [phaseEnvironmentOfSplitBudgets_law] at h
    simpa only [v,phaseEnvironmentOfSplitBudgets,actualPhaseAnalyticEnvironmentOfBudgets,
      actualPhaseGibbsEnvironment] using h
  have hv2 := (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mp hv
  have hf := phaseVelocityJet_memLp d L a s hb k
  have hf2 := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hmono : (∫ z, ‖phaseVelocityJet d L a s k z‖^2 ∂phaseSeedLaw d) ≤
      ((L/s)^(k+1))^2 * (∫ z, ‖v z‖^2 ∂phaseSeedLaw d) := by
    rw [← integral_const_mul]
    apply integral_mono hf2 (hv2.const_mul _)
    intro z
    simp only [phaseVelocityJet,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
    exact mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
        (norm_phasePositionCLM_le (v z))) (by positivity)
  have hm := mul_le_mul_of_nonneg_left
    (actual_phase_position_jet_moment d L a hc hR hR1 hb k)
    (sq_nonneg ((L/s)^(k+1)))
  apply hmono.trans
  convert hm using 1
  simp only [velocityJetEnergyScale,Nat.cast_add]
  ring

theorem norm_velocityJetLp_sq_le (d : Data (Fin D)) (L a s : ℝ) (hs : 0 < s) {c R : ℝ}
    (hc : 1 ≤ c) (hR : 0 < R) (hR1 : R ≤ 1)
    (hb : PhasePrimitiveBudgets (phaseCoefficients d L a) (phasePotential d) c R)
    (k : ℕ) (t : ℝ) :
    ‖velocityJetLp d L a s hs hb k t‖^2 ≤ (D:ℝ)*velocityJetEnergyScale L s c R k := by
  change ‖CenterMeanStationaryLp.orbit d s hs _ t‖^2 ≤ _
  rw [CenterMeanStationaryLp.norm_orbit,Analysis.DominatedLp.norm_sq_toLp]
  have hm : MeasurePreserving phaseCoordinateEquiv.symm (seedMeasure d) (phaseSeedLaw d) :=
    ⟨phaseCoordinateEquiv.symm.continuous.measurable,rfl⟩
  have he := hm.integral_comp
    phaseCoordinateEquiv.symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun z => ‖phaseVelocityJet d L a s k z‖^2)
  change (∫ z, ‖seedVelocityJet d L a s k z‖^2 ∂seedMeasure d) =
    (∫ z, ‖phaseVelocityJet d L a s k z‖^2 ∂phaseSeedLaw d) at he
  rw [he]
  exact integral_phaseVelocityJet_norm_sq_le d L a s hc hR hR1 hb k

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
