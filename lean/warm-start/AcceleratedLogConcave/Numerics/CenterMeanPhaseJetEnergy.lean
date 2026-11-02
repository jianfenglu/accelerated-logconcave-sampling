import AcceleratedLogConcave.Numerics.CenterMeanPhaseJetLp

/-! Exact physical scaling and one square-root-dimension budget for the
connected source ladder, conditional on genuine primitive split bounds. -/
noncomputable section
open MeasureTheory
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Conditional CenteringFlowLp Tensor Tensor.PhaseExpression Tensor.PhaseSourceJetInduction
open Tensor.AdjointReduction Tensor.Ordered.Graph
variable {D : ℕ}
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))

def sourceJetEnergyScale (L a s c R : ℝ) (k : ℕ) : ℝ :=
  2*(a*(L/s)^(k+1))^2 * PhaseBudget.Q c (5*(k+1)+1) * R^(-4*((k:ℝ)+1))

theorem sourceJetEnergyScale_nonneg (L a s : ℝ) {c R : ℝ}
    (hc : 0 ≤ c) (hR : 0 ≤ R) (k : ℕ) : 0 ≤ sourceJetEnergyScale L a s c R k :=
  mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (PhaseBudget.Q_nonneg hc _)) (Real.rpow_nonneg hR _)

theorem norm_phasePositionCLM_le (z : EP) : ‖phasePositionCLM z‖ ≤ ‖z‖ := by
  simpa only [phasePositionCLM_apply,phasePosition,WithLp.fst,LinearIsometryEquiv.norm_map] using
    WithLp.norm_fst_le (EuclideanSpace ℝ (Fin D)) (phaseCoordinateEquiv z)

theorem integral_phaseSourceJet_norm_sq_le (d : Data (Fin D)) (L a s : ℝ) {c R : ℝ}
    (hc : 1 ≤ c) (hR : 0 < R) (hR1 : R ≤ 1)
    (hb : PhasePrimitiveBudgets (phaseCoefficients d L a) (phasePotential d) c R) (k : ℕ) :
    (∫ z, ‖phaseSourceJet d L a s k z‖^2 ∂phaseSeedLaw d) ≤
      (D:ℝ)*sourceJetEnergyScale L a s c R k := by
  let v := vectorSection (phaseCoefficients d L a) (phasePotential d) (jet F k)
  have hv : MemLp v 2 (phaseSeedLaw d) := by
    have h := memLp_vectorSection (phaseEnvironmentOfSplitBudgets d L a hb) (jet F k)
    rw [phaseEnvironmentOfSplitBudgets_law] at h
    simpa only [v,phaseEnvironmentOfSplitBudgets,actualPhaseAnalyticEnvironmentOfBudgets,
      actualPhaseGibbsEnvironment] using h
  have hv2 := (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mp hv
  have hf := phaseSourceJet_memLp d L a s hb k
  have hf2 := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hmono : (∫ z, ‖phaseSourceJet d L a s k z‖^2 ∂phaseSeedLaw d) ≤
      (a*(L/s)^(k+1))^2 * (∫ z, ‖v z‖^2 ∂phaseSeedLaw d) := by
    rw [← integral_const_mul]
    apply integral_mono hf2 (hv2.const_mul _)
    intro z
    simp only [phaseSourceJet,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
    exact mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
        (norm_phasePositionCLM_le (v z))) (by positivity)
  have hm := mul_le_mul_of_nonneg_left
    (actual_phase_observable_jet_moment d L a hc hR hR1 hb k)
    (sq_nonneg (a*(L/s)^(k+1)))
  apply hmono.trans
  convert hm using 1
  simp only [sourceJetEnergyScale,Nat.cast_add]
  ring

theorem norm_sourceJetLp_sq_le (d : Data (Fin D)) (L a s : ℝ) (hs : 0 < s) {c R : ℝ}
    (hc : 1 ≤ c) (hR : 0 < R) (hR1 : R ≤ 1)
    (hb : PhasePrimitiveBudgets (phaseCoefficients d L a) (phasePotential d) c R)
    (k : ℕ) (t : ℝ) :
    ‖sourceJetLp d L a s hs hb k t‖^2 ≤ (D:ℝ)*sourceJetEnergyScale L a s c R k := by
  change ‖CenterMeanStationaryLp.orbit d s hs _ t‖^2 ≤ _
  rw [CenterMeanStationaryLp.norm_orbit,Analysis.DominatedLp.norm_sq_toLp]
  have hm : MeasurePreserving phaseCoordinateEquiv.symm (seedMeasure d) (phaseSeedLaw d) :=
    ⟨phaseCoordinateEquiv.symm.continuous.measurable,rfl⟩
  have he := hm.integral_comp
    phaseCoordinateEquiv.symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun z => ‖phaseSourceJet d L a s k z‖^2)
  change (∫ z, ‖seedSourceJet d L a s k z‖^2 ∂seedMeasure d) =
    (∫ z, ‖phaseSourceJet d L a s k z‖^2 ∂phaseSeedLaw d) at he
  rw [he]
  exact integral_phaseSourceJet_norm_sq_le d L a s hc hR hR1 hb k

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
