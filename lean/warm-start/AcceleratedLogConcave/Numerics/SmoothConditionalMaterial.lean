import AcceleratedLogConcave.Numerics.SmoothConditionalReference
import AcceleratedLogConcave.Tensor.MaterialVectorBudget

/-! The published material-expression estimate transferred to the actual
conditional seed. This module states the coordinate supplier for Fin D
explicitly; no change of coordinate index type is implicit. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace AcceleratedLogConcave.Numerics.ConditionalSmoothing
open Conditional Analysis.PositiveVarianceSlab Tensor.ActualCoefficientIntegrability
variable {D : ℕ}

/-- The explicit universal order/dimension factor inherited from the material
mass and vector RMS suppliers. The mean derivative order is k+1. -/
def materialOrderFactor (D k : ℕ) : ℝ :=
  (3*(3+3*(k:ℝ)+1)^2)^k * Real.sqrt (materialRmsNumeric D (3+3*k))

theorem materialOrderFactor_nonneg (D k : ℕ) : 0 ≤ materialOrderFactor D k := by
  unfold materialOrderFactor
  positivity

/-- Uniform in the frozen center, including affine potentials and D=0. -/
theorem integral_gaussian_jet_sq_le_material
    (d : SamplingCenterLp.Data (Fin D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (k : ℕ) (x : EuclideanSpace ℝ (Fin D)) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    (∫ z, ‖(jet d (k+2) t (x,z)).2‖^2 ∂stdGaussian (EuclideanSpace ℝ (Fin D))) ≤
      ((d.ell*d.r^2)*materialOrderFactor D k/(1-t^2)^(k+1))^2 := by
  have hv : 0 < 1-t^2 := conditionalVariance_pos
    (by linarith [ht.1]) (ht.2.trans_lt d.hb1)
  have hM0 : 0 ≤ Real.sqrt (materialRmsNumeric D (3+3*k))/(1-t^2)^(k+1) := by
    positivity
  have hh := positionJetLp_norm_le_massBudget (fixedData d x) hsmall k ht hM0
    (materialMean_expression_moment_variance (fixedData d x) hsmall k ht)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hh 2
  unfold PositiveVarianceFlowData.positionJetLp at hsq
  rw [Analysis.DominatedLp.norm_sq_toLp ((fixedData d x).positionJet_memLp (k+2) t)] at hsq
  rw [integral_jet_sq_eq_referencePositionJet d (k+2) x (source_subset d.hb d.hb1 ht)]
  convert hsq using 1
  dsimp [materialOrderFactor, fixedData]
  ring

end AcceleratedLogConcave.Numerics.ConditionalSmoothing

namespace AcceleratedLogConcave.Numerics.MeanResidualBridge
open MeanFlowLp AffineGraph ConditionalSmoothing Analysis.PositiveVarianceSlab
variable {D m : ℕ}

/-- State-jet estimate on the literal seed, with the local radius squared. -/
theorem conditionalJetLp_norm_le_material (d : MeanFlowLp.Data (Fin D) m)
    (j : Fin m) (ρ : d.G.Kernel) (k : ℕ) {t : ℝ} (ht : t ∈ Icc 0 conditionalEnd) :
    ‖conditionalJetLp d j ρ (k+2) t‖ ≤
      (d.ell*(d.r*Real.sqrt (d.G.variance ρ))^2)*materialOrderFactor D k/
        (1-t^2)^(k+1) := by
  have hv : 0 < 1-t^2 := Conditional.conditionalVariance_pos
    (by linarith [ht.1]) (ht.2.trans_lt conditionalEnd_lt_one)
  have hnonneg : 0 ≤ (d.ell*(d.r*Real.sqrt (d.G.variance ρ))^2)*materialOrderFactor D k/
      (1-t^2)^(k+1) := by
    exact div_nonneg (mul_nonneg (mul_nonneg d.hell (sq_nonneg _))
      (materialOrderFactor_nonneg D k)) (pow_nonneg hv.le _)
  have hsq : ‖conditionalJetLp d j ρ (k+2) t‖^2 ≤
      ((d.ell*(d.r*Real.sqrt (d.G.variance ρ))^2)*materialOrderFactor D k/
        (1-t^2)^(k+1))^2 := by
    rw [norm_sq_conditionalJetLp, integral_conditionalJet_sq_eq_phase_gaussian]
    have hh := integral_mono (integrable_phase_gaussian_jet_sq d j ρ (k+2) t)
      (integrable_const (((d.ell*(d.r*Real.sqrt (d.G.variance ρ))^2)*
        materialOrderFactor D k/(1-t^2)^(k+1))^2))
      (fun p => integral_gaussian_jet_sq_le_material (conditionalData d ρ)
        (conditionalData_small d ρ) k (conditionalPhaseCenter d j ρ p) ht)
    simpa using hh
  nlinarith [norm_nonneg (conditionalJetLp d j ρ (k+2) t)]

/-- Exact positive-order conditional budget. Only one positive local-radius
factor remains after the mean/state-jet identity is applied. -/
def materialConditionalDerivativeBudget (d : MeanFlowLp.Data (Fin D) m)
    (ρ : d.G.Kernel) (k : ℕ) : ℝ :=
  (d.ell*(d.r*Real.sqrt (d.G.variance ρ)))*materialOrderFactor D k

theorem materialConditionalDerivativeBudget_nonneg (d : MeanFlowLp.Data (Fin D) m)
    (ρ : d.G.Kernel) (k : ℕ) : 0 ≤ materialConditionalDerivativeBudget d ρ k :=
  mul_nonneg (mul_nonneg d.hell (conditionalData d ρ).hr.le) (materialOrderFactor_nonneg D k)

theorem conditionalMean_derivative_le_material (d : MeanFlowLp.Data (Fin D) m)
    (U : H d → ℝ → H d) (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U)
    (j : Fin m) (ρ : d.G.Kernel) (k : ℕ) {t : ℝ} (ht : t ∈ Icc 0 conditionalEnd) :
    ‖iteratedDeriv (k+1) ((curvesWithConditional d).conditionalMean d.G U 0 d.r j ρ) t‖ ≤
      materialConditionalDerivativeBudget d ρ k/(1-t^2)^(k+1) := by
  rw [iteratedDeriv_replacement_conditionalMean_source d j ρ U hu (k+1) ht,
    norm_smul, Real.norm_eq_abs, abs_inv, abs_neg, abs_of_pos (conditionalData d ρ).hr]
  have hh := mul_le_mul_of_nonneg_left (conditionalJetLp_norm_le_material d j ρ k ht)
    (inv_nonneg.mpr (conditionalData d ρ).hr.le)
  convert hh using 1
  dsimp [materialConditionalDerivativeBudget, conditionalData]
  field_simp [(conditionalData d ρ).hr.ne']

/-- Exact finite-sum receiver budget; no mesh or schedule hypothesis occurs. -/
def materialConditionalCellBudget (d : MeanFlowLp.Data (Fin D) m) (ρ : d.G.Kernel)
    (c : (d.G.conditional ρ).Cell) : ℝ :=
  materialConditionalDerivativeBudget d ρ (m-1)/(1-((d.G.conditional ρ).right c)^2)^m

theorem conditionalMean_cellRegularity_material (d : MeanFlowLp.Data (Fin D) m)
    (U : H d → ℝ → H d) (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U)
    (j : Fin m) (ρ : d.G.Kernel) :
    AffineResidual.CellRegularity (d.G.conditional ρ) m
      ((curvesWithConditional d).conditionalMean d.G U 0 d.r j ρ)
      (materialConditionalCellBudget d ρ) := by
  have hm : 1 ≤ m := by have hj := j.isLt; omega
  have hright (c : (d.G.conditional ρ).Cell) :
      0 < 1-((d.G.conditional ρ).right c)^2 := by
    apply Conditional.conditionalVariance_pos
    · have h0 := (d.G.conditional ρ).lo_le_left c
      have hl := (d.G.conditional ρ).length_pos c
      dsimp [IntervalMesh.length] at hl
      linarith
    · have hh := (d.G.conditional ρ).right_le_hi c
      linarith [conditionalEnd_lt_one]
  refine ⟨?_, ?_, ?_⟩
  · intro c
    exact div_nonneg (materialConditionalDerivativeBudget_nonneg d ρ (m-1))
      (pow_nonneg (hright c).le _)
  · intro c t ht
    exact contDiffAt_replacement_conditionalMean d U hu j ρ m
      ⟨((d.G.conditional ρ).lo_le_left c).trans ht.1,
        ht.2.trans ((d.G.conditional ρ).right_le_hi c)⟩
  · intro c t ht
    have hsource : t ∈ Icc 0 conditionalEnd :=
      ⟨((d.G.conditional ρ).lo_le_left c).trans ht.1,
        ht.2.trans ((d.G.conditional ρ).right_le_hi c)⟩
    have hb := conditionalMean_derivative_le_material d U hu j ρ (m-1) hsource
    rw [Nat.sub_add_cancel hm] at hb
    refine hb.trans ?_
    unfold materialConditionalCellBudget
    apply div_le_div_of_nonneg_left (materialConditionalDerivativeBudget_nonneg d ρ (m-1))
      (pow_pos (hright c) m)
    apply pow_le_pow_left₀ (hright c).le
    nlinarith [hsource.1, ht.2]

end AcceleratedLogConcave.Numerics.MeanResidualBridge
