import AcceleratedLogConcave.Numerics.SmoothConditionalOrder
import AcceleratedLogConcave.Numerics.SmoothConditionalReindex

/-! Explicit conditional cell regularity under the original Data, for any
finite physical coordinate type. The budget has amplitude ell*a*sqrt(D),
denominator exponent m, and universal order envelope (12*m)^(12*m).
This supplies only the conditional field, not full Regularity or a schedule. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace AcceleratedLogConcave.Numerics.ConditionalSmoothing
open Analysis.PositiveVarianceSlab
variable {ι : Type*} [Fintype ι]

/-- The Fin-D material theorem transported through an explicit coordinate
isometry, including its Gaussian law and actual time-jet identity. -/
theorem integral_gaussian_jet_sq_le_material_fintype
    (d : SamplingCenterLp.Data ι) (hsmall : d.r^2*d.ell ≤ 1/2)
    (k : ℕ) (x : EuclideanSpace ℝ ι) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    (∫ z, ‖(jet d (k+2) t (x,z)).2‖^2 ∂stdGaussian (EuclideanSpace ℝ ι)) ≤
      ((d.ell*d.r^2)*materialOrderFactor (Fintype.card ι) k/(1-t^2)^(k+1))^2 := by
  let e := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin ι)
  rw [integral_gaussian_jet_sq_reindex d e (k+2) x (source_subset d.hb d.hb1 ht)]
  exact integral_gaussian_jet_sq_le_material (reindexData d e) hsmall k (e x) ht

end AcceleratedLogConcave.Numerics.ConditionalSmoothing

namespace AcceleratedLogConcave.Numerics.MeanResidualBridge
open MeanFlowLp AffineGraph ConditionalSmoothing Analysis.PositiveVarianceSlab
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

/-- General finite-coordinate actual-seed state-jet bound. -/
theorem conditionalJetLp_norm_le_material_fintype (d : MeanFlowLp.Data ι m)
    (j : Fin m) (ρ : d.G.Kernel) (k : ℕ) {t : ℝ} (ht : t ∈ Icc 0 conditionalEnd) :
    ‖conditionalJetLp d j ρ (k+2) t‖ ≤
      (d.ell*(d.r*Real.sqrt (d.G.variance ρ))^2)*materialOrderFactor (Fintype.card ι) k/
        (1-t^2)^(k+1) := by
  have hv : 0 < 1-t^2 := Conditional.conditionalVariance_pos
    (by linarith [ht.1]) (ht.2.trans_lt conditionalEnd_lt_one)
  have hnonneg : 0 ≤ (d.ell*(d.r*Real.sqrt (d.G.variance ρ))^2)*
      materialOrderFactor (Fintype.card ι) k/(1-t^2)^(k+1) :=
    div_nonneg (mul_nonneg (mul_nonneg d.hell (sq_nonneg _))
      (materialOrderFactor_nonneg _ k)) (pow_nonneg hv.le _)
  have hsq : ‖conditionalJetLp d j ρ (k+2) t‖^2 ≤
      ((d.ell*(d.r*Real.sqrt (d.G.variance ρ))^2)*materialOrderFactor (Fintype.card ι) k/
        (1-t^2)^(k+1))^2 := by
    rw [norm_sq_conditionalJetLp, integral_conditionalJet_sq_eq_phase_gaussian]
    have hh := integral_mono (integrable_phase_gaussian_jet_sq d j ρ (k+2) t)
      (integrable_const (((d.ell*(d.r*Real.sqrt (d.G.variance ρ))^2)*
        materialOrderFactor (Fintype.card ι) k/(1-t^2)^(k+1))^2))
      (fun p => integral_gaussian_jet_sq_le_material_fintype (conditionalData d ρ)
        (conditionalData_small d ρ) k (conditionalPhaseCenter d j ρ p) ht)
    simpa using hh
  nlinarith [norm_nonneg (conditionalJetLp d j ρ (k+2) t)]

/-- Explicit original-data amplitude for a positive mean derivative order. -/
def conditionalDerivativeBudget (d : MeanFlowLp.Data ι m) (ρ : d.G.Kernel) (n : ℕ) : ℝ :=
  d.ell*(d.r*Real.sqrt (d.G.variance ρ))*Real.sqrt (Fintype.card ι : ℝ)*
    conditionalOrderEnvelope n

omit [DecidableEq ι] in
theorem conditionalDerivativeBudget_nonneg (d : MeanFlowLp.Data ι m)
    (ρ : d.G.Kernel) (n : ℕ) : 0 ≤ conditionalDerivativeBudget d ρ n :=
  mul_nonneg (mul_nonneg (mul_nonneg d.hell (conditionalData d ρ).hr.le)
    (Real.sqrt_nonneg _)) (conditionalOrderEnvelope_nonneg n)

/-- The actual receiver derivative estimate, without an inverse-variance loss.
The local radius is retained literally; both source endpoints are included. -/
theorem conditionalMean_derivative_le_explicit (d : MeanFlowLp.Data ι m)
    (U : H d → ℝ → H d) (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U)
    (j : Fin m) (ρ : d.G.Kernel) (k : ℕ) {t : ℝ} (ht : t ∈ Icc 0 conditionalEnd) :
    ‖iteratedDeriv (k+1) ((curvesWithConditional d).conditionalMean d.G U 0 d.r j ρ) t‖ ≤
      conditionalDerivativeBudget d ρ (k+1)/(1-t^2)^(k+1) := by
  have hv : 0 < 1-t^2 := Conditional.conditionalVariance_pos
    (by linarith [ht.1]) (ht.2.trans_lt conditionalEnd_lt_one)
  rw [iteratedDeriv_replacement_conditionalMean_source d j ρ U hu (k+1) ht,
    norm_smul, Real.norm_eq_abs, abs_inv, abs_neg, abs_of_pos (conditionalData d ρ).hr]
  have hh := mul_le_mul_of_nonneg_left (conditionalJetLp_norm_le_material_fintype d j ρ k ht)
    (inv_nonneg.mpr (conditionalData d ρ).hr.le)
  have he : (conditionalData d ρ).r⁻¹ *
      ((d.ell*(d.r*Real.sqrt (d.G.variance ρ))^2)*materialOrderFactor (Fintype.card ι) k/
        (1-t^2)^(k+1)) =
      (d.ell*(d.r*Real.sqrt (d.G.variance ρ)))*materialOrderFactor (Fintype.card ι) k/
        (1-t^2)^(k+1) := by
    dsimp [conditionalData]
    field_simp [(conditionalData d ρ).hr.ne']
  rw [he] at hh
  refine hh.trans ?_
  unfold conditionalDerivativeBudget
  apply div_le_div_of_nonneg_right _ (pow_nonneg hv.le _)
  have h := mul_le_mul_of_nonneg_left (materialOrderFactor_le (Fintype.card ι) k)
    (mul_nonneg d.hell (conditionalData d ρ).hr.le)
  simpa only [conditionalData, mul_assoc] using h

/-- Exact cellwise conditional budget, before any mesh/schedule simplification. -/
def conditionalCellBudget (d : MeanFlowLp.Data ι m) (ρ : d.G.Kernel)
    (c : (d.G.conditional ρ).Cell) : ℝ :=
  conditionalDerivativeBudget d ρ m/(1-((d.G.conditional ρ).right c)^2)^m

/-- The requested conditional CellRegularity supplier on original Data.
The j-index ensures m≥1; the m=0 family is empty. -/
theorem conditionalMean_cellRegularity_explicit (d : MeanFlowLp.Data ι m)
    (U : H d → ℝ → H d) (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U)
    (j : Fin m) (ρ : d.G.Kernel) :
    AffineResidual.CellRegularity (d.G.conditional ρ) m
      ((curvesWithConditional d).conditionalMean d.G U 0 d.r j ρ)
      (conditionalCellBudget d ρ) := by
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
    exact div_nonneg (conditionalDerivativeBudget_nonneg d ρ m) (pow_nonneg (hright c).le _)
  · intro c t ht
    exact contDiffAt_replacement_conditionalMean d U hu j ρ m
      ⟨((d.G.conditional ρ).lo_le_left c).trans ht.1,
        ht.2.trans ((d.G.conditional ρ).right_le_hi c)⟩
  · intro c t ht
    have hsource : t ∈ Icc 0 conditionalEnd :=
      ⟨((d.G.conditional ρ).lo_le_left c).trans ht.1,
        ht.2.trans ((d.G.conditional ρ).right_le_hi c)⟩
    have hb := conditionalMean_derivative_le_explicit d U hu j ρ (m-1) hsource
    rw [Nat.sub_add_cancel hm] at hb
    refine hb.trans ?_
    unfold conditionalCellBudget
    apply div_le_div_of_nonneg_left (conditionalDerivativeBudget_nonneg d ρ m)
      (pow_pos (hright c) m)
    apply pow_le_pow_left₀ (hright c).le
    nlinarith [hsource.1, ht.2]

end AcceleratedLogConcave.Numerics.MeanResidualBridge
