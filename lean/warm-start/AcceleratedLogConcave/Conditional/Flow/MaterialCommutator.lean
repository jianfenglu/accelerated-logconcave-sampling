import AcceleratedLogConcave.Analysis.MaterialCommutator
import AcceleratedLogConcave.Conditional.Flow.ActualCoefficientJets

/-! The source material/spatial commutator for the actual conditional-mean
velocity, with its exact r t U1 correction and no division by t. -/
noncomputable section
open Set
open scoped ContDiff
set_option autoImplicit false
namespace AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
open Analysis Analysis.PositiveVarianceSlab Analysis.CoupledVelocityPolynomial
variable {E A : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
variable (d : PositiveVarianceFlowData E)

def materialVelocity (p : ℝ × E) : ℝ × E :=
  (1, (-d.r) • conditionalMean d.F d.x d.r p.1 p.2)

theorem contDiffOn_materialVelocity :
    ContDiffOn ℝ ∞ d.materialVelocity (openDomain E) :=
  contDiffOn_const.prodMk ((contDiffOn_conditionalMean d.hF d.hlo d.hhi d.x d.r).const_smul (-d.r))

theorem fderiv_materialVelocity_spatial {t : ℝ} (ht : -1 < t ∧ t < 1) (y u : E) :
    fderiv ℝ d.materialVelocity (t,y) (0,u) =
      (0, (-d.r*t) • firstScaledJet d.F d.x d.r t y u) := by
  let M : ℝ × E → E := fun p => conditionalMean d.F d.x d.r p.1 p.2
  have hM : DifferentiableAt ℝ M (t,y) :=
    ((contDiffOn_conditionalMean d.hF d.hlo d.hhi d.x d.r).contDiffAt
      ((isOpen_openDomain E).mem_nhds (show (t,y) ∈ openDomain E from ht))).differentiableAt (by simp)
  have hpart := hM.hasFDerivAt.comp y ((hasFDerivAt_const t y).prodMk (hasFDerivAt_id y))
  have he : fderiv ℝ M (t,y) (0,u) =
      t • firstScaledJet d.F d.x d.r t y u := by
    have hh := congrArg (fun L : E →L[ℝ] E => L u) hpart.fderiv
    change fderiv ℝ (conditionalMean d.F d.x d.r t) y u = fderiv ℝ M (t,y) (0,u) at hh
    rw [fderiv_conditionalMean_eq_smul_firstScaledJet d.hF d.hlo d.hhi d.x d.r ht.1 ht.2] at hh
    exact hh.symm
  have hV := (hasFDerivAt_const (1 : ℝ) (t,y)).prodMk (hM.hasFDerivAt.const_smul (-d.r))
  change HasFDerivAt d.materialVelocity _ (t,y) at hV
  rw [hV.fderiv]
  change (0, (-d.r) • (fderiv ℝ M (t,y) (0,u))) = _
  rw [he, smul_smul]

/-- [D,∂u]f = r t ∂_(U1 u) f. The formula includes t=0 without a singular
normalization. Smoothness of the test observable is explicit; the actual
velocity and its derivative are discharged from the original flow data. -/
theorem material_spatial_commutator {f : ℝ × E → A}
    (hf : ContDiffOn ℝ ∞ f (openDomain E)) {t : ℝ}
    (ht : -1 < t ∧ t < 1) (y u : E) :
    materialDerivative d.materialVelocity (directionalDerivative (0,u) f) (t,y) =
      directionalDerivative (0,u) (materialDerivative d.materialVelocity f) (t,y) +
        (d.r*t) • directionalDerivative
          (0, firstScaledJet d.F d.x d.r t y u) f (t,y) := by
  have hfa := hf.contDiffAt ((isOpen_openDomain E).mem_nhds (show (t,y) ∈ openDomain E from ht))
  have hV := (d.contDiffOn_materialVelocity.contDiffAt
    ((isOpen_openDomain E).mem_nhds (show (t,y) ∈ openDomain E from ht))).differentiableAt (by simp)
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) (t,y) := by
    exact (hfa.fderiv_right (m := 1) (by simp)).differentiableAt_one
  rw [material_directional_commutator hfd hV (hfa.isSymmSndFDerivAt (by simp)) (0,u),
    d.fderiv_materialVelocity_spatial ht y u]
  have he : ((0 : ℝ), (-d.r*t) • firstScaledJet d.F d.x d.r t y u) =
      (-(d.r*t)) • ((0 : ℝ), firstScaledJet d.F d.x d.r t y u) := by
    simp only [Prod.smul_mk, smul_zero, neg_mul]
  rw [he, map_smul, neg_smul, sub_neg_eq_add]
  rfl

end AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
