import AcceleratedLogConcave.Conditional.Flow.AdjointProduct

/-! Exact material/positive-weighted-adjoint commutator for the actual
conditional probability velocity. No integration or norm estimate is used. -/
noncomputable section
open Set
open scoped ContDiff RealInnerProductSpace
set_option autoImplicit false
namespace AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
open Analysis Analysis.CoupledVelocityPolynomial Analysis.Poisson Kinetic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι

def spacetimeAdjoint (d : PositiveVarianceFlowData E) (V : ℝ × E → E) (p : ℝ × E) : ℝ :=
  -(∑ i : Fin (Module.finrank ℝ E), inner ℝ (stdOrthonormalBasis ℝ E i)
    (directionalDerivative (0, stdOrthonormalBasis ℝ E i) V p)) +
    inner ℝ (d.scoreField p) (V p)

omit [DecidableEq ι] in
theorem spacetimeAdjoint_eq_weightedAdjoint (d : PositiveVarianceFlowData E)
    {V : ℝ × E → E} {t : ℝ} {y : E} (hV : DifferentiableAt ℝ V (t,y)) :
    d.spacetimeAdjoint V (t,y) =
      weightedAdjoint (fun z => d.scoreField (t,z)) (fun z => V (t,z)) y := by
  have hh := hV.hasFDerivAt.comp y ((hasFDerivAt_const t y).prodMk (hasFDerivAt_id y))
  change HasFDerivAt (fun z => V (t,z)) _ y at hh
  unfold spacetimeAdjoint weightedAdjoint
  rw [fluxDivergence_eq_sum_basis (stdOrthonormalBasis ℝ E) hh.differentiableAt]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  rw [hh.fderiv]
  rfl

/-- [D,A]V = r t A(U1 V), with A the actual positive weighted adjoint.
The test-field smoothness is explicit; the law and velocity require only
original PositiveVarianceFlowData. -/
theorem material_spacetimeAdjoint_commutator (d : PositiveVarianceFlowData E)
    {V : ℝ × E → E} (hV : ContDiffOn ℝ ∞ V (openDomain E))
    {t : ℝ} (ht : -1 < t ∧ t < 1) (y : E) :
    materialDerivative d.materialVelocity (d.spacetimeAdjoint V) (t,y) =
      d.spacetimeAdjoint (materialDerivative d.materialVelocity V) (t,y) +
      (d.r*t) * weightedAdjoint (fun z => d.scoreField (t,z))
        (fun z => firstScaledJet d.F d.x d.r t z (V (t,z))) y := by
  let p : ℝ × E := (t,y)
  let b := stdOrthonormalBasis ℝ E
  have hp : p ∈ openDomain E := ht
  have hv := hV.contDiffAt ((isOpen_openDomain E).mem_nhds hp)
  have hs := d.contDiffOn_scoreField.contDiffAt ((isOpen_openDomain E).mem_nhds hp)
  have hfd : DifferentiableAt ℝ (fderiv ℝ V) p :=
    (hv.fderiv_right (m := 1) (by simp)).differentiableAt_one
  have hj (i : Fin (Module.finrank ℝ E)) :
      DifferentiableAt ℝ (directionalDerivative (0,b i) V) p :=
    (hfd.hasFDerivAt.clm_apply (hasFDerivAt_const (0,b i) p)).differentiableAt
  have hi (i : Fin (Module.finrank ℝ E)) :=
    (hasFDerivAt_const (b i) p).inner ℝ (hj i).hasFDerivAt
  have hh := (HasFDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) => hi i)).neg.add
    ((hs.differentiableAt (by simp)).hasFDerivAt.inner ℝ
      (hv.differentiableAt (by simp)).hasFDerivAt)
  change HasFDerivAt (d.spacetimeAdjoint V) _ p at hh
  have hdiff : materialDerivative d.materialVelocity (d.spacetimeAdjoint V) p =
      -(∑ i, inner ℝ (b i) (materialDerivative d.materialVelocity
        (directionalDerivative (0,b i) V) p)) +
      (inner ℝ (materialDerivative d.materialVelocity d.scoreField p) (V p) +
       inner ℝ (d.scoreField p) (materialDerivative d.materialVelocity V p)) := by
    unfold materialDerivative
    rw [hh.fderiv]
    simp [add_apply, neg_apply, _root_.sum_apply, ContinuousLinearMap.comp_apply,
      zero_apply, add_comm]
  rw [hdiff]
  simp only [p] at *
  simp_rw [d.material_spatial_commutator hV ht y]
  rw [d.material_scoreField ht y]
  have hslice : Differentiable ℝ (fun z => V (t,z)) := by
    intro z
    have hvz := (hV.contDiffAt ((isOpen_openDomain E).mem_nhds
      (show (t,z) ∈ openDomain E from ht))).differentiableAt (by simp)
    exact hvz.comp z (((hasFDerivAt_const t z).prodMk (hasFDerivAt_id z)).differentiableAt)
  have hprod := d.weightedAdjoint_firstJet_apply ht hslice y
  have hslice_deriv (u : E) : fderiv ℝ (fun z => V (t,z)) y u =
      directionalDerivative (0,u) V p := by
    have hh := (hv.differentiableAt (by simp)).hasFDerivAt.comp y
      ((hasFDerivAt_const t y).prodMk (hasFDerivAt_id y))
    change HasFDerivAt (fun z => V (t,z)) _ y at hh
    rw [hh.fderiv]
    rfl
  change weightedAdjoint (fun z => d.scoreField (t,z)) _ y = _ at hprod
  rw [hprod]
  simp_rw [hslice_deriv]
  simp only [spacetimeAdjoint, inner_add_right, inner_smul_right, real_inner_smul_left,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [real_inner_comm (conditionalMaterialMean d.F d.x d.r t y) (V p)]
  ring

end AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
