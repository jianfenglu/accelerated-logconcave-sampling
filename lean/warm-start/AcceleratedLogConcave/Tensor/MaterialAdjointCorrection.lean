import AcceleratedLogConcave.Tensor.MaterialExpressionAdjoint

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff RealInnerProductSpace BigOperators
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open Conditional Analysis Analysis.CoupledVelocityPolynomial CoordinateReduction Kinetic

def materialAdjointCorrection {r : ℕ} (e : Expr signature (r+2)) (i : Fin (r+2)) :
    Expr signature (r+1) :=
  .adjoint (Fin.last (r+1)) (.contract e (.coefficient (Sum.inl 0)) i (1 : Fin 2))

theorem materialAdjointCorrection_size {r : ℕ} (e : Expr signature (r+2)) (i : Fin (r+2)) :
    (materialAdjointCorrection e i).size = (Expr.adjoint i e).size + 3 := by
  simp [materialAdjointCorrection,Expr.size,signature]

theorem materialAdjointCorrection_weight {r : ℕ} (e : Expr signature (r+2)) (i : Fin (r+2)) :
    (materialAdjointCorrection e i).weight = (Expr.adjoint i e).weight := by
  simp [materialAdjointCorrection,Expr.weight,signature]

private theorem correction_left_assignment {D r : ℕ} (a : Fin (r+1) → Fin D)
    (i : Fin (r+2)) (k j : Fin D) :
    leftAssignment (s := 0) i (Fin.snoc a k) j = Fin.insertNth i j a := by
  unfold leftAssignment
  congr 1
  funext z
  change (show Fin (r+2) → Fin D from Fin.snoc a k) z.castSucc = a z
  exact Fin.snoc_castSucc _ _ _

private theorem correction_right_assignment {D r : ℕ} (a : Fin (r+1) → Fin D) (k j : Fin D) :
    rightAssignment (r := r) (1 : Fin 2) (Fin.snoc a k) j = Fin.cons k (fun _ : Fin 1 => j) := by
  funext z
  fin_cases z
  · change (show Fin (r+2) → Fin D from Fin.snoc a k) (Fin.last (r+1)) = k
    exact Fin.snoc_last _ _
  · simp [rightAssignment]

/-- The exact U1 action on the actual row, with its original physical scale.
This identity retains ell=0 without division by curvature. -/
theorem firstJet_materialExpressionRow {D r : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (e : Expr signature (r+2)) (i : Fin (r+2)) (a : Fin (r+1) → Fin D)
    {t : ℝ} (ht : -1<t ∧ t<1) (y : EuclideanSpace ℝ (Fin D)) :
    firstScaledJet d.F d.x d.r t y (materialExpressionRow d e i a (t,y)) =
      (d.ell*d.r) • materialExpressionRow d
        (.contract e (.coefficient (Sum.inl 0)) i (1 : Fin 2)) (Fin.last (r+1)) a (t,y) := by
  ext k
  have hi (v : EuclideanSpace ℝ (Fin D)) :
      inner ℝ (coordinateDirection D k) v = v k := by
    simpa [coordinateDirection,EuclideanSpace.single] using
      EuclideanSpace.inner_single_left k (1:ℝ) v
  rw [← hi,← hi,inner_smul_right,materialExpressionRow_coordinate]
  simp only [materialExpressionRow,map_sum,map_smul,inner_sum,inner_smul_right]
  have hj (j : Fin D) := firstJet_coordinate_eq_scaled_coefficient d ht y
    (Fin.cons k (fun _ : Fin 1 => j))
  change ∀ j : Fin D, inner ℝ (coordinateDirection D k)
    (firstScaledJet d.F d.x d.r t y (coordinateDirection D j)) =
    (d.ell*d.r) * coefficientEnvironment d.F d.x d.ell d.r t (Sum.inl 0) y
      (Fin.cons k (fun _ : Fin 1 => j)) at hj
  simp_rw [hj]
  rw [Fin.insertNth_last']
  change (∑ j : Fin D, _ * ((d.ell*d.r) * _)) =
    (d.ell*d.r) * (∑ j : Fin D,
      materialExpressionValue d e (leftAssignment (s := 0) i (Fin.snoc a k) j) (t,y) *
      coefficientEnvironment d.F d.x d.ell d.r t (Sum.inl 0) y
        (rightAssignment (r := r) (1 : Fin 2) (Fin.snoc a k) j))
  simp_rw [correction_left_assignment,correction_right_assignment]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Exact material-adjoint rule with its correction encoded as a literal
canonical Expr, including rho=0 and ell=0. -/
theorem material_expression_adjoint_correction {D r : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (e : Expr signature (r+2)) (he : IsMaterialExpression e)
    (i : Fin (r+2)) (a : Fin (r+1) → Fin D)
    {t : ℝ} (ht : -1<t ∧ t<1) (y : EuclideanSpace ℝ (Fin D)) :
    materialDerivative d.materialVelocity (materialExpressionValue d (.adjoint i e) a) (t,y) =
      d.spacetimeAdjoint
        (materialDerivative d.materialVelocity (materialExpressionRow d e i a)) (t,y) +
      (d.ell*d.r^2*t) * materialExpressionValue d (materialAdjointCorrection e i) a (t,y) := by
  rw [material_expression_adjoint_row_commutator d e he i a ht y]
  let c : Expr signature (r+2) := .contract e (.coefficient (Sum.inl 0)) i (1 : Fin 2)
  have hc : IsMaterialExpression c := ⟨he,trivial⟩
  have hd := ((contDiffOn_materialExpressionRow d c hc (Fin.last (r+1)) a).contDiffAt
    ((isOpen_openDomain _).mem_nhds (show (t,y) ∈ openDomain _ from ht))).differentiableAt (by simp)
  have hs := hd.comp y
    (((hasFDerivAt_const (𝕜 := ℝ) t y).prodMk (hasFDerivAt_id (𝕜 := ℝ) y)).differentiableAt)
  change DifferentiableAt ℝ (fun z => materialExpressionRow d c (Fin.last (r+1)) a (t,z)) y at hs
  have hfield : (fun z => firstScaledJet d.F d.x d.r t z (materialExpressionRow d e i a (t,z))) =
      fun z => (d.ell*d.r) • materialExpressionRow d c (Fin.last (r+1)) a (t,z) := by
    funext z
    exact firstJet_materialExpressionRow d e i a ht z
  rw [hfield,Conditional.weightedAdjoint_smul (differentiableAt_const _) hs]
  simp only [fderiv_fun_const,Pi.zero_apply,zero_apply,sub_zero]
  rw [← d.spacetimeAdjoint_eq_weightedAdjoint hd,
    ← materialExpressionValue_adjoint d c hc (Fin.last (r+1)) a ht y]
  dsimp [c,materialAdjointCorrection]
  ring

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
