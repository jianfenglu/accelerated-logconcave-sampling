import AcceleratedLogConcave.Tensor.MaterialTrajectory
import AcceleratedLogConcave.Numerics.SmoothBackwardMean

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open Conditional Analysis Analysis.PositiveVarianceSlab Analysis.CoupledVelocityPolynomial Set
variable {D : ℕ} (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))

 theorem positionJet_two_eq_materialMean {t : ℝ}
    (ht : t ∈ Ioo (left d.b) (right d.b)) (y : EuclideanSpace ℝ (Fin D)) :
    d.positionJet 2 t y = -d.r • conditionalMaterialMean d.F d.x d.r t (d.state t y).fst := by
  have ht' := construction_subset d.hb0 d.hb1 ⟨ht.1.le,ht.2.le⟩
  have hM := ((contDiffOn_conditionalMean d.hF d.hlo d.hhi d.x d.r).contDiffAt
    ((isOpen_openDomain _).mem_nhds
      (show (t,(d.state t y).fst) ∈ openDomain (EuclideanSpace ℝ (Fin D)) from ht'))).differentiableAt (by simp)
  have hh := hM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_materialPosition d ht y)
  change HasDerivAt (fun u => conditionalMean d.F d.x d.r u (d.state u y).fst)
    (conditionalMaterialMean d.F d.x d.r t (d.state t y).fst) t at hh
  have he : (fun u => d.positionJet 1 u y) =ᶠ[nhds t]
      (fun u => -d.r • conditionalMean d.F d.x d.r u (d.state u y).fst) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    rw [d.positionJet_one_eq_mean hu,d.positionJet_zero_eq_state ⟨hu.1.le,hu.2.le⟩]
  exact (d.hasDerivAt_positionJet 1 ht y).unique ((hh.const_smul (-d.r)).congr_of_eventuallyEq he)

/-- Actual higher position jets, including the physical minus sign and scale. -/
theorem positionJet_coordinate_expansion (k : ℕ) (a : Fin 1 → Fin D) {t : ℝ}
    (ht : t ∈ Ioo (left d.b) (right d.b)) (y : EuclideanSpace ℝ (Fin D)) :
    inner ℝ (coordinateDirection D (a 0)) (d.positionJet (k+2) t y) =
      -(d.ell*d.r^2) * materialTermsValue d
        (materialIterate (d.ell*d.r^2) materialMeanExpr k) a (t,(d.state t y).fst) := by
  let f (q : ℕ) (u : ℝ) := inner ℝ (coordinateDirection D (a 0)) (d.positionJet (q+2) u y)
  let g (q : ℕ) (u : ℝ) := -(d.ell*d.r^2) * materialTermsValue d
    (materialIterate (d.ell*d.r^2) materialMeanExpr q) a (u,(d.state u y).fst)
  have hf (q : ℕ) {u : ℝ} (hu : u ∈ Ioo (left d.b) (right d.b)) :
      HasDerivAt (f q) (f (q+1) u) u := by
    have hh := (innerSL ℝ (coordinateDirection D (a 0))).hasFDerivAt.comp_hasDerivAt u
      (d.hasDerivAt_positionJet (q+2) hu y)
    simpa [f,Nat.add_assoc,Function.comp_def] using hh
  have hm : IsMaterialExpression materialMeanExpr := by simp [materialMeanExpr,IsMaterialExpression]
  have hg (q : ℕ) {u : ℝ} (hu : u ∈ Ioo (left d.b) (right d.b)) :
      HasDerivAt (g q) (g (q+1) u) u :=
    (hasDerivAt_materialIterate_along d materialMeanExpr hm q a hu y).const_mul _
  have hfg : f 0 =ᶠ[nhds t] g 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    dsimp [f,g]
    rw [positionJet_two_eq_materialMean d hu,inner_smul_right,
      conditionalMaterialMean_eq_expression d
        (construction_subset d.hb0 d.hb1 ⟨hu.1.le,hu.2.le⟩),materialIterate_zero_value]
    change -d.r * ((d.ell*d.r) * _) = -(d.ell*d.r^2) * _
    simp only [materialExpressionValue]
    ring
  have hfi := iteratedDeriv_eq_of_finite_ladder k f isOpen_Ioo (fun q _ _ hu => hf q hu) ht
  have hgi := iteratedDeriv_eq_of_finite_ladder k g isOpen_Ioo (fun q _ _ hu => hg q hu) ht
  exact hfi.symm.trans ((hfg.iteratedDeriv k).eq_of_nhds.trans hgi)

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
