import AcceleratedLogConcave.Tensor.MaterialMass

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open Conditional Analysis Analysis.PositiveVarianceSlab Analysis.CoupledVelocityPolynomial Set

variable {D : ℕ} (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))

theorem hasDerivAt_materialPosition {t : ℝ}
    (ht : t ∈ Ioo (left d.b) (right d.b)) (y : EuclideanSpace ℝ (Fin D)) :
    HasDerivAt (fun u => (u,(d.state u y).fst))
      (d.materialVelocity (t,(d.state t y).fst)) t := by
  exact (hasDerivAt_id t).prodMk (d.hasDerivAt_state ht y).fst

theorem hasDerivAt_materialIterate_along {r : ℕ} (e : Expr signature r)
    (he : IsMaterialExpression e) (k : ℕ) (a : Fin r → Fin D) {t : ℝ}
    (ht : t ∈ Ioo (left d.b) (right d.b)) (y : EuclideanSpace ℝ (Fin D)) :
    HasDerivAt (fun u => materialTermsValue d (materialIterate (d.ell*d.r^2) e k)
      a (u,(d.state u y).fst))
      (materialTermsValue d (materialIterate (d.ell*d.r^2) e (k+1))
        a (t,(d.state t y).fst)) t := by
  have ht' := construction_subset d.hb0 d.hb1 ⟨ht.1.le,ht.2.le⟩
  have hf := (contDiffOn_materialTermsValue d (materialIterate (d.ell*d.r^2) e k) (materialIterate_isMaterial (d.ell*d.r^2) e he k) a).contDiffAt
    (isOpen_openDomain _ |>.mem_nhds (show (t,(d.state t y).fst) ∈ openDomain (EuclideanSpace ℝ (Fin D)) from ht'))
  have hh := (hf.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_materialPosition d ht y)
  change HasDerivAt _ (materialDerivative d.materialVelocity
    (materialTermsValue d (materialIterate (d.ell*d.r^2) e k) a)
      (t,(d.state t y).fst)) t at hh
  rw [materialIterate_derivative d e he k a ht'] at hh
  exact hh

theorem iteratedDeriv_materialExpression_along {r : ℕ} (e : Expr signature r)
    (he : IsMaterialExpression e) (k : ℕ) (a : Fin r → Fin D) {t : ℝ}
    (ht : t ∈ Ioo (left d.b) (right d.b)) (y : EuclideanSpace ℝ (Fin D)) :
    iteratedDeriv k (fun u => materialExpressionValue d e a (u,(d.state u y).fst)) t =
      materialTermsValue d (materialIterate (d.ell*d.r^2) e k) a (t,(d.state t y).fst) := by
  have hh := iteratedDeriv_eq_of_finite_ladder k
    (fun q u => materialTermsValue d (materialIterate (d.ell*d.r^2) e q) a (u,(d.state u y).fst))
    isOpen_Ioo (fun q _ _u hu => hasDerivAt_materialIterate_along d e he q a hu y) ht
  simpa only [materialIterate_zero_value] using hh

theorem materialFirstJet_coordinate_expansion (k : ℕ) (a : Fin 2 → Fin D) {t : ℝ}
    (ht : t ∈ Ioo (left d.b) (right d.b)) (y : EuclideanSpace ℝ (Fin D)) :
    inner ℝ (coordinateDirection D (a 0))
      (d.materialFirstJet k t y (coordinateDirection D (a 1))) =
      (d.ell*d.r) * materialTermsValue d
        (materialIterate (d.ell*d.r^2) (.coefficient (Sum.inl 0)) k) a (t,(d.state t y).fst) := by
  let f (q : ℕ) (u : ℝ) := inner ℝ (coordinateDirection D (a 0))
    (d.materialFirstJet q u y (coordinateDirection D (a 1)))
  let g (q : ℕ) (u : ℝ) := (d.ell*d.r) * materialTermsValue d
    (materialIterate (d.ell*d.r^2) (.coefficient (Sum.inl 0)) q) a (u,(d.state u y).fst)
  have hf (q : ℕ) {u : ℝ} (hu : u ∈ Ioo (left d.b) (right d.b)) :
      HasDerivAt (f q) (f (q+1) u) u := by
    have hh := (d.hasDerivAt_materialFirstJet q hu y).clm_apply
      (hasDerivAt_const u (coordinateDirection D (a 1)))
    have hh' := (innerSL ℝ (coordinateDirection D (a 0))).hasFDerivAt.comp_hasDerivAt u hh
    simpa [f,Function.comp_def] using hh'
  have hg (q : ℕ) {u : ℝ} (hu : u ∈ Ioo (left d.b) (right d.b)) :
      HasDerivAt (g q) (g (q+1) u) u :=
    (hasDerivAt_materialIterate_along d (.coefficient (Sum.inl 0)) (by trivial) q a hu y).const_mul _
  have hfg : f 0 =ᶠ[nhds t] g 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    dsimp [f,g]
    rw [materialIterate_zero_value,d.materialFirstJet_zero]
    exact firstJet_coordinate_eq_scaled_coefficient d
      (construction_subset d.hb0 d.hb1 ⟨hu.1.le,hu.2.le⟩) _ a
  have hfi := iteratedDeriv_eq_of_finite_ladder k f isOpen_Ioo (fun q _ _ hu => hf q hu) ht
  have hgi := iteratedDeriv_eq_of_finite_ladder k g isOpen_Ioo (fun q _ _ hu => hg q hu) ht
  exact hfi.symm.trans ((hfg.iteratedDeriv k).eq_of_nhds.trans hgi)

/-- The existing actual C-jet receiver, with its single physical smallness factor. -/
theorem jacobianCoefficientJet_coordinate_expansion (k : ℕ) (a : Fin 2 → Fin D) {t : ℝ}
    (ht : t ∈ Ioo (left d.b) (right d.b)) (y : EuclideanSpace ℝ (Fin D)) :
    inner ℝ (coordinateDirection D (a 0))
      (d.jacobianCoefficientJet k t y (coordinateDirection D (a 1))) =
      (d.ell*d.r^2) *
        (t * materialTermsValue d
          (materialIterate (d.ell*d.r^2) (.coefficient (Sum.inl 0)) k) a (t,(d.state t y).fst) +
        (k:ℝ) * materialTermsValue d
          (materialIterate (d.ell*d.r^2) (.coefficient (Sum.inl 0)) (k-1)) a (t,(d.state t y).fst)) := by
  rw [d.jacobianCoefficientJet_eq_material k ht y]
  simp only [smul_apply,add_apply,
    inner_smul_right,inner_add_right]
  rw [materialFirstJet_coordinate_expansion d k a ht y,
    materialFirstJet_coordinate_expansion d (k-1) a ht y]
  ring

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
