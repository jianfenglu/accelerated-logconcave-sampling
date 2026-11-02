import AcceleratedLogConcave.Conditional.Flow.MaterialScaledJetSuccessor

noncomputable section
open MeasureTheory
open scoped ContDiff RealInnerProductSpace BigOperators
namespace AcceleratedLogConcave.Conditional

private theorem iterated_scalar_swap_heads {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (q : ℕ)
    (a : Fin q → E) (u v x : E) :
    iteratedFDeriv ℝ (q+2) f x (Fin.cons u (Fin.cons v a)) =
      iteratedFDeriv ℝ (q+2) f x (Fin.cons v (Fin.cons u a)) := by
  have hq : ContDiff ℝ (⊤ : ℕ∞) (iteratedFDeriv ℝ q f) := hf.iteratedFDeriv_right (by simp)
  have hq1 : ContDiff ℝ (⊤ : ℕ∞) (iteratedFDeriv ℝ (q+1) f) := hf.iteratedFDeriv_right (by simp)
  let g := fun z => iteratedFDeriv ℝ q f z a
  let L : (E [×q]→L[ℝ] ℝ) →L[ℝ] ℝ := LinearMap.mkContinuous
    { toFun := fun A => A a
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
    (∏ i, ‖a i‖) (fun A => by change ‖A a‖ ≤ (∏ i, ‖a i‖)*‖A‖; simpa only [mul_comm] using A.le_opNorm a)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := L.contDiff.comp hq
  have he (z w : E) : iteratedFDeriv ℝ (q+1) f z (Fin.cons w a) = fderiv ℝ g z w := by
    simpa only [Fin.cons_zero,Fin.tail_cons] using
      ((hq.differentiable (by simp)) z).iteratedFDeriv_succ_apply_left' (m := Fin.cons w a)
  rw [((hq1.differentiable (by simp)) x).iteratedFDeriv_succ_apply_left',
    ((hq1.differentiable (by simp)) x).iteratedFDeriv_succ_apply_left']
  simp only [Fin.cons_zero,Fin.tail_cons]
  simp_rw [he]
  exact congrFun (JetCalculus.dir_dir hg u v) x

namespace PositiveVarianceFlowData
variable {D : ℕ} (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))

/-- Swap the two leading actual center-jet slots at every probability time,
including zero. This is proved from center smoothness, not inverse-time scaling. -/
theorem scaledJetCoordinate_swap_heads (q : ℕ) (w u v : EuclideanSpace ℝ (Fin D))
    (a : Fin q → EuclideanSpace ℝ (Fin D)) {t : ℝ}
    (ht : -1 < t ∧ t < 1) (y : EuclideanSpace ℝ (Fin D)) :
    d.scaledJetCoordinate (q+2) w (Fin.cons u (Fin.cons v a)) (t,y) =
      d.scaledJetCoordinate (q+2) w (Fin.cons v (Fin.cons u a)) (t,y) := by
  let N := fun c : EuclideanSpace ℝ (Fin D) => ∫ z, primitiveObservable d.F d.x d.r z
    ∂Gibbs.heatPosterior (primitivePotential d.F d.x d.r) (conditionalVariance t) c
  have hN : ContDiff ℝ ∞ N :=
    Tilt.contDiff_integral_heatPosterior (contDiff_primitivePotential d.hF d.x d.r)
      (le_refl 0) (conditionalVariance_pos ht.1 ht.2)
      (by simpa using primitivePotential_hessian_nonneg d.hF d.hlo d.x d.r)
      (continuous_primitiveObservable d.hF d.x d.r)
      (‖gradient d.F 0‖ + |d.ell| * ‖d.x‖) (|d.ell| * |d.r|) 1
      (by simpa only [pow_one] using norm_primitiveObservable_le_affine d.hF d.hlo d.hhi d.x d.r)
  let f := fun c => inner ℝ w (N c)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := contDiff_const.inner ℝ hN
  have he (b : Fin (q+2) → EuclideanSpace ℝ (Fin D)) :
      d.scaledJetCoordinate (q+2) w b (t,y) = iteratedFDeriv ℝ (q+2) f (t • y) b := by
    have hh := (innerSL ℝ w).iteratedFDeriv_comp_left (x := t • y) hN.contDiffAt
      (show ((q+2 : ℕ) : ℕ∞ω) ≤ (⊤ : ℕ∞) by simp)
    change iteratedFDeriv ℝ (q+2) f (t • y) = _ at hh
    rw [hh]
    rfl
  rw [he,he]
  exact iterated_scalar_swap_heads hf q a u v (t • y)

end PositiveVarianceFlowData
end AcceleratedLogConcave.Conditional
