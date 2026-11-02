import AcceleratedLogConcave.Analysis.Poisson.ReferenceFamily
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Operator.Prod

/-! The actual coupled position--momentum drift and its complete C1 flow.
The Hilbert product is used internally; its coordinate projections are the
ordinary position and momentum variables. -/
noncomputable section
open Set Function InnerProductSpace
open scoped Topology NNReal
namespace AcceleratedLogConcave.Kinetic
open Analysis.Poisson OAI.LogConcaveSampling.GlobalODE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

abbrev CoupledPhase (E : Type*) := WithLp 2 (E × E)

/-- The manuscript's actual coupled drift, with `c t = a*t` in the reverse-heat phase. -/
def coupledDrift (U : ℝ → E → ℝ) (ell : ℝ) (c : ℝ → ℝ)
    (t : ℝ) (z : CoupledPhase E) : CoupledPhase E :=
  WithLp.toLp 2 (ell • z.snd - c t • gradient (U t) z.fst,
    -ell • gradient (U t) z.fst)

private def fstCLM : CoupledPhase E →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ E E).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ E E).toContinuousLinearMap
private def sndCLM : CoupledPhase E →L[ℝ] E :=
  (ContinuousLinearMap.snd ℝ E E).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ E E).toContinuousLinearMap
private def pairCLM : (E × E) →L[ℝ] CoupledPhase E :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.toContinuousLinearMap

/-- The actual block spatial derivative of the coupled drift. -/
def coupledDriftDerivative (U : ℝ → E → ℝ) (ell : ℝ) (c : ℝ → ℝ)
    (t : ℝ) (z : CoupledPhase E) : CoupledPhase E →L[ℝ] CoupledPhase E :=
  pairCLM.comp ((ell • sndCLM - c t • (hessianOperator (U t) z.fst).comp fstCLM).prod
    (-ell • (hessianOperator (U t) z.fst).comp fstCLM))

@[simp] theorem coupledDriftDerivative_apply (U : ℝ → E → ℝ) (ell : ℝ) (c : ℝ → ℝ)
    (t : ℝ) (z w : CoupledPhase E) :
    coupledDriftDerivative U ell c t z w = WithLp.toLp 2
      (ell • w.snd - c t • hessianOperator (U t) z.fst w.fst,
        -ell • hessianOperator (U t) z.fst w.fst) := rfl

theorem coupledDrift_hasFDerivAt (U : ℝ → E → ℝ) (ell : ℝ) (c : ℝ → ℝ)
    (t : ℝ) (z : CoupledPhase E) (hU : ContDiff ℝ 2 (U t)) :
    HasFDerivAt (coupledDrift U ell c t) (coupledDriftDerivative U ell c t z) z := by
  have hg := (gradient_hasFDerivAt_hessian hU z.fst).comp z (fstCLM (E := E)).hasFDerivAt
  exact pairCLM.hasFDerivAt.comp z
    (((sndCLM.hasFDerivAt.const_smul ell).sub (hg.const_smul (c t))).prodMk
      (hg.const_smul (-ell)))

theorem coupledDrift_continuous (U : ℝ → E → ℝ) (ell : ℝ) (c : ℝ → ℝ)
    (hG : Continuous (uncurry (fun t => gradient (U t)))) (hc : Continuous c) :
    Continuous (uncurry (coupledDrift U ell c)) := by
  have hg : Continuous (fun p : ℝ × CoupledPhase E => gradient (U p.1) p.2.fst) :=
    hG.comp (continuous_fst.prodMk ((fstCLM (E := E)).continuous.comp continuous_snd))
  exact pairCLM.continuous.comp
    (((sndCLM.continuous.comp continuous_snd).const_smul ell |>.sub
      ((hc.comp continuous_fst).smul hg)).prodMk (hg.const_smul (-ell)))

theorem coupledDriftDerivative_continuous (U : ℝ → E → ℝ) (ell : ℝ) (c : ℝ → ℝ)
    (hH : Continuous (uncurry (fun t => hessianOperator (U t)))) (hc : Continuous c) :
    Continuous (uncurry (coupledDriftDerivative U ell c)) := by
  have hh : Continuous (fun p : ℝ × CoupledPhase E => hessianOperator (U p.1) p.2.fst) :=
    hH.comp (continuous_fst.prodMk ((fstCLM (E := E)).continuous.comp continuous_snd))
  exact continuous_const.clm_comp
    ((ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp
      ((continuous_const.sub ((hc.comp continuous_fst).smul (hh.clm_comp continuous_const))).prodMk
        ((hh.clm_comp continuous_const).const_smul (-ell))))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem coupled_norm_le (x y : E) : ‖WithLp.toLp 2 (x,y)‖ ≤ ‖x‖ + ‖y‖ := by
  have he : WithLp.toLp 2 (x,y) = WithLp.toLp 2 (x,(0:E)) + WithLp.toLp 2 ((0:E),y) := by
    apply WithLp.ofLp_injective
    simp
  rw [he]
  simpa only [WithLp.norm_toLp_fst, WithLp.norm_toLp_snd] using
    norm_add_le (WithLp.toLp 2 (x,(0:E))) (WithLp.toLp 2 ((0:E),y))

theorem coupledDrift_lipschitz (U : ℝ → E → ℝ) (ell : ℝ) (c : ℝ → ℝ)
    (t : ℝ) (hU : ContDiff ℝ 2 (U t))
    (hlo : ∀ x v, 0 ≤ fderiv ℝ (fderiv ℝ (U t)) x v v)
    (hup : ∀ x v, fderiv ℝ (fderiv ℝ (U t)) x v v ≤ ‖v‖ ^ 2)
    (C : ℝ≥0) (hC : |c t| ≤ C) :
    LipschitzWith (2 * ‖ell‖₊ + C) (coupledDrift U ell c t) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have hg := (gradient_lipschitz_of_unit_hessian hU hlo hup).dist_le_mul z.fst w.fst
  simp only [NNReal.coe_one, one_mul, dist_eq_norm] at hg
  have hx : ‖z.fst - w.fst‖ ≤ ‖z-w‖ := WithLp.norm_fst_le E (z-w)
  have hy : ‖z.snd - w.snd‖ ≤ ‖z-w‖ := WithLp.norm_snd_le E (z-w)
  have he : coupledDrift U ell c t z - coupledDrift U ell c t w =
      WithLp.toLp 2 (ell • (z.snd-w.snd) - c t • (gradient (U t) z.fst-gradient (U t) w.fst),
        -ell • (gradient (U t) z.fst-gradient (U t) w.fst)) := by
    apply (WithLp.prodContinuousLinearEquiv 2 ℝ E E).injective
    simp only [coupledDrift, map_sub ]
    ext <;> simp [smul_sub]
    abel
  rw [dist_eq_norm, he]
  apply (coupled_norm_le _ _).trans
  apply (add_le_add (norm_sub_le _ _) le_rfl).trans
  simp only [norm_smul, norm_neg, Real.norm_eq_abs, NNReal.coe_add, NNReal.coe_mul,
    NNReal.coe_ofNat, coe_nnnorm, dist_eq_norm]
  have hg' := hg.trans hx
  nlinarith [mul_le_mul_of_nonneg_left hy (abs_nonneg ell),
    mul_le_mul_of_nonneg_left hg' (abs_nonneg ell),
    mul_le_mul hC hg' (norm_nonneg _) C.coe_nonneg]

section Flow
variable (U : ℝ → E → ℝ) (ell : ℝ) (c : ℝ → ℝ) {a b : ℝ}
  (hU : ∀ t ∈ Icc a b, ContDiff ℝ 2 (U t))
  (hG : Continuous (uncurry (fun t => gradient (U t)))) (hc : Continuous c)
  (C : ℝ≥0) (hC : ∀ t ∈ Icc a b, |c t| ≤ C)
  (hlo : ∀ t ∈ Icc a b, ∀ x v, 0 ≤ fderiv ℝ (fderiv ℝ (U t)) x v v)
  (hup : ∀ t ∈ Icc a b, ∀ x v, fderiv ℝ (fderiv ℝ (U t)) x v v ≤ ‖v‖ ^ 2)

/-- Complete trajectory of the coupled ODE on the source interval. -/
def coupledFlow (s : Icc a b) (z : CoupledPhase E) : ℝ → CoupledPhase E :=
  flow (fun t ht => coupledDrift_lipschitz U ell c t (hU t ht) (hlo t ht) (hup t ht) C (hC t ht))
    (coupledDrift_continuous U ell c hG hc) s z

theorem coupledFlow_initial (s : Icc a b) (z : CoupledPhase E) :
    coupledFlow U ell c hU hG hc C hC hlo hup s z s = z := flow_initial _ _ _ _

theorem coupledFlow_deriv (s : Icc a b) (z : CoupledPhase E) (t : ℝ) (ht : t ∈ Icc a b) :
    HasDerivWithinAt (coupledFlow U ell c hU hG hc C hC hlo hup s z)
      (coupledDrift U ell c t (coupledFlow U ell c hU hG hc C hC hlo hup s z t))
      (Icc a b) t := flow_deriv _ _ _ _ t ht

/-- Invertibility of the actual coupled flow, obtained from ODE uniqueness. -/
def coupledFlowHomeomorph (s t : Icc a b) : CoupledPhase E ≃ₜ CoupledPhase E :=
  flowHomeomorph
    (fun t ht => coupledDrift_lipschitz U ell c t (hU t ht) (hlo t ht) (hup t ht) C (hC t ht))
    (coupledDrift_continuous U ell c hG hc) s t

/-- The ordinary pair representation of the same actual coupled flow. -/
def coupledPairFlowHomeomorph (s t : Icc a b) : (E × E) ≃ₜ (E × E) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.toHomeomorph.trans
    ((coupledFlowHomeomorph U ell c hU hG hc C hC hlo hup s t).trans
      (WithLp.prodContinuousLinearEquiv 2 ℝ E E).toHomeomorph)

end Flow

section SmoothFlow
variable (U : ℝ → E → ℝ) (ell : ℝ) (c : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
  (hU : ∀ t, ContDiff ℝ 2 (U t))
  (hG : Continuous (uncurry (fun t => gradient (U t))))
  (hH : Continuous (uncurry (fun t => hessianOperator (U t)))) (hc : Continuous c)
  (C : ℝ≥0) (hC : ∀ t ∈ Icc a b, |c t| ≤ C)
  (hlo : ∀ t ∈ Icc a b, ∀ x v, 0 ≤ fderiv ℝ (fderiv ℝ (U t)) x v v)
  (hup : ∀ t ∈ Icc a b, ∀ x v, fderiv ℝ (fderiv ℝ (U t)) x v v ≤ ‖v‖ ^ 2)

include hab hH in
/-- Spatial C1 regularity is derived from C2 potentials, with no supplied flow. -/
theorem coupledFlowHomeomorph_contDiff (s t : Icc a b) :
    ContDiff ℝ 1 (coupledFlowHomeomorph U ell c (fun t _ => hU t) hG hc C hC hlo hup s t) :=
  flow_contDiff_one (D := coupledDriftDerivative U ell c) hab
    (coupledDrift_continuous U ell c hG hc)
    (fun t ht => coupledDrift_lipschitz U ell c t (hU t) (hlo t ht) (hup t ht) C (hC t ht))
    (coupledDriftDerivative_continuous U ell c hH hc)
    (fun t x => coupledDrift_hasFDerivAt U ell c t x (hU t)) s t

include hab hH in
theorem coupledFlowHomeomorph_symm_contDiff (s t : Icc a b) :
    ContDiff ℝ 1 (coupledFlowHomeomorph U ell c (fun t _ => hU t) hG hc C hC hlo hup s t).symm :=
  coupledFlowHomeomorph_contDiff U ell c hab hU hG hH hc C hC hlo hup t s

include hab hH in
theorem coupledPairFlowHomeomorph_contDiff (s t : Icc a b) :
    ContDiff ℝ 1 (coupledPairFlowHomeomorph U ell c (fun t _ => hU t) hG hc C hC hlo hup s t) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E E).contDiff.comp
    ((coupledFlowHomeomorph_contDiff U ell c hab hU hG hH hc C hC hlo hup s t).comp
      (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.contDiff)

end SmoothFlow

end AcceleratedLogConcave.Kinetic
