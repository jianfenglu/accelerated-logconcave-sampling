import AcceleratedLogConcave.Kinetic.ReferenceFlow.Drift
import AcceleratedLogConcave.Kinetic.ReferenceFlow.Divergence
import AcceleratedLogConcave.Kinetic.ReferenceFlow.Score

/-! The Hamiltonian part cancels in the actual product-density continuity
equation. All differentiation is classical C1/C2, with the Gibbs score derived
from the actual spatial density law. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Function
open scoped RealInnerProductSpace Topology
namespace AcceleratedLogConcave.Kinetic
open Analysis.Poisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Actual product density on the Hilbert position--momentum product. -/
def coupledDensity (r δ : E → ℝ) (z : CoupledPhase E) : ℝ := r z.fst * δ z.snd

/-- The Hamiltonian drift has zero ordinary divergence; the only divergence
comes from the spatial reverse-heat velocity. -/
theorem coupledDrift_divergence (U : ℝ → E → ℝ) (ell : ℝ) (c : ℝ → ℝ)
    (t : ℝ) (z : CoupledPhase E) (hU : ContDiff ℝ 2 (U t)) :
    fluxDivergence (coupledDrift U ell c t) z =
      fluxDivergence (referenceDrift U c t) z.fst := by
  let b := stdOrthonormalBasis ℝ E
  rw [fluxDivergence_eq_sum_basis (b.prod b) (coupledDrift_hasFDerivAt U ell c t z hU).differentiableAt,
    (coupledDrift_hasFDerivAt U ell c t z hU).fderiv,
    fluxDivergence_eq_sum_basis b (referenceDrift_hasFDerivAt U c t z.fst hU).differentiableAt,
    (referenceDrift_hasFDerivAt U c t z.fst hU).fderiv,
    Fintype.sum_sum_type]
  simp [coupledDriftDerivative_apply, OrthonormalBasis.prod_apply, WithLp.prod_inner_apply]

/-- Derivative of the product density evaluated in the actual coupled drift. -/
theorem coupledDensity_deriv_drift (U : ℝ → E → ℝ) (ell : ℝ) (c : ℝ → ℝ)
    (t : ℝ) (z : CoupledPhase E) (r δ : E → ℝ)
    (hr : HasFDerivAt r ((-r z.fst) • fderiv ℝ (U t) z.fst) z.fst)
    (hδ : HasFDerivAt δ ((-δ z.snd) • innerSL ℝ z.snd) z.snd)
    :
    fderiv ℝ (coupledDensity r δ) z (coupledDrift U ell c t z) =
      δ z.snd * fderiv ℝ r z.fst (referenceDrift U c t z.fst) := by
  let F : CoupledPhase E →L[ℝ] E := (ContinuousLinearMap.fst ℝ E E).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ E E).toContinuousLinearMap
  let S : CoupledPhase E →L[ℝ] E := (ContinuousLinearMap.snd ℝ E E).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ E E).toContinuousLinearMap
  have hd := (hr.comp z F.hasFDerivAt).mul (hδ.comp z S.hasFDerivAt)
  change fderiv ℝ (r ∘ WithLp.fst * δ ∘ WithLp.snd) z _ = _
  rw [hd.fderiv, hr.fderiv]
  have hgrad : fderiv ℝ (U t) z.fst = innerSL ℝ (gradient (U t) z.fst) := by
    exact (toDual_gradient (f := U t) (x := z.fst)).symm
  change r z.fst * (-δ z.snd * inner ℝ z.snd (-ell • gradient (U t) z.fst)) +
    δ z.snd * (-r z.fst * fderiv ℝ (U t) z.fst
      (ell • z.snd - c t • gradient (U t) z.fst)) =
    δ z.snd * (-r z.fst * fderiv ℝ (U t) z.fst (-c t • gradient (U t) z.fst))
  simp only [hgrad, innerSL_apply_apply, inner_sub_right, inner_smul_right]
  rw [real_inner_comm z.snd (gradient (U t) z.fst)]
  ring

variable [MeasurableSpace E] [BorelSpace E]

/-- The spatial density continuity equation implies the true coupled
Gibbs--Gaussian phase equation; no phase transport statement is assumed. -/
theorem coupledDensity_continuity_equation {a b : ℝ} (F : ReferencePoissonFamily E a b)
    (ell : ℝ) (δ : E → ℝ)
    (hδ : ∀ y, HasFDerivAt δ ((-δ y) • innerSL ℝ y) y)
    (t : ℝ) (ht : t ∈ Ioo a b) (z : CoupledPhase E) :
    F.densityVelocity t z.fst * δ z.snd +
      fluxDivergence (fun w => coupledDensity (F.density t) δ w •
        coupledDrift F.potential ell F.scale t w) z = 0 := by
  have hr := reference_density_hasFDerivAt F t ⟨ht.1.le, ht.2.le⟩ z.fst
  have hv := coupledDrift_hasFDerivAt F.potential ell F.scale t z (F.potential_C2 t)
  have hvb := referenceDrift_hasFDerivAt F.potential F.scale t z.fst (F.potential_C2 t)
  have hd : DifferentiableAt ℝ (coupledDensity (F.density t) δ) z :=
    (hr.differentiableAt.comp z
      ((ContinuousLinearMap.fst ℝ E E).comp
        (WithLp.prodContinuousLinearEquiv 2 ℝ E E).toContinuousLinearMap).differentiableAt).mul
    ((hδ z.snd).differentiableAt.comp z
      ((ContinuousLinearMap.snd ℝ E E).comp
        (WithLp.prodContinuousLinearEquiv 2 ℝ E E).toContinuousLinearMap).differentiableAt)
  rw [fluxDivergence_smul hd hv.differentiableAt,
    coupledDrift_divergence _ _ _ _ _ (F.potential_C2 t),
    coupledDensity_deriv_drift _ _ _ _ _ _ _ hr (hδ z.snd)]
  have hp := F.continuity_equation t ht z.fst
  rw [fluxDivergence_smul hr.differentiableAt hvb.differentiableAt] at hp
  dsimp [coupledDensity]
  nlinarith [congrArg (fun q : ℝ => q * δ z.snd) hp]

end AcceleratedLogConcave.Kinetic
