import DirectW12.MovingTestProduct
import DirectW12.PoissonVectorCancellation

/-!

-/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace Set Function
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.DirectW12
open Analysis.Poisson Analysis.WeightedGradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {a b : ℝ}

theorem coupledPairInverse_contDiff (P : ReferencePoissonFamily E a b)
    (ell : ℝ) (t : Icc a b) :
    ContDiff ℝ 1 (referenceCoupledPairFlow P ell t).symm := by
  exact ((WithLp.prodContinuousLinearEquiv 2 ℝ E E).contDiff.comp
    (referenceCoupledFlow_symm_contDiff P ell t)).comp
      (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.contDiff

/-- The vector test is genuinely transported by the inverse coupled flow. -/
def coupledMovingVectorTest (P : ReferencePoissonFamily E a b)
    (ell : ℝ) (t : Icc a b) (ψ : E × E → E) : E × E → E :=
  ψ ∘ (referenceCoupledPairFlow P ell t).symm

theorem coupledMovingVectorTest_contDiff (P : ReferencePoissonFamily E a b)
    (ell : ℝ) (t : Icc a b) {ψ : E × E → E} (hψ : ContDiff ℝ 1 ψ) :
    ContDiff ℝ 1 (coupledMovingVectorTest P ell t ψ) :=
  hψ.comp (coupledPairInverse_contDiff P ell t)

theorem coupledMovingVectorTest_compact (P : ReferencePoissonFamily E a b)
    (ell : ℝ) (t : Icc a b) {ψ : E × E → E} (hc : HasCompactSupport ψ) :
    HasCompactSupport (coupledMovingVectorTest P ell t ψ) :=
  hc.comp_homeomorph (referenceCoupledPairFlow P ell t).symm

/-- Exact coupled-flow change of variables. The measurable homeomorphism
version of integral_comp works for arbitrary representatives. -/
theorem coupled_pairing_changeVariables
    (P : ReferencePoissonFamily E a b) (ell : ℝ) (t : Icc a b)
    (f : E × E → E) (ψ : E × E → E) :
    (∫ z, inner ℝ (f (referenceCoupledPairFlow P ell t z)) (ψ z)
      ∂(P.law a).prod (stdGaussian E)) =
    ∫ z, inner ℝ (f z) (coupledMovingVectorTest P ell t ψ z)
      ∂(P.law t).prod (stdGaussian E) := by
  have h := (referenceCoupledPairFlow_measurePreserving P ell t).integral_comp
    (referenceCoupledPairFlow P ell t).toMeasurableEquiv.measurableEmbedding
    (fun z => inner ℝ (f z) (coupledMovingVectorTest P ell t ψ z))
  simpa only [coupledMovingVectorTest, Function.comp_apply,
    Homeomorph.symm_apply_apply] using h

/-- The actual physical inverse supplies actual closed-gradient rows and
cancellation against its actual coupled-moving test, including sharp energy.
This theorem is static in t; it does not assert a time derivative. -/
theorem physicalGradient_moving_test_cancellation
    (P : ReferencePoissonFamily E a b) (ell : ℝ)
    (g : Lp ℝ 2 (P.law a)) (t : Icc a b)
    (ψ : E × E → E) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    let v := physicalGradient P g t
    let Ψ := coupledMovingVectorTest P ell t ψ
    ∃ rows : Fin (Module.finrank ℝ E) → Lp E 2 (P.law t),
      (∀ i, ((innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).compLp v, rows i) ∈
        (closedGradient (P.law t) (P.potential t)
          ((P.potential_C2 t).of_le (by norm_num))
          (P.integrable t t.property) (P.gibbs_law t t.property)).graph) ∧
      ‖gaussianHessianVector (P.law t) rows‖ ^ 2 ≤ ‖g‖ ^ 2 ∧
      Integrable (fun z => inner ℝ (v z.1)
        (fderiv ℝ Ψ z (z.2, -gradient (P.potential t) z.1)))
        ((P.law t).prod (stdGaussian E)) ∧
      Integrable (fun z => inner ℝ (gaussianHessianVector (P.law t) rows z) (Ψ z))
        ((P.law t).prod (stdGaussian E)) ∧
      (∫ z, inner ℝ (v z.1)
        (fderiv ℝ Ψ z (z.2, -gradient (P.potential t) z.1))
        ∂(P.law t).prod (stdGaussian E)) =
        -(∫ z, inner ℝ (gaussianHessianVector (P.law t) rows z) (Ψ z)
          ∂(P.law t).prod (stdGaussian E)) := by
  obtain ⟨rows, hrows, hb, hcancel⟩ :=
    gradientPoissonInverse_vector_hamiltonian_cancellation
      (P.law t) (P.potential t) (P.potential_C2 t)
      (P.integrable t t.property) (P.gibbs_law t t.property)
      (P.lower t) (P.lower_pos t t.property) (P.hessian_lower t t.property)
      (by simpa only [one_mul] using P.hessian_upper t t.property)
      ((P.unitary t).symm g)
  refine ⟨rows, hrows, ?_, hcancel _
    (coupledMovingVectorTest_contDiff P ell t hψ)
    (coupledMovingVectorTest_compact P ell t hc)⟩
  simpa only [(P.unitary t).symm.norm_map] using hb

end AcceleratedLogConcave.Kinetic.DirectW12
