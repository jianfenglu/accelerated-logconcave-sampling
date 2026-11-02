import DirectW12.ClosedPairing
import DirectW12.CompactVectorDensity

/-!

-/
noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory ProbabilityTheory InnerProductSpace Set Function Filter
open scoped Topology NNReal RealInnerProductSpace
open OAI.LogConcaveSampling.GlobalODE
namespace AcceleratedLogConcave.Kinetic.DirectW12
open Analysis.Poisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {a b : ℝ}

/-- The physical Poisson gradient lifted to the current phase law and pulled
back by the actual coupled phase flow. No artificial endpoint is introduced. -/
def physicalCoupledVector (P : ReferencePoissonFamily E a b) (ell : ℝ)
    (g : Lp ℝ 2 (P.law a)) (t : Icc a b) :
    Lp E 2 ((P.law a).prod (stdGaussian E)) :=
  coupledPullback P ell t
    (Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst (physicalGradient P g t))

/-- Representative identity in the fixed initial phase measure. The null-set
pullback is justified by measure preservation, not pointwise evaluation of L² classes. -/
theorem physicalCoupledVector_coe (P : ReferencePoissonFamily E a b) (ell : ℝ)
    (g : Lp ℝ 2 (P.law a)) (t : Icc a b) :
    (physicalCoupledVector P ell g t : E × E → E) =ᵐ[(P.law a).prod (stdGaussian E)]
      fun z => physicalGradient P g t (referenceCoupledPairFlow P ell t z).1 := by
  let v : Lp E 2 ((P.law t).prod (stdGaussian E)) :=
    Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst (physicalGradient P g t)
  filter_upwards [Lp.coeFn_compMeasurePreserving v
      (referenceCoupledPairFlow_measurePreserving P ell t),
    (referenceCoupledPairFlow_measurePreserving P ell t).quasiMeasurePreserving.ae
      (Lp.coeFn_compMeasurePreserving (physicalGradient P g t) measurePreserving_fst)]
    with z hflow hfst
  exact hflow.trans hfst

/-- The existing physical scalar pairing is exactly the inner product of the
actual E-valued coupled L² path with the compact vector test. -/
theorem physicalCoupledVector_inner (P : ReferencePoissonFamily E a b) (ell : ℝ)
    (g : Lp ℝ 2 (P.law a)) (t : Icc a b) (ψ : E × E → E)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    inner ℝ (physicalCoupledVector P ell g t) (pairTestLp P ψ hψ hc) =
      physicalCoupledPairing P ell g ψ t := by
  rw [L2.inner_def]
  unfold physicalCoupledPairing
  rw [projIcc_of_mem P.ordered t.property]
  apply integral_congr_ae
  filter_upwards [physicalCoupledVector_coe P ell g t,
    (hψ.memLp_of_hasCompactSupport hc).coeFn_toLp] with z hv htest
  change pairTestLp P ψ hψ hc z = ψ z at htest
  rw [hv, htest]

/-- Genuine compact C¹ vector-test density in the initial phase L² space. -/
theorem physicalPairTest_dense (P : ReferencePoissonFamily E a b) :
    Dense {v : Lp E 2 ((P.law a).prod (stdGaussian E)) |
      ∃ (ψ : E × E → E) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ),
        v = pairTestLp P ψ hψ.continuous hc} := by
  exact compact_contDiff_vector_dense ((P.law a).prod (stdGaussian E))

/-- Exact affine-speed closed-clock increment for the actual coupled physical
path. There is no inverse-curvature loss, density field, endpoint replacement,
strong derivative hypothesis, or jointly measurable velocity selection. -/
theorem physicalCoupledVector_increment_le (P : ReferencePoissonFamily E a b)
    {ell A u R : ℝ} (hell : 0 ≤ ell) (hA : 0 ≤ A) (hu : 0 ≤ u)
    (huR : u ≤ R) (huI : u ∈ Icc a b) (hRI : R ∈ Icc a b)
    (hscale : ∀ r ∈ Ioo u R, P.scale r = A*r)
    (g : Lp ℝ 2 (P.law a)) :
    ‖physicalCoupledVector P ell g ⟨R,hRI⟩ -
      physicalCoupledVector P ell g ⟨u,huI⟩‖ ≤
      (ell*(R-u) + A*(R^2-u^2)/2) * ‖g‖ := by
  have hC : 0 ≤ (ell*(R-u) + A*(R^2-u^2)/2) * ‖g‖ := by
    apply mul_nonneg _ (norm_nonneg g)
    apply add_nonneg (mul_nonneg hell (sub_nonneg.mpr huR))
    apply div_nonneg (mul_nonneg hA _) (by norm_num)
    nlinarith [mul_nonneg (sub_nonneg.mpr huR) (add_nonneg (hu.trans huR) hu)]
  apply norm_le_of_abs_inner_le_dense _ (physicalPairTest_dense P) _ hC
  rintro v ⟨ψ, hψ, hc, rfl⟩
  rw [inner_sub_left, physicalCoupledVector_inner, physicalCoupledVector_inner]
  exact physicalCoupledPairing_increment_le P hell hA hu huR huI hRI hscale g ψ hψ hc

/-- The paper's final-law input normalization: pull g_R to the fixed reference
space by the genuine spatial unitary. Its norm is exactly preserved. -/
theorem physicalCoupledVector_increment_final_source_le (P : ReferencePoissonFamily E a b)
    {ell A u R : ℝ} (hell : 0 ≤ ell) (hA : 0 ≤ A) (hu : 0 ≤ u)
    (huR : u ≤ R) (huI : u ∈ Icc a b) (hRI : R ∈ Icc a b)
    (hscale : ∀ r ∈ Ioo u R, P.scale r = A*r)
    (gR : Lp ℝ 2 (P.law R)) :
    ‖physicalCoupledVector P ell (P.unitary ⟨R,hRI⟩ gR) ⟨R,hRI⟩ -
      physicalCoupledVector P ell (P.unitary ⟨R,hRI⟩ gR) ⟨u,huI⟩‖ ≤
      (ell*(R-u) + A*(R^2-u^2)/2) * ‖gR‖ := by
  simpa only [LinearIsometryEquiv.norm_map] using
    physicalCoupledVector_increment_le P hell hA hu huR huI hRI hscale
      (P.unitary ⟨R,hRI⟩ gR)

end AcceleratedLogConcave.Kinetic.DirectW12
