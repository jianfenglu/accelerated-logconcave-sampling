import DirectW12.CovarianceIntegration
import DirectW12.LiteralQuadrature

/-!

-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace AcceleratedLogConcave.Root.RecursiveInnovation
open Numerics.AffineGraph Kinetic Kinetic.ConditionalContraction
/-- All extended phase L² tests, literal source weights, physical inverse at R. -/
theorem sourcePhysicalCorrector_bound_sq
    {ι : Type*} [fi : Fintype ι] [di : DecidableEq ι] {m : ℕ}
    {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1/2)
  {V : (EuclideanSpace ℝ ι) → ℝ} (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ V) z a a)
  (hup : ∀ z a, fderiv ℝ (fderiv ℝ V) z a a ≤ ‖a‖^2)
  (G : MeanGeometry m) (hm : 0 < m) (t : ℝ) (ht : 0 < t) (K : ℕ)
  (P : Analysis.Poisson.ReferencePoissonFamily (EuclideanSpace ℝ ι) 0 (1/2))
  (hpotential : ∀ r ∈ Icc (0:ℝ) (1/2),
    P.potential r = Gibbs.heatPotential V (2*h^2*(1-r^2)))
  (hscale : ∀ r ∈ Icc (0:ℝ) (1/2), P.scale r = (2*h^2)*r)
    (R : ClockLaw.Clock)
    (f : Lp ℝ 2 (gaussianPhaseMeasure (P.law R))) :
    let κ := physicalSourceSection (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf)
      (V := V) (hV := hV) (hlo := hlo) (hup := hup)
      (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := R)
    let hκ := physicalSourceSection_invariant (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf)
      (V := V) (hV := hV) (hlo := hlo) (hup := hup)
      (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := R)
    let A := sourcePhysicalCorrector (ι := ι) (fi := fi) (P := P) (clock := R)
    ‖physicalDormantChannel (1/2) (Real.sqrt 3/2) source_split_coefficients
      (P.law R) κ hκ (A.adjoint f)-A.adjoint f‖^2 ≤
        (25/32 : ℝ) * (2*h^2)^2 * ‖f‖^2 := by
  classical
  let c := fun i => (1+Real.sqrt (2*h^2)*((R : ℝ)-(sourceNode hh K R i : ℝ))+
    (2*h^2)*((R : ℝ)^2-(sourceNode hh K R i : ℝ)^2)/2)^2
  have hj := sourcePhysicalCorrector_jensen (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf)
      (V := V) (hV := hV) (hlo := hlo) (hup := hup)
      (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := R) (f := f)
  have hi := sourcePhysicalCoefficient_covariance_integral (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf)
      (V := V) (hV := hV) (hlo := hlo) (hup := hup)
      (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (hpotential := hpotential) (R := R) (f := f)
  apply (hj.trans hi).trans
  have hsum :
      (∑ i, (sourceWeight h K R i)^2 * (1-(sourceNode hh K R i : ℝ)^2) *
        (∫ z, sourceCurvature (ι := ι) (fi := fi) (h := h) (hh := hh)
          (K := K) (P := P) (R := R) (f := f) (i := i) z ∂(P.law R).prod (stdGaussian (EuclideanSpace ℝ ι)))) ≤
      (∑ i, (sourceWeight h K R i)^2 * (1-(sourceNode hh K R i : ℝ)^2) * c i) * ‖f‖^2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have hu := (sourceNode hh K R i).property
    change 0 ≤ (sourceNode hh K R i : ℝ) ∧ (sourceNode hh K R i : ℝ) ≤ 1/2 at hu
    have hw : 0 ≤ (sourceWeight h K R i)^2 * (1-(sourceNode hh K R i : ℝ)^2) :=
      mul_nonneg (sq_nonneg _) (by nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hu.2)])
    simpa only [mul_assoc, c] using mul_le_mul_of_nonneg_left
      (sourceCurvature_bound (ι := ι) (fi := fi) (h := h) (hh := hh)
        (K := K) (P := P) (hscale := hscale) (R := R) (f := f) (i := i)) hw
  calc
    _ ≤ 2*h^4 * ((∑ i, (sourceWeight h K R i)^2 *
        (1-(sourceNode hh K R i : ℝ)^2) * c i) * ‖f‖^2) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (2*h^4 * (∑ i, (sourceWeight h K R i)^2 *
        (1-(sourceNode hh K R i : ℝ)^2) * c i)) * ‖f‖^2 := by ring
    _ ≤ (25/32 : ℝ) * (2*h^2)^2 * ‖f‖^2 :=
      mul_le_mul_of_nonneg_right (ClockSchedule.source_quadrature_C1 (hh := hh) (hhalf := hhalf) (K := K) (R := R)) (sq_nonneg _)

/-- Scoped exact-reference C=1 theorem. The physical potential/clock identities
are explicit; they do not posit the desired covariance or operator estimate. -/
theorem physicalSourceSection_W12
    {ι : Type*} [fi : Fintype ι] [di : DecidableEq ι] {m : ℕ}
    {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1/2)
  {V : (EuclideanSpace ℝ ι) → ℝ} (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ V) z a a)
  (hup : ∀ z a, fderiv ℝ (fderiv ℝ V) z a a ≤ ‖a‖^2)
  (G : MeanGeometry m) (hm : 0 < m) (t : ℝ) (ht : 0 < t) (K : ℕ)
  (P : Analysis.Poisson.ReferencePoissonFamily (EuclideanSpace ℝ ι) 0 (1/2))
  (hpotential : ∀ r ∈ Icc (0:ℝ) (1/2),
    P.potential r = Gibbs.heatPotential V (2*h^2*(1-r^2)))
  (hscale : ∀ r ∈ Icc (0:ℝ) (1/2), P.scale r = (2*h^2)*r)
    (R : ClockLaw.Clock) :
    physicalDormantW12 P R
      (physicalSourceSection (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf)
      (V := V) (hV := hV) (hlo := hlo) (hup := hup)
      (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := R))
      (physicalSourceSection_invariant (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf)
      (V := V) (hV := hV) (hlo := hlo) (hup := hup)
      (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := R))
      1 (2*h^2) := by
  unfold physicalDormantW12 DormantW12
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  have hb := sourcePhysicalCorrector_bound_sq (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf)
      (V := V) (hV := hV) (hlo := hlo) (hup := hup)
      (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (hpotential := hpotential) (hscale := hscale) (R := R) (f := f)
  dsimp only at hb
  change ‖physicalDormantChannel (1/2) (Real.sqrt 3/2) source_split_coefficients
    (P.law R) (physicalSourceSection (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf)
      (V := V) (hV := hV) (hlo := hlo) (hup := hup)
      (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := R))
    (physicalSourceSection_invariant (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf)
      (V := V) (hV := hV) (hlo := hlo) (hup := hup)
      (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := R))
    ((sourcePhysicalCorrector (ι := ι) (fi := fi) (P := P) (clock := R)).adjoint f)-(sourcePhysicalCorrector (ι := ι) (fi := fi) (P := P) (clock := R)).adjoint f‖ ≤
      (1*(2*h^2))*‖f‖
  have hn : 0 ≤ (2*h^2)*‖f‖ := by positivity
  have hs : 0 ≤ (2*h^2)^2 * ‖f‖^2 := by positivity
  nlinarith [norm_nonneg (physicalDormantChannel (1/2) (Real.sqrt 3/2)
    source_split_coefficients (P.law R)
    (physicalSourceSection (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf)
      (V := V) (hV := hV) (hlo := hlo) (hup := hup)
      (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := R))
    (physicalSourceSection_invariant (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf)
      (V := V) (hV := hV) (hlo := hlo) (hup := hup)
      (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := R))
    ((sourcePhysicalCorrector (ι := ι) (fi := fi) (P := P) (clock := R)).adjoint f)-(sourcePhysicalCorrector (ι := ι) (fi := fi) (P := P) (clock := R)).adjoint f)]
end AcceleratedLogConcave.Root.RecursiveInnovation
