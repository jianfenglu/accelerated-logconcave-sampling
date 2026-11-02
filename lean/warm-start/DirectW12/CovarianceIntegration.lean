import DirectW12.CrossCurvature
import DirectW12.SourceRetainedJoin
import DirectW12.RetainedInnovation
import AcceleratedLogConcave.Kinetic.Mixing.SourceCollision

/-!

-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace
namespace AcceleratedLogConcave.Root.RecursiveInnovation
open Numerics.AffineGraph Kinetic Kinetic.DirectW12 Kinetic.ConditionalContraction


/-- Literal source node; notation only, no change of quadrature rule. -/
abbrev sourceNode {h : ℝ} (hh : 0 < h) (K : ℕ) (R : ClockLaw.Clock) :
    Fin (ClockSchedule.sourceCells h * ClockSchedule.sourceOrder K) → ClockLaw.Clock :=
  ClockSchedule.node (ClockSchedule.sourceCells h) (ClockSchedule.sourceOrder K)
    (ClockSchedule.sourceCells_pos hh) R
abbrev sourceWeight (h : ℝ) (K : ℕ) (R : ClockLaw.Clock) :
    Fin (ClockSchedule.sourceCells h * ClockSchedule.sourceOrder K) → ℝ :=
  ClockSchedule.weight (ClockSchedule.sourceCells h) (ClockSchedule.sourceOrder K) R

def sourceCurvature
    {ι : Type*} [fi : Fintype ι] {h : ℝ} (hh : 0 < h) (K : ℕ)
    (P : Analysis.Poisson.ReferencePoissonFamily (EuclideanSpace ℝ ι) 0 (1/2)) (R : ClockLaw.Clock)
    (f : Lp ℝ 2 (gaussianPhaseMeasure (P.law R)))
    (i : Fin (ClockSchedule.sourceCells h * ClockSchedule.sourceOrder K)) (z : (EuclideanSpace ℝ ι) × (EuclideanSpace ℝ ι)) : ℝ :=
  fderiv ℝ (fderiv ℝ (P.potential (sourceNode hh K R i)))
    (physicalCenter (ι := ι) (h := h) (hh := hh) (K := K)
      (P := P) (clock := R) (parent := z) (i := i))
    (sourcePhysicalCoefficient (ι := ι) (fi := fi) (P := P) (clock := R) (f := f) z.1) (sourcePhysicalCoefficient (ι := ι) (fi := fi) (P := P) (clock := R) (f := f) z.1)

theorem sourceCurvature_nonneg
    {ι : Type*} [fi : Fintype ι] {h : ℝ} (hh : 0 < h) (K : ℕ)
    (P : Analysis.Poisson.ReferencePoissonFamily (EuclideanSpace ℝ ι) 0 (1/2)) (R : ClockLaw.Clock)
    (f : Lp ℝ 2 (gaussianPhaseMeasure (P.law R))) (i : Fin (ClockSchedule.sourceCells h * ClockSchedule.sourceOrder K)) (z : (EuclideanSpace ℝ ι) × (EuclideanSpace ℝ ι)) :
    0 ≤ sourceCurvature (ι := ι) (fi := fi) (h := h) (hh := hh)
      (K := K) (P := P) (R := R) (f := f) (i := i) z :=
  P.hessian_nonneg _ (sourceNode hh K R i).property _ _

theorem sourceCurvature_integrable
    {ι : Type*} [fi : Fintype ι] {h : ℝ} (hh : 0 < h) (K : ℕ)
    (P : Analysis.Poisson.ReferencePoissonFamily (EuclideanSpace ℝ ι) 0 (1/2)) (R : ClockLaw.Clock)
    (f : Lp ℝ 2 (gaussianPhaseMeasure (P.law R)))
    (i : Fin (ClockSchedule.sourceCells h * ClockSchedule.sourceOrder K)) :
    Integrable (sourceCurvature (ι := ι) (fi := fi) (h := h) (hh := hh)
      (K := K) (P := P) (R := R) (f := f) (i := i)) ((P.law R).prod (stdGaussian (EuclideanSpace ℝ ι))) := by
  exact terminal_curvature_integrable (P := P) (ell := Real.sqrt (2*h^2))
    (R := R) (u := sourceNode hh K R i) (gR := gaussianAverage (P.law R) f)

theorem sourceCurvature_bound
    {ι : Type*} [fi : Fintype ι] {h : ℝ} (hh : 0 < h) (K : ℕ)
    (P : Analysis.Poisson.ReferencePoissonFamily (EuclideanSpace ℝ ι) 0 (1/2))
    (hscale : ∀ r ∈ Icc (0:ℝ) (1/2), P.scale r = (2*h^2)*r)
    (R : ClockLaw.Clock) (f : Lp ℝ 2 (gaussianPhaseMeasure (P.law R)))
    (i : Fin (ClockSchedule.sourceCells h * ClockSchedule.sourceOrder K)) :
    (∫ z, sourceCurvature (ι := ι) (fi := fi) (h := h) (hh := hh)
      (K := K) (P := P) (R := R) (f := f) (i := i) z ∂(P.law R).prod (stdGaussian (EuclideanSpace ℝ ι))) ≤
      (1+Real.sqrt (2*h^2)*((R : ℝ)-(sourceNode hh K R i : ℝ))+
        (2*h^2)*((R : ℝ)^2-(sourceNode hh K R i : ℝ)^2)/2)^2 * ‖f‖^2 := by
  have hu := ClockSchedule.nodeValue_mem (ClockSchedule.sourceCells h)
    (ClockSchedule.sourceOrder K) (ClockSchedule.sourceCells_pos hh) R i
  have hc := physical_poisson_cross_curvature
    (P := P) (ell := Real.sqrt (2*h^2)) (A := 2*h^2)
    (u := (sourceNode hh K R i : ℝ)) (R := (R : ℝ))
    (hell := Real.sqrt_nonneg (2*h^2)) (hA := by positivity)
    (hu := hu.1) (huR := hu.2)
    (huI := (sourceNode hh K R i).property) (hRI := R.property)
    (hscale := fun r hr => hscale r
      ⟨(sourceNode hh K R i).property.1.trans hr.1.le, hr.2.le.trans R.property.2⟩)
    (gR := gaussianAverage (P.law R) f)
  have hg : ‖gaussianAverage (P.law R) f‖ ≤ ‖f‖ := by
    calc
      _ ≤ ‖gaussianAverage (P.law R)‖ * ‖f‖ := (gaussianAverage (P.law R)).le_opNorm f
      _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right (gaussianAverage_norm_le _) (norm_nonneg _)
      _ = _ := one_mul _
  apply hc.trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  nlinarith [norm_nonneg (gaussianAverage (P.law R) f), norm_nonneg f]

/-- Integrate the actual pointwise covariance at the measurable physical inverse.
Nonnegative disintegration is converted to real integrals only after both
fixed-parent and full-joint integrability have independently been proved. -/
theorem sourcePhysicalCoefficient_covariance_integral
    {ι : Type*} [fi : Fintype ι] [di : DecidableEq ι]
    {m : ℕ} {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1/2)
  {V : (EuclideanSpace ℝ ι) → ℝ} (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ V) z a a)
  (hup : ∀ z a, fderiv ℝ (fderiv ℝ V) z a a ≤ ‖a‖^2)
  (G : MeanGeometry m) (hm : 0 < m) (t : ℝ) (ht : 0 < t) (K : ℕ)
  (P : Analysis.Poisson.ReferencePoissonFamily (EuclideanSpace ℝ ι) 0 (1/2))
  (hpotential : ∀ r ∈ Icc (0:ℝ) (1/2),
    P.potential r = Gibbs.heatPotential V (2*h^2*(1-r^2)))
    (R : ClockLaw.Clock)
    (f : Lp ℝ 2 (gaussianPhaseMeasure (P.law R))) :
    let κ := physicalSourceSection (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf)
        (V := V) (hV := hV) (hlo := hlo) (hup := hup)
        (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := R)
    (∫ z, ((Real.sqrt 3/2) * inner ℝ (z.2-z.1.2)
      (sourcePhysicalCoefficient (ι := ι) (fi := fi) (P := P) (clock := R) (f := f) z.1.1.1))^2
      ∂dormantJoint ((P.law R).prod (stdGaussian (EuclideanSpace ℝ ι))) (stdGaussian (EuclideanSpace ℝ ι)) κ) ≤
      2*h^4 * ∑ i, (sourceWeight h K R i)^2 *
        (1-(sourceNode hh K R i : ℝ)^2) *
        (∫ z, sourceCurvature (ι := ι) (fi := fi) (h := h) (hh := hh)
      (K := K) (P := P) (R := R) (f := f) (i := i) z ∂(P.law R).prod (stdGaussian (EuclideanSpace ℝ ι))) := by
  classical
  let ν := (P.law R).prod (stdGaussian (EuclideanSpace ℝ ι))
  let κ := physicalSourceSection (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf)
        (V := V) (hV := hV) (hlo := hlo) (hup := hup)
        (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := R)
  let v := sourcePhysicalCoefficient (ι := ι) (fi := fi) (P := P) (clock := R) (f := f)
  let F := fun z : GaussianPhase (EuclideanSpace ℝ ι) × (EuclideanSpace ℝ ι) => ((Real.sqrt 3/2)*inner ℝ (z.2-z.1.2) (v z.1.1.1))^2
  let B := fun z : (EuclideanSpace ℝ ι) × (EuclideanSpace ℝ ι) => 2*h^4 * ∑ i, (sourceWeight h K R i)^2 *
    (1-(sourceNode hh K R i : ℝ)^2) * sourceCurvature (ι := ι) (fi := fi) (h := h) (hh := hh)
      (K := K) (P := P) (R := R) (f := f) (i := i) z
  have hF : Integrable F (dormantJoint ν (stdGaussian (EuclideanSpace ℝ ι)) κ) :=
    physical_lift_increment_integrable_sq
      (μ := P.law R) (s := 1/2) (n := Real.sqrt 3/2)
      (hsn := source_split_coefficients) (κ := κ)
      (hκ := physicalSourceSection_invariant (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf)
        (V := V) (hV := hV) (hlo := hlo) (hup := hup)
        (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := R)) (G := v)
  have hB : Integrable B ν := by
    apply Integrable.const_mul
    exact integrable_finsetSum Finset.univ (fun i _ =>
      (sourceCurvature_integrable (ι := ι) (fi := fi) (h := h) (hh := hh)
      (K := K) (P := P) (R := R) (f := f) (i := i)).const_mul _)
  have hw (i) : 0 ≤ 1-(sourceNode hh K R i : ℝ)^2 := by
    have hu := (sourceNode hh K R i).property
    change 0 ≤ (sourceNode hh K R i : ℝ) ∧ (sourceNode hh K R i : ℝ) ≤ 1/2 at hu
    nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hu.2)]
  have hB0 (z) : 0 ≤ B z := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun i _ => mul_nonneg
      (mul_nonneg (sq_nonneg _) (hw i)) (sourceCurvature_nonneg (ι := ι) (fi := fi) (h := h) (hh := hh)
      (K := K) (P := P) (R := R) (f := f) (i := i) z))
  have hn : (Real.sqrt 3/2)^2 = (3/4 : ℝ) := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    norm_num
  have hpoint (z : (EuclideanSpace ℝ ι) × (EuclideanSpace ℝ ι)) :
      let d := physicalSourceData (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf)
        (V := V) (hV := hV) (hlo := hlo) (hup := hup)
        (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := R) (parent := z)
      (∫⁻ q, ENNReal.ofReal (((Real.sqrt 3/2)*
        inner ℝ (RetainedLaw.output d q-q.1.1) (v z.1))^2) ∂RetainedLaw.averagedJoint d)
        ≤ ENNReal.ofReal (B z) := by
    dsimp only
    let d := physicalSourceData (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf)
        (V := V) (hV := hV) (hlo := hlo) (hup := hup)
        (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := R) (parent := z)
    have he (q : RetainedLaw.Execution (ι := ι)
        (m := ClockSchedule.sourceCells h * ClockSchedule.sourceOrder K)) :
        ((Real.sqrt 3/2)*inner ℝ (RetainedLaw.output d q-q.1.1) (v z.1))^2 =
          (3/4:ℝ) * inner ℝ (v z.1) (RetainedLaw.output d q-q.1.1)^2 := by
      rw [mul_pow, hn, real_inner_comm]
    have hi : Integrable (fun q => ((Real.sqrt 3/2)*
        inner ℝ (RetainedLaw.output d q-q.1.1) (v z.1))^2) (RetainedLaw.averagedJoint d) := by
      simp_rw [he]
      exact (retained_innovation_integrable (ι := ι) (fi := fi) (d := d) (v := v z.1)).const_mul _
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun q => sq_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    simp_rw [he]
    rw [integral_const_mul]
    have hb := physical_source_innovation_bound (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf)
        (V := V) (hV := hV) (hlo := hlo) (hup := hup)
        (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := R) (parent := z) (v := v z.1)
    change (3/4:ℝ)*(∫ q, inner ℝ (v z.1) (RetainedLaw.output d q-q.1.1)^2
      ∂RetainedLaw.averagedJoint d) ≤ _ at hb
    apply hb.trans_eq
    dsimp only [B]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [sourceCurvature]
    rw [hpotential _ (sourceNode hh K R i).property]
  have he : ENNReal.ofReal (∫ z, F z ∂dormantJoint ν (stdGaussian (EuclideanSpace ℝ ι)) κ) ≤
      ENNReal.ofReal (∫ z, B z ∂ν) := by
    rw [ofReal_integral_eq_lintegral_ofReal hF (Eventually.of_forall fun z => sq_nonneg _)]
    rw [sourcePhysicalCoefficient_lintegral (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf)
        (V := V) (hV := hV) (hlo := hlo) (hup := hup)
        (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := R) (f := f)]
    rw [ofReal_integral_eq_lintegral_ofReal hB (Eventually.of_forall hB0)]
    exact lintegral_mono hpoint
  have hr := ENNReal.toReal_mono (by simp : ENNReal.ofReal (∫ z, B z ∂ν) ≠ ⊤) he
  rw [ENNReal.toReal_ofReal (integral_nonneg fun z => sq_nonneg _),
    ENNReal.toReal_ofReal (integral_nonneg hB0)] at hr
  have hBeq : (∫ z, B z ∂ν) = 2*h^4 * ∑ i, (sourceWeight h K R i)^2 *
      (1-(sourceNode hh K R i : ℝ)^2) * (∫ z, sourceCurvature (ι := ι) (fi := fi) (h := h) (hh := hh)
      (K := K) (P := P) (R := R) (f := f) (i := i) z ∂ν) := by
    dsimp only [B]
    rw [integral_const_mul, integral_finsetSum Finset.univ
      (fun i _ => (sourceCurvature_integrable (ι := ι) (fi := fi) (h := h) (hh := hh)
      (K := K) (P := P) (R := R) (f := f) (i := i)).const_mul _)]
    simp_rw [integral_const_mul]
    rfl
  rw [hBeq] at hr
  exact hr
end AcceleratedLogConcave.Root.RecursiveInnovation
