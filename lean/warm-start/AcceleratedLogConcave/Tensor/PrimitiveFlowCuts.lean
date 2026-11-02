import AcceleratedLogConcave.Tensor.RankTwoCuts
import AcceleratedLogConcave.Tensor.PrimitiveScalarNormalization
import AcceleratedLogConcave.Conditional.ScaledJetSplitNorm
import AcceleratedLogConcave.Conditional.ScaledJetPolynomial
import AcceleratedLogConcave.Conditional.FirstJet
import AcceleratedLogConcave.Conditional.Transport.ActualFlowVolterra

/-!

-/
noncomputable section
set_option autoImplicit false
open Set
open scoped ContDiff BigOperators Classical
namespace AcceleratedLogConcave.Tensor.ActualCoefficient
open Conditional Conditional.ScaledJetPolynomial Conditional.Transport.SpatialFlow EdgeClosure
variable {D : ℕ}

 theorem vectorCoeff_smul {I : Type*} [Fintype I] (c : ℝ)
    (T : ContinuousMultilinearMap ℝ (fun _ : I => Space D) (Space D)) :
    vectorCoeff (c • T) = c • vectorCoeff T := by
  ext a
  simp [vectorCoeff,mapCoeff]

 theorem vectorCoeff_scaledJet (q : ℕ) (F : Space D → ℝ)
    (x : Space D) (r t : ℝ) (y : Space D) :
    vectorCoeff (scaledJet q F x r t y) = scaledJetCoefficient q F x r t y := rfl

 theorem velocity_iteratedFDeriv_eq_scaledJet
    (d : PositiveVarianceFlowData (Space D)) (q : ℕ) (y : Space D)
    {t : ℝ} (ht : -1 < t ∧ t < 1) :
    iteratedFDeriv ℝ q (probabilityVelocity d.F d.x d.r t) y =
      (-d.r*t^q) • scaledJet q d.F d.x d.r t y := by
  have hM : ContDiff ℝ ∞ (conditionalMean d.F d.x d.r t) := by
    have hc : ContDiff ℝ ∞ (fun z : Space D => (t,z)) :=
      contDiff_const.prodMk contDiff_id
    have hh := (contDiffOn_conditionalMean d.hF d.hlo d.hhi d.x d.r).comp
      hc.contDiffOn (s := Set.univ) (fun _ _ => ht)
    exact contDiffOn_univ.mp hh
  change iteratedFDeriv ℝ q (fun z => -d.r • conditionalMean d.F d.x d.r t z) y = _
  rw [iteratedFDeriv_const_smul_apply' (hM.of_le (by simp)).contDiffAt,
    iteratedFDeriv_conditionalMean_eq_scaledJet_of_curvature q d.hF d.hlo d.hhi
      d.x d.r ht.1 ht.2 y,smul_smul]

/-- Exact coefficient identity, before taking any norm. Every input and output
index remains present; repeated labels require no special case. -/
 theorem probabilityVelocity_vectorCoeff_eq (d : PositiveVarianceFlowData (Space D))
    (q : ℕ) (y : Space D) {t : ℝ} (ht : -1 < t ∧ t < 1) :
    vectorCoeff (iteratedFDeriv ℝ q (probabilityVelocity d.F d.x d.r t) y) =
      (-d.r*t^q) • scaledJetCoefficient q d.F d.x d.r t y := by
  rw [velocity_iteratedFDeriv_eq_scaledJet d q y ht,vectorCoeff_smul,vectorCoeff_scaledJet]

/-- The exact sharp derivative operator, nonsingular even at time zero. -/
 theorem fderiv_probabilityVelocity_eq (d : PositiveVarianceFlowData (Space D))
    (y : Space D) {t : ℝ} (ht : -1 < t ∧ t < 1) :
    fderiv ℝ (probabilityVelocity d.F d.x d.r t) y =
      (-d.r*t) • firstScaledJet d.F d.x d.r t y := by
  apply ContinuousLinearMap.ext
  intro v
  have h := congrArg (fun T => T (fun _ : Fin 1 => v))
    (velocity_iteratedFDeriv_eq_scaledJet d 1 y ht)
  simpa only [iteratedFDeriv_one_apply,smul_apply,pow_one,
    scaledJet_one_apply_eq_firstScaledJet d.hF d.hlo d.hhi d.x d.r ht.1 ht.2] using h

 theorem norm_fderiv_probabilityVelocity_le (d : PositiveVarianceFlowData (Space D))
    (y : Space D) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    ‖fderiv ℝ (probabilityVelocity d.F d.x d.r t) y‖ ≤ (d.r^2*d.ell)*t := by
  have htime : -1 < t ∧ t < 1 := ⟨by linarith [ht.1],ht.2.trans_lt d.hb1⟩
  rw [fderiv_probabilityVelocity_eq d y htime,norm_smul,Real.norm_eq_abs,
    abs_mul,abs_neg,abs_of_pos d.hr,abs_of_nonneg ht.1]
  calc
    d.r*t*‖firstScaledJet d.F d.x d.r t y‖ ≤ d.r*t*(d.r*d.ell) :=
      mul_le_mul_of_nonneg_left
        (norm_firstScaledJet_le d.hF d.hell d.hlo d.hhi d.x d.hr htime.1 htime.2 y)
        (mul_nonneg d.hr.le ht.1)
    _ = _ := by ring

 theorem probabilityVelocity_allProper_one (d : PositiveVarianceFlowData (Space D))
    (y : Space D) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    AllProper D (vectorCoeff (iteratedFDeriv ℝ 1
      (probabilityVelocity d.F d.x d.r t) y)) ((d.r^2*d.ell)*t) := by
  intro S hS
  rw [vectorCoeff_one_eq_rankTwo]
  exact (rankTwo_splitNorm_le _ S hS).trans (norm_fderiv_probabilityVelocity_le d y ht)

/-- The first-order sharp bound also survives arbitrary output placement. -/
 theorem probabilityVelocity_allProper_one_relabel {A : Type*}
    [Fintype A] [DecidableEq A]
    (d : PositiveVarianceFlowData (Space D)) (e : (Fin 1 ⊕ Unit) ≃ A)
    (y : Space D) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    AllProper D (relabel D e (vectorCoeff (iteratedFDeriv ℝ 1
      (probabilityVelocity d.F d.x d.r t) y))) ((d.r^2*d.ell)*t) :=
  (probabilityVelocity_allProper_one d y ht).relabel e

/-- The literal sigma^q source bound, still retaining the full t^q factor. -/
 theorem probabilityVelocity_splitNorm_source (d : PositiveVarianceFlowData (Space D))
    (q : ℕ) (y : Space D) {t : ℝ} (ht : t ∈ Icc 0 d.b)
    (S : Finset (Fin q ⊕ Unit)) (hS : NontrivialSplit S) :
    splitNorm D S (vectorCoeff (iteratedFDeriv ℝ q
      (probabilityVelocity d.F d.x d.r t) y)) ≤
      (d.r*t^q) * (((conditionalVariance t^q)⁻¹*(d.r*d.ell))*
        ((q.factorial:ℝ)*Real.sqrt (2*conditionalVariance t)^(q+1))) := by
  have htime : -1 < t ∧ t < 1 := ⟨by linarith [ht.1],ht.2.trans_lt d.hb1⟩
  rw [probabilityVelocity_vectorCoeff_eq d q y htime,splitNorm_smul,
    abs_mul,abs_neg,abs_of_pos d.hr,abs_of_nonneg (pow_nonneg ht.1 q)]
  exact mul_le_mul_of_nonneg_left
    (d.scaledJetCoefficient_splitNorm_le q htime y S hS)
    (mul_nonneg d.hr.le (pow_nonneg ht.1 q))

/-- Stable all-proper supplier for strong induction. No division by alpha or b;
no positive dimension, positive curvature, or nonzero time hypothesis. -/
 theorem probabilityVelocity_allProper_ge_two (d : PositiveVarianceFlowData (Space D))
    (q : ℕ) (hq : 2 ≤ q) (y : Space D) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    AllProper D (vectorCoeff (iteratedFDeriv ℝ q
      (probabilityVelocity d.F d.x d.r t) y))
      ((d.r^2*d.ell)*t*((q.factorial:ℝ)*Real.sqrt 2^(q+1))*
        (d.b/Real.sqrt (1-d.b^2))^(q-1)) := by
  intro S hS
  have htime : -1 < t ∧ t < 1 := ⟨by linarith [ht.1],ht.2.trans_lt d.hb1⟩
  have hs := conditionalVariance_pos htime.1 htime.2
  have he : (d.r*t^q) * (((conditionalVariance t^q)⁻¹*(d.r*d.ell))*
      ((q.factorial:ℝ)*Real.sqrt (2*conditionalVariance t)^(q+1))) =
      (d.r^2*d.ell)*t*((q.factorial:ℝ)*Real.sqrt 2^(q+1))*
        (t/Real.sqrt (1-t^2))^(q-1) := by
    obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le (show 1 ≤ q by omega)
    subst q
    simpa [conditionalVariance, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      primitive_scalar_normalization d.r d.ell t (conditionalVariance t)
        (((1+k).factorial):ℝ) hs k
  apply (probabilityVelocity_splitNorm_source d q y ht S hS).trans
  rw [he]
  apply mul_le_mul_of_nonneg_left
  · exact pow_le_pow_left₀ (div_nonneg ht.1 (Real.sqrt_nonneg _))
      (time_variance_ratio_le ht.1 ht.2 d.hb1) (q-1)
  · exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) d.hell) ht.1)
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _))

/-- Arbitrary placement of the distinguished output is a true slot relabeling,
not a directional estimate. -/
 theorem probabilityVelocity_allProper_relabel {A : Type*} [Fintype A] [DecidableEq A]
    (d : PositiveVarianceFlowData (Space D)) (q : ℕ) (hq : 2 ≤ q)
    (e : (Fin q ⊕ Unit) ≃ A) (y : Space D) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    AllProper D (relabel D e (vectorCoeff (iteratedFDeriv ℝ q
      (probabilityVelocity d.F d.x d.r t) y)))
      ((d.r^2*d.ell)*t*((q.factorial:ℝ)*Real.sqrt 2^(q+1))*
        (d.b/Real.sqrt (1-d.b^2))^(q-1)) :=
  (probabilityVelocity_allProper_ge_two d q hq y ht).relabel e

end AcceleratedLogConcave.Tensor.ActualCoefficient
