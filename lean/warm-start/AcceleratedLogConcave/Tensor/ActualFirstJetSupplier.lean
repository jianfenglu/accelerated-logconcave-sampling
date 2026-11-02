import AcceleratedLogConcave.Tensor.ActualKernelJetIntegral
import AcceleratedLogConcave.Tensor.PrimitiveScalarNormalization
import AcceleratedLogConcave.Tensor.RankTwoCuts
import AcceleratedLogConcave.Tensor.SingleEdgeAllProper

/-!

-/
noncomputable section
open Set MeasureTheory
open scoped ContDiff BigOperators Classical
namespace AcceleratedLogConcave.Tensor.QuantitativeKernel
open Conditional
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)

/-- The ordinary operator input is the LAST slot of the (n+1)-st center jet;
its output remains the distinguished output, with no permutation quotient. -/
def firstJetSlotChart (n : ℕ) :
    (Fin (n+1) ⊕ Unit) ≃ (Fin n ⊕ (Unit ⊕ Unit)) where
  toFun := fun a => match a with
    | .inl j => Fin.lastCases (.inr (.inl ())) (fun i => .inl i) j
    | .inr _ => .inr (.inr ())
  invFun := fun a => match a with
    | .inl j => .inl j.castSucc
    | .inr (.inl _) => .inl (Fin.last n)
    | .inr (.inr _) => .inr ()
  left_inv := by
    intro a
    rcases a with j | u
    · refine Fin.lastCases ?_ (fun i => ?_) j <;> simp
    · cases u; rfl
  right_inv := by
    intro a
    rcases a with j | (u | u)
    · simp
    · cases u; simp
    · cases u; rfl

/-- Exact all-order differentiation of U_1 in the spatial input, including
probability time zero. Only the fixed Gaussian center is differentiated. -/
theorem firstScaledJet_iteratedFDeriv_apply
    (d : PositiveVarianceFlowData E) (n : ℕ) {t : ℝ}
    (ht : -1 < t ∧ t < 1) (y : E) (v : Fin n → E) (w : E) :
    (iteratedFDeriv ℝ n (firstScaledJet d.F d.x d.r t) y v) w =
      t^n • scaledJet (n+1) d.F d.x d.r t y (Fin.snoc v w) := by
  let N : E → E := fun c => ∫ z, primitiveObservable d.F d.x d.r z ∂
    Gibbs.heatPosterior (primitivePotential d.F d.x d.r) (conditionalVariance t) c
  have hN : ContDiff ℝ ∞ N :=
    Tilt.contDiff_integral_heatPosterior (contDiff_primitivePotential d.hF d.x d.r)
      (m := 0) (le_refl 0) (conditionalVariance_pos ht.1 ht.2)
      (by simpa using primitivePotential_hessian_nonneg d.hF d.hlo d.x d.r)
      (continuous_primitiveObservable d.hF d.x d.r)
      (‖gradient d.F 0‖ + |d.ell| * ‖d.x‖) (|d.ell| * |d.r|) 1
      (by simpa only [pow_one] using norm_primitiveObservable_le_affine d.hF d.hlo d.hhi d.x d.r)
  have he : firstScaledJet d.F d.x d.r t = fun z => fderiv ℝ N (t • z) := by
    funext z
    exact (fderiv_centerMean_eq_firstScaledJet d.hF d.hlo d.hhi
      d.x d.r ht.1 ht.2 z).symm
  rw [he,iteratedFDeriv_comp_const_smul t
    (hN.fderiv_right (m := (n : WithTop ℕ∞)) (by simp))]
  change t^n • (iteratedFDeriv ℝ n (fderiv ℝ N) (t • y) v) w =
    t^n • iteratedFDeriv ℝ (n+1) N (t • y) (Fin.snoc v w)
  rw [iteratedFDeriv_succ_apply_right,Fin.init_snoc,Fin.snoc_last]

/-- Exact all-index coefficient transport into the legacy operator chart. -/
theorem firstScaledJet_operatorJetCoeff_eq
    (d : PositiveVarianceFlowData E) (n : ℕ) {t : ℝ}
    (ht : -1 < t ∧ t < 1) (y : E) :
    operatorJetCoeff n (firstScaledJet d.F d.x d.r t) y =
      t^n • EdgeClosure.relabel D (firstJetSlotChart n)
        (scaledJetCoefficient (n+1) d.F d.x d.r t y) := by
  ext a
  change inner ℝ (EuclideanSpace.basisFun (Fin D) ℝ (a (.inr (.inr ()))))
    ((iteratedFDeriv ℝ n (firstScaledJet d.F d.x d.r t) y
      (fun j => EuclideanSpace.basisFun (Fin D) ℝ (a (.inl j))))
        (EuclideanSpace.basisFun (Fin D) ℝ (a (.inr (.inl ()))))) = _
  rw [firstScaledJet_iteratedFDeriv_apply d n ht]
  simp only [inner_smul_right]
  change t^n * inner ℝ (EuclideanSpace.basisFun (Fin D) ℝ (a (.inr (.inr ()))))
      (scaledJet (n+1) d.F d.x d.r t y _) =
    t^n * inner ℝ (EuclideanSpace.basisFun (Fin D) ℝ
      (a (firstJetSlotChart n (.inr ()))))
      (scaledJet (n+1) d.F d.x d.r t y
        (fun j => EuclideanSpace.basisFun (Fin D) ℝ
          (a (firstJetSlotChart n (.inl j)))))
  have hdir : Fin.snoc
      (fun j : Fin n => EuclideanSpace.basisFun (Fin D) ℝ (a (.inl j)))
      (EuclideanSpace.basisFun (Fin D) ℝ (a (.inr (.inl ())))) =
      (fun j : Fin (n+1) => EuclideanSpace.basisFun (Fin D) ℝ
        (a (firstJetSlotChart n (.inl j)))) := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [firstJetSlotChart]
  exact congrArg (fun v => t^n * inner ℝ
    (EuclideanSpace.basisFun (Fin D) ℝ (a (.inr (.inr ()))))
    (scaledJet (n+1) d.F d.x d.r t y v)) hdir

/-- Original-data rectangular bound for the U_1 root before scalar cleanup.
The unbounded posterior integral has already been handled by the scaled-jet
supplier; the norm is never replaced by the full coefficient norm. -/
theorem firstScaledJet_operatorJetCoeff_source
    (d : PositiveVarianceFlowData E) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 d.b) (y : E) :
    AllProper D (operatorJetCoeff n (firstScaledJet d.F d.x d.r t) y)
      (t^n * (((conditionalVariance t^(n+1))⁻¹*(d.r*d.ell)) *
        (((n+1).factorial : ℝ)*Real.sqrt (2*conditionalVariance t)^(n+2)))) := by
  have ht' : -1 < t ∧ t < 1 := ⟨by linarith [ht.1],ht.2.trans_lt d.hb1⟩
  have hp : EdgeClosure.AllProper D (scaledJetCoefficient (n+1) d.F d.x d.r t y)
      (((conditionalVariance t^(n+1))⁻¹*(d.r*d.ell)) *
        (((n+1).factorial : ℝ)*Real.sqrt (2*conditionalVariance t)^(n+2))) := by
    intro S hS
    exact d.scaledJetCoefficient_splitNorm_le (n+1) ht' y S hS
  rw [firstScaledJet_operatorJetCoeff_eq d n ht' y]
  intro S hS
  rw [splitNorm_smul,abs_of_nonneg (pow_nonneg ht.1 n)]
  exact mul_le_mul_of_nonneg_left (hp.relabel (firstJetSlotChart n) S hS)
    (pow_nonneg ht.1 n)

/-- Cancellation of the positive Gaussian variance, with no division by time,
curvature, radius, or terminal time. -/
theorem firstJet_source_scalar (r ell t sigma C : ℝ) (hs : 0 < sigma) (n : ℕ) :
    t^n * (((sigma^(n+1))⁻¹*(r*ell)) *
      (C*Real.sqrt (2*sigma)^(n+2))) =
      (r*ell)*(C*Real.sqrt 2^(n+2))*(t/Real.sqrt sigma)^n := by
  have hv : Real.sqrt sigma ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  conv_lhs => arg 2; arg 1; arg 1; arg 1; rw [← Real.sq_sqrt hs.le]
  simp only [pow_add,pow_one,pow_two,mul_pow,div_pow]
  field_simp [hv,pow_ne_zero n hv]

/-- Positive-order root supplier in the precise kernel scale. At n=0 this
looser formula is still valid; the sharp rank-two supplier must be used for
the exceptional compositionConstant 0 = 1 branch. -/
theorem firstScaledJet_operatorJetCoeff_scaled
    (d : PositiveVarianceFlowData E) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 d.b) (y : E) :
    AllProper D (operatorJetCoeff n (firstScaledJet d.F d.x d.r t) y)
      ((d.r*d.ell) * (((n+1).factorial : ℝ)*Real.sqrt 2^(n+2)) * spatialScale d.b^n) := by
  intro S hS
  have ht' : -1 < t ∧ t < 1 := ⟨by linarith [ht.1],ht.2.trans_lt d.hb1⟩
  apply (firstScaledJet_operatorJetCoeff_source d n ht y S hS).trans
  rw [firstJet_source_scalar d.r d.ell t (conditionalVariance t)
    ((n+1).factorial : ℝ) (conditionalVariance_pos ht'.1 ht'.2) n]
  apply mul_le_mul_of_nonneg_left
  · exact pow_le_pow_left₀ (div_nonneg ht.1 (Real.sqrt_nonneg _))
      (ActualCoefficient.time_variance_ratio_le ht.1 ht.2 d.hb1) n
  · exact mul_nonneg (mul_nonneg d.hr.le d.hell)
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _))

/-- Zeroth operator jets are rank two in the exact retained legacy slots. -/
theorem operatorJetCoeff_zero_eq_rankTwo_relabel (f : E → E →L[ℝ] E) (y : E) :
    operatorJetCoeff 0 f y = EdgeClosure.relabel D (firstJetSlotChart 0)
      (ActualCoefficient.rankTwoCoeff (f y)) := by
  ext a
  simp [operatorJetCoeff,EdgeClosure.relabel,firstJetSlotChart,
    ActualCoefficient.rankTwoCoeff,ActualCoefficient.basis]
  rw [← Fin.last_zero, Fin.lastCases_last]

/-- The sharp zero-order U_1 root bound, with beta = r*ell, rather than the
looser first center-jet factorial bound. This closes the exceptional n=0 root. -/
theorem firstScaledJet_operatorJetCoeff_zero
    (d : PositiveVarianceFlowData E) {t : ℝ}
    (ht : t ∈ Icc 0 d.b) (y : E) :
    AllProper D (operatorJetCoeff 0 (firstScaledJet d.F d.x d.r t) y) (d.r*d.ell) := by
  have hp : EdgeClosure.AllProper D
      (ActualCoefficient.rankTwoCoeff (firstScaledJet d.F d.x d.r t y)) (d.r*d.ell) := by
    intro S hS
    exact (ActualCoefficient.rankTwo_splitNorm_le _ S hS).trans
      (norm_firstScaledJet_le d.hF d.hell d.hlo d.hhi d.x d.hr
        (by linarith [ht.1]) (ht.2.trans_lt d.hb1) y)
  rw [operatorJetCoeff_zero_eq_rankTwo_relabel]
  exact hp.relabel (firstJetSlotChart 0)

/-- The complete original-data root supplier in the literal kernel constants,
including their sharp exceptional first-jet coefficient. No actual-flow or
inverse induction is part of this theorem. -/
theorem firstScaledJet_primitive_allProper
    (d : PositiveVarianceFlowData E) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 d.b) (y : E) :
    AllProper D (operatorJetCoeff n (firstScaledJet d.F d.x d.r t) y)
      ((d.r*d.ell) * primitiveConstant (n+1) * spatialScale d.b^n) := by
  cases n with
  | zero => simpa [primitiveConstant] using firstScaledJet_operatorJetCoeff_zero d ht y
  | succ n =>
    have hn : n+1+1 ≠ 1 := by omega
    simpa only [primitiveConstant,ite_eq_right hn] using
      firstScaledJet_operatorJetCoeff_scaled d (n+1) ht y

/-- Positive spatial derivatives of U_1 at probability time zero vanish by
the exact t^n identity, not by dividing a positive-time formula by t. -/
theorem firstScaledJet_iteratedFDeriv_time_zero
    (d : PositiveVarianceFlowData E) (n : ℕ) (hn : 0 < n) (y : E) :
    iteratedFDeriv ℝ n (firstScaledJet d.F d.x d.r 0) y = 0 := by
  apply ContinuousMultilinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  simpa only [zero_pow (Nat.ne_of_gt hn),zero_smul,
    zero_apply] using
    firstScaledJet_iteratedFDeriv_apply d n (t := 0) (by norm_num) y v w

end AcceleratedLogConcave.Tensor.QuantitativeKernel
