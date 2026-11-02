import AcceleratedLogConcave.Tensor.OriginalDataFlowBounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!

-/
noncomputable section
set_option autoImplicit false
open Set Function
open scoped ContDiff Classical BigOperators
namespace AcceleratedLogConcave.Tensor.InverseFlow
open Conditional Conditional.Transport.SpatialFlow
open ActualCoefficient EdgeClosure FlowInduction
open AcceleratedLogConcave.Analysis.FixedCut
variable {D : ℕ}

abbrev actualB (d : PositiveVarianceFlowData (Space D)) (t : ℝ) :=
  transportedJacobian d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 t
abbrev actualJ (d : PositiveVarianceFlowData (Space D)) (t : ℝ) :=
  fderiv ℝ (actualY d t)

/-- Pay invertibility by differentiating both literal inverse maps.
No smallness or membership in the time slab is needed for the clipped maps. -/
theorem original_data_inverse_pair (d : PositiveVarianceFlowData (Space D))
    (t : ℝ) (y : Space D) :
    actualJ d t y * actualB d t y = 1 ∧ actualB d t y * actualJ d t y = 1 := by
  let T := forwardProbabilityTransport d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 t
  let Y := backwardProbabilityTransport d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 t
  have hT := (contDiff_one_forwardProbabilityTransport d.hF d.hell d.hlo d.hhi
    d.x d.hr d.hb0 d.hb1 t).differentiable (by norm_num)
  have hY := (contDiff_one_backwardProbabilityTransport d.hF d.hell d.hlo d.hhi
    d.x d.hr d.hb0 d.hb1 t).differentiable (by norm_num)
  have hTY : (T : Space D → Space D) ∘ Y = id := funext fun z =>
    forward_backwardProbabilityTransport d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 t z
  have hYT : (Y : Space D → Space D) ∘ T = id := funext fun z =>
    backward_forwardProbabilityTransport d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 t z
  have hleft := ((hY (T (Y y))).hasFDerivAt.comp (Y y) (hT (Y y)).hasFDerivAt).fderiv
  have hright := ((hT (Y y)).hasFDerivAt.comp y (hY y).hasFDerivAt).fderiv
  rw [hYT, fderiv_id] at hleft
  rw [hTY, fderiv_id] at hright
  have hcancel : T (Y y) = y :=
    forward_backwardProbabilityTransport d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 t y
  rw [hcancel] at hleft
  exact ⟨hleft.symm, hright.symm⟩

/-- This unit is constructed from the just-proved original-data identities. -/
def actualJUnit (d : PositiveVarianceFlowData (Space D)) (t : ℝ) (y : Space D) :
    (Space D →L[ℝ] Space D)ˣ where
  val := actualJ d t y
  inv := actualB d t y
  val_inv := (original_data_inverse_pair d t y).1
  inv_val := (original_data_inverse_pair d t y).2

theorem actualB_eq_ringInverse (d : PositiveVarianceFlowData (Space D)) (t : ℝ) :
    actualB d t = Ring.inverse ∘ actualJ d t := by
  funext y
  exact (Ring.inverse_unit (actualJUnit d t y)).symm

theorem original_data_J_smooth (d : PositiveVarianceFlowData (Space D))
    (hsmall : d.r^2*d.ell ≤ 1/2) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    ContDiff ℝ ∞ (actualJ d t) :=
  (contDiff_backward_spatial d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1
    hsmall ht).fderiv_right (by simp)

theorem original_data_B_smooth (d : PositiveVarianceFlowData (Space D))
    (hsmall : d.r^2*d.ell ≤ 1/2) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    ContDiff ℝ ∞ (actualB d t) := by
  rw [actualB_eq_ringInverse]
  exact contDiff_iff_contDiffAt.mpr fun y =>
    (contDiffAt_ringInverse ℝ (actualJUnit d t y)).comp y
      (original_data_J_smooth d hsmall ht).contDiffAt

abbrev actualBTimeRHS (d : PositiveVarianceFlowData (Space D)) (y : Space D) (t : ℝ) :=
  (d.r*t) • (actualB d t y).comp (firstScaledJet d.F d.x d.r t (actualY d t y))

theorem original_data_B_time_derivative (d : PositiveVarianceFlowData (Space D))
    (y : Space D) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    HasDerivWithinAt (fun s => actualB d s y) (actualBTimeRHS d y t) (Icc 0 d.b) t :=
  transportedJacobian_deriv d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 ht y

/-- Sharp Q0 clock, from the original time ODE, not the coarser source e bound.
No division by t, ell, b, or the clock. -/
theorem original_data_B_norm (d : PositiveVarianceFlowData (Space D))
    (y : Space D) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    ‖actualB d t y‖ ≤ Real.exp (flowClock d t) := by
  have h := backward_homogeneous_bound (flowAlpha_nonneg d)
    (continuousOn_transportedJacobian d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 y)
    (fun s hs => original_data_B_time_derivative d y hs)
    (δ := 1) (α := flowAlpha d)
    (by
      rw [transportedJacobian_terminal]
      apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      intro z
      simp)
    (fun s hs => by
      have hU := norm_firstScaledJet_le d.hF d.hell d.hlo d.hhi d.x d.hr
        (by linarith [hs.1]) (hs.2.trans_lt d.hb1) (actualY d s y)
      change ‖(d.r*s) • (actualB d s y).comp
        (firstScaledJet d.F d.x d.r s (actualY d s y))‖ ≤ _
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg d.hr.le hs.1)]
      calc
        _ ≤ (d.r*s)*(‖actualB d s y‖ *
            ‖firstScaledJet d.F d.x d.r s (actualY d s y)‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
            (mul_nonneg d.hr.le hs.1)
        _ ≤ (d.r*s)*(‖actualB d s y‖ * (d.r*d.ell)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hU (norm_nonneg _))
            (mul_nonneg d.hr.le hs.1)
        _ = _ := by dsimp [flowAlpha]; ring) ht
  simpa only [one_mul,flowClock] using h

/-- Q0 has exactly two ordinary slots, and no derivative slot. -/
def zeroOperatorChart : (Fin 1 ⊕ Unit) ≃ ((Fin 0 ⊕ Unit) ⊕ Unit) where
  toFun := fun a => match a with
    | .inl _ => .inl (.inr ())
    | .inr _ => .inr ()
  invFun := fun a => match a with
    | .inl (.inl j) => Fin.elim0 j
    | .inl (.inr _) => .inl 0
    | .inr _ => .inr ()
  left_inv := by intro a; fin_cases a <;> rfl
  right_inv := by
    intro a
    rcases a with (j | u) | u
    · exact Fin.elim0 j
    · cases u; rfl
    · cases u; rfl

def inverseJetCoeff (d : PositiveVarianceFlowData (Space D)) (n : ℕ)
    (t : ℝ) (y : Space D) := operatorCoeff (iteratedFDeriv ℝ n (actualB d t) y)

theorem inverseJetCoeff_zero (d : PositiveVarianceFlowData (Space D)) (t : ℝ) (y : Space D) :
    inverseJetCoeff d 0 t y = relabel D zeroOperatorChart (rankTwoCoeff (actualB d t y)) := by
  ext a
  simp [inverseJetCoeff,operatorCoeff,relabel,rankTwoCoeff,zeroOperatorChart]

/-- BOTH proper cuts, not just the matrix/output-row cut. -/
theorem original_data_inverse_zero_allProper (d : PositiveVarianceFlowData (Space D))
    (y : Space D) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    AllProper D (inverseJetCoeff d 0 t y) (Real.exp (flowClock d t)) := by
  rw [inverseJetCoeff_zero]
  apply EdgeClosure.AllProper.relabel (e := zeroOperatorChart)
  intro S hS
  exact (rankTwo_splitNorm_le (actualB d t y) S hS).trans (original_data_B_norm d y ht)

theorem original_data_inverse_zero_relabel {A : Type*} [Fintype A] [DecidableEq A]
    (d : PositiveVarianceFlowData (Space D)) (e : ((Fin 0 ⊕ Unit) ⊕ Unit) ≃ A)
    (y : Space D) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    AllProper D (relabel D e (inverseJetCoeff d 0 t y)) (Real.exp (flowClock d t)) :=
  (original_data_inverse_zero_allProper d y ht).relabel e
end AcceleratedLogConcave.Tensor.InverseFlow
