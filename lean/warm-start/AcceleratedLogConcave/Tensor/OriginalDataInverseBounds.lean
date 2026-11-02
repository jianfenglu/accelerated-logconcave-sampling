import AcceleratedLogConcave.Tensor.OriginalDataInverseRecurrence
import AcceleratedLogConcave.Tensor.OriginalDataJacobianCuts
import AcceleratedLogConcave.Tensor.InverseOrderConstants

/-!

-/
noncomputable section
set_option autoImplicit false
open Set Function
open scoped Classical BigOperators
namespace AcceleratedLogConcave.Tensor.InverseFlow
open Conditional Conditional.Transport.SpatialFlow
open ActualCoefficient EdgeClosure FlowInduction
open LabeledOperatorLeibniz hiding Space basis
variable {D : ℕ}

/-- Original B, with the rank-two slot convention required by the path supplier. -/
theorem original_data_B_rankTwo_allProper
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (y : Space D) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    AllProper D (rankTwoCoeff (actualB d t y)) growthConstant := by
  intro S hS
  exact (rankTwo_splitNorm_le (actualB d t y) S hS).trans
    ((original_data_B_norm d y ht).trans
      (Real.exp_le_exp.mpr (flowClock_bounds d hsmall ht).2))

/-- Local induction step. Lower-order premises here are discharged by strong
induction below, and do not appear in the public original-data theorem. -/
theorem inverse_step_from_lower_orders
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (n : ℕ) (hn : 0 < n) (y : Space D) {t : ℝ} (ht : t ∈ Icc 0 d.b)
    (hbranch : ∀ s, s < n → AllProper D (inverseJetCoeff d s t y)
      (flowScale d^s * inverseOrderConstant s)) :
    AllProper D (inverseJetCoeff d n t y)
      (flowClock d t * flowScale d^n * inverseOrderConstant n) := by
  let A := flowClock d t
  let H := flowScale d
  let E := growthConstant
  have hA : 0 ≤ A := (flowClock_bounds d hsmall ht).1
  have hH : 0 ≤ H := flowScale_nonneg d
  have hE : 0 ≤ E := (Real.exp_pos _).le
  let weight : Finset (Fin n) → ℝ := fun S =>
    A*H^n*(inverseOrderConstant S.card * orderConstant (n-S.card+1) * E)
  have hterms (S : Finset (Fin n)) (hS : S ∈ properSubsets n) :
      AllProper D (inverseSubsetCoeff d n t y S) (weight S) := by
    let s := leftCount ((subsetEquiv n).symm S)
    let k := rightCount ((subsetEquiv n).symm S)
    have hs : s < n := properSubset_left_lt hS
    have hk : 0 < k := properSubset_right_pos hS
    have hsc : s = S.card := subset_leftCount S
    have hkc : k = n-S.card := subset_rightCount S
    have hL : AllProper D (operatorCoeff (iteratedFDeriv ℝ s (actualB d t) y))
        (H^s * inverseOrderConstant s) := hbranch s hs
    have hM : AllProper D (operatorCoeff (iteratedFDeriv ℝ k (actualJ d t) y))
        (A*H^k*orderConstant (k+1)) := by
      simpa only [flowBudget,ite_eq_right (show k+1 ≠ 1 by omega),Nat.add_sub_cancel]
        using original_data_J_jet_allProper d hsmall k y ht
    have hc := (threeFactorCoeff_allProper
      (iteratedFDeriv ℝ s (actualB d t) y)
      (iteratedFDeriv ℝ k (actualJ d t) y) (actualB d t y)
      (mul_nonneg (pow_nonneg hH _) (inverseOrderConstant_nonneg s))
      (mul_nonneg (mul_nonneg hA (pow_nonneg hH _)) (orderConstant_nonneg _))
      hE hL hM (original_data_B_rankTwo_allProper d hsmall y ht)).relabel
        (inverseSubsetChart S)
    have hw : ((H^s*inverseOrderConstant s)*(A*H^k*orderConstant (k+1)))*E =
        weight S := by
      change ((H^s*inverseOrderConstant s)*(A*H^k*orderConstant (k+1)))*E =
        A*H^n*(inverseOrderConstant S.card * orderConstant (n-S.card+1) * E)
      rw [hsc,hkc]
      exact inverse_weight A H (inverseOrderConstant S.card)
        (orderConstant (n-S.card+1)) E (Nat.le_of_lt (properSubset_card_lt hS))
    rw [hw] at hc
    exact hc
  have hsum := inverse_coefficient_sum_allProper (inverseSubsetCoeff d n t y) weight hterms
  have hw : (∑ S ∈ properSubsets n, weight S) = A*H^n*inverseOrderConstant n := by
    dsimp [weight]
    rw [← Finset.mul_sum, properSubset_sum_card n
      (fun s => inverseOrderConstant s * orderConstant (n-s+1) * E)]
    rw [inverseOrderConstant_recurrence hn]
    congr 1
    calc
      (∑ s ∈ Finset.range n,
        (n.choose s : ℝ)*(inverseOrderConstant s*orderConstant (n-s+1)*E)) =
          E * ∑ s ∈ Finset.range n,
            (n.choose s : ℝ)*inverseOrderConstant s*orderConstant (n-s+1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        ring
      _ = _ := rfl
  rw [hw] at hsum
  rw [original_data_inverse_coefficient_sum d hsmall ht n hn]
  exact hsum

/-- Positive inverse-jet theorem with no recurrence, cut supplier, derivative
identity, lower-jet or desired Q bound among its hypotheses. The small clock is
retained for every n>=1. This is SOURCE ONLY until independent elaboration. -/
theorem original_data_positive_inverse_allProper
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (n : ℕ) (hn : 0 < n) (y : Space D) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    AllProper D (inverseJetCoeff d n t y)
      (flowClock d t * flowScale d^n * inverseOrderConstant n) := by
  suffices hall : ∀ m, 0 < m → AllProper D (inverseJetCoeff d m t y)
      (flowClock d t * flowScale d^m * inverseOrderConstant m) from hall n hn
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm
    apply inverse_step_from_lower_orders d hsmall m hm y ht
    intro s hs S hS
    by_cases hs0 : s = 0
    · subst s
      have hzero := original_data_inverse_zero_allProper d y ht S hS
      have he : Real.exp (flowClock d t) ≤ growthConstant :=
        Real.exp_le_exp.mpr (flowClock_bounds d hsmall ht).2
      simpa only [pow_zero,one_mul,inverseOrderConstant_zero] using hzero.trans he
    · have hpos := ih s hs (Nat.pos_of_ne_zero hs0) S hS
      have hweight : 0 ≤ flowScale d^s * inverseOrderConstant s :=
        mul_nonneg (pow_nonneg (flowScale_nonneg d) _) (inverseOrderConstant_nonneg s)
      calc
        _ ≤ flowClock d t * flowScale d^s * inverseOrderConstant s := hpos
        _ = flowClock d t * (flowScale d^s * inverseOrderConstant s) := mul_assoc _ _ _
        _ ≤ 1 * (flowScale d^s * inverseOrderConstant s) :=
          mul_le_mul_of_nonneg_right
            ((flowClock_bounds d hsmall ht).2.trans (by norm_num)) hweight
        _ = _ := one_mul _

/-- Piecewise Q budget: Q0 keeps exp(A), unlike the coarsened induction budget. -/
def inverseBudget (d : PositiveVarianceFlowData (Space D)) (n : ℕ) (t : ℝ) : ℝ :=
  if n = 0 then Real.exp (flowClock d t)
  else flowClock d t*flowScale d^n*inverseOrderConstant n

 theorem original_data_inverse_allProper
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (n : ℕ) (y : Space D) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    AllProper D (inverseJetCoeff d n t y) (inverseBudget d n t) := by
  by_cases hn : n = 0
  · subst n
    simpa [inverseBudget] using original_data_inverse_zero_allProper d y ht
  · simpa [inverseBudget, hn] using
      original_data_positive_inverse_allProper d hsmall n (Nat.pos_of_ne_zero hn) y ht

/-- Any output placement and any proper cut, transported by a literal bijection. -/
theorem original_data_inverse_relabel {X : Type*} [Fintype X] [DecidableEq X]
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (n : ℕ) (e : ((Fin n ⊕ Unit) ⊕ Unit) ≃ X)
    (y : Space D) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    AllProper D (relabel D e (inverseJetCoeff d n t y)) (inverseBudget d n t) :=
  (original_data_inverse_allProper d hsmall n y ht).relabel e

 theorem positive_inverse_cut_zero_of_curvature_zero
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (hell : d.ell = 0) (n : ℕ) (hn : 0 < n) (y : Space D)
    (S : Finset ((Fin n ⊕ Unit) ⊕ Unit)) (hS : NontrivialSplit S)
    {t : ℝ} (ht : t ∈ Icc 0 d.b) : splitNorm D S (inverseJetCoeff d n t y) = 0 := by
  apply le_antisymm _ (splitNorm_nonneg D S _)
  simpa [flowClock,flowAlpha,hell] using
    original_data_positive_inverse_allProper d hsmall n hn y ht S hS

 theorem positive_inverse_cut_zero_of_terminal_zero
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (hb : d.b = 0) (n : ℕ) (hn : 0 < n) (y : Space D)
    (S : Finset ((Fin n ⊕ Unit) ⊕ Unit)) (hS : NontrivialSplit S)
    {t : ℝ} (ht : t ∈ Icc 0 d.b) : splitNorm D S (inverseJetCoeff d n t y) = 0 := by
  have ht0 : t = 0 := le_antisymm (ht.2.trans_eq hb) ht.1
  apply le_antisymm _ (splitNorm_nonneg D S _)
  simpa [flowClock,hb,ht0] using
    original_data_positive_inverse_allProper d hsmall n hn y ht S hS

 theorem inverse_cut_dimension_zero
    (d : PositiveVarianceFlowData (Space 0)) (n : ℕ) (t : ℝ) (y : Space 0)
    (S : Finset ((Fin n ⊕ Unit) ⊕ Unit)) : splitNorm 0 S (inverseJetCoeff d n t y) = 0 := by
  rw [inverseJetCoeff_dimension_zero,splitNorm_zero]

end AcceleratedLogConcave.Tensor.InverseFlow
