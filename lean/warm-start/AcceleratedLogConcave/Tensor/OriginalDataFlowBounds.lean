import AcceleratedLogConcave.Tensor.FlowOrderConstants
import AcceleratedLogConcave.Tensor.ActualFlowComparisonSpecializations
import AcceleratedLogConcave.Tensor.PrimitiveFlowCuts
import AcceleratedLogConcave.Tensor.ActualTerminalCuts

/-!

-/
noncomputable section
set_option autoImplicit false
open Set
open scoped BigOperators Classical
namespace AcceleratedLogConcave.Tensor.FlowInduction
open Conditional Conditional.Transport.SpatialFlow
open EdgeClosure ActualCoefficient ActualPartitionTree
open AcceleratedLogConcave.Analysis.SpatialPartition
variable {D : ℕ}

def flowAlpha (d : PositiveVarianceFlowData (Space D)) : ℝ := d.r^2*d.ell
def flowScale (d : PositiveVarianceFlowData (Space D)) : ℝ := d.b/Real.sqrt (1-d.b^2)
def flowClock (d : PositiveVarianceFlowData (Space D)) (t : ℝ) : ℝ :=
  flowAlpha d * (d.b^2-t^2)/2

 theorem flowAlpha_nonneg (d : PositiveVarianceFlowData (Space D)) : 0 ≤ flowAlpha d :=
  mul_nonneg (sq_nonneg _) d.hell
 theorem flowScale_nonneg (d : PositiveVarianceFlowData (Space D)) : 0 ≤ flowScale d :=
  div_nonneg d.hb0 (Real.sqrt_nonneg _)
 theorem flowClock_bounds (d : PositiveVarianceFlowData (Space D))
    (hsmall : d.r^2*d.ell ≤ 1/2) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    0 ≤ flowClock d t ∧ flowClock d t ≤ 1/4 := by
  have ha := flowAlpha_nonneg d
  have hd : 0 ≤ d.b^2-t^2 := by nlinarith [ht.1,ht.2]
  have hd' : d.b^2-t^2 ≤ 1 := by nlinarith [d.hb0,d.hb1,sq_nonneg t]
  have hm := mul_le_mul hsmall hd' hd (by norm_num : (0:ℝ) ≤ 1/2)
  constructor
  · exact div_nonneg (mul_nonneg ha hd) (by norm_num)
  · change (d.r^2*d.ell)*(d.b^2-t^2)/2 ≤ 1/4
    nlinarith

/-- First order, sharpened to the actual variable-coefficient exponential. -/
 theorem original_data_first_flow_allProper
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (y : Space D) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    AllProper D (actualJetCoeff d 1 y t) (Real.exp (flowClock d t)) := by
  intro S hS
  exact actual_first_cut_homogeneous d hsmall y S (flowAlpha_nonneg d)
    (actualJetCoeff_terminal_one_le d y S hS)
    (fun s hs => norm_fderiv_probabilityVelocity_le d (actualY d s y) hs) ht

/-- The induction closes on the literal ordered-partition forcing, retaining
all labeled multiplicities. This local helper's branch premise is discharged
by strong induction in original_data_higher_flow_allProper below. -/
 theorem forcing_from_lower_orders
    (d : PositiveVarianceFlowData (Space D)) (n : ℕ) (hn : 0 < n)
    (y : Space D) {s : ℝ} (hs : s ∈ Icc 0 d.b)
    (hbranch : ∀ j, 1 ≤ j → j < n →
      AllProper D (actualJetCoeff d j y s)
        (flowScale d^(j-1)*orderConstant j)) :
    AllProper D (actualForcingCoeff d n hn y s)
      (flowAlpha d*s*(flowScale d^(n-1)*forcingConstant n hn)) := by
  have h := actual_forcing_allProper d n hn s y
    (fun k => flowAlpha d*s*primitiveConstant k*flowScale d^(k-1))
    (fun j => flowScale d^(j-1)*orderConstant j)
    (fun k => mul_nonneg
      (mul_nonneg (mul_nonneg (flowAlpha_nonneg d) hs.1) (primitiveConstant_nonneg k))
      (pow_nonneg (flowScale_nonneg d) _))
    (fun j => mul_nonneg (pow_nonneg (flowScale_nonneg d) _) (orderConstant_nonneg j))
    (fun k hk _ => probabilityVelocity_allProper_ge_two d k hk (actualY d s y) hs)
    hbranch
  rw [show (∑ c ∈ (Finset.univ : Finset (OrderedFinpartition n)).erase
      (OrderedFinpartition.oneBlock n hn),
      (flowAlpha d*s*primitiveConstant c.length*flowScale d^(c.length-1)) *
        ∏ i, flowScale d^(c.partSize i-1)*orderConstant (c.partSize i)) =
      flowAlpha d*s*flowScale d^(n-1)*forcingConstant n hn from
        forcing_weight n hn (flowAlpha d) s (flowScale d)] at h
  simpa only [mul_assoc] using h

/-- Genuine strong induction from original data. No norm-budget, integrability,
Volterra, forcing, or primitive-cut assumptions remain in the statement. -/
 theorem original_data_higher_flow_allProper
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (n : ℕ) (hn : 2 ≤ n) (y : Space D) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    AllProper D (actualJetCoeff d n y t)
      (flowClock d t * flowScale d^(n-1)*orderConstant n) := by
  suffices hall : ∀ m, 2 ≤ m → ∀ z : Space D, ∀ u : ℝ, u ∈ Icc 0 d.b →
      AllProper D (actualJetCoeff d m z u)
        (flowClock d u * flowScale d^(m-1)*orderConstant m) from hall n hn y t ht
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn y t ht
    have hforce (s : ℝ) (hs : s ∈ Icc 0 d.b) :
        AllProper D (actualForcingCoeff d n (by omega) y s)
          (flowAlpha d*s*(flowScale d^(n-1)*forcingConstant n (by omega))) := by
      apply forcing_from_lower_orders d n (by omega) y hs
      intro j hj hjn S hS
      by_cases hj1 : j = 1
      · subst j
        have hfirst := original_data_first_flow_allProper d hsmall y hs S hS
        have he : Real.exp (flowClock d s) ≤ growthConstant :=
          Real.exp_le_exp.mpr (flowClock_bounds d hsmall hs).2
        simpa [orderConstant_small (show 1 < 2 by omega)] using hfirst.trans he
      · have hj2 : 2 ≤ j := by omega
        have hl := ih j hjn hj2 y s hs S hS
        have hc := flowClock_bounds d hsmall hs
        have hweight : 0 ≤ flowScale d^(j-1)*orderConstant j :=
          mul_nonneg (pow_nonneg (flowScale_nonneg d) _) (orderConstant_nonneg j)
        calc
          _ ≤ flowClock d s * flowScale d^(j-1)*orderConstant j := hl
          _ = flowClock d s * (flowScale d^(j-1)*orderConstant j) := mul_assoc _ _ _
          _ ≤ 1 * (flowScale d^(j-1)*orderConstant j) :=
            mul_le_mul_of_nonneg_right (hc.2.trans (by norm_num)) hweight
          _ = _ := one_mul _
    intro S hS
    have hb := actualJetCoeff_terminal_ge_two_eq_zero d n hn y S
    have hcomparison := actual_cut_proportional d hsmall n (by omega) y S
      (flowAlpha_nonneg d) hb
      (fun s hs => norm_fderiv_probabilityVelocity_le d (actualY d s y) hs)
      (fun s hs => hforce s hs S hS) ht
    have hw : 0 ≤ flowScale d^(n-1)*forcingConstant n (by omega) :=
      mul_nonneg (pow_nonneg (flowScale_nonneg d) _) (forcingConstant_nonneg _ _)
    have hc := flowClock_bounds d hsmall ht
    calc
      _ ≤ (flowScale d^(n-1)*forcingConstant n (by omega)) *
          (Real.exp (flowClock d t)-1) := hcomparison
      _ ≤ (flowScale d^(n-1)*forcingConstant n (by omega)) *
          (flowClock d t*growthConstant) :=
        mul_le_mul_of_nonneg_left (exp_sub_one_le hc.1 hc.2) hw
      _ = flowClock d t*flowScale d^(n-1)*orderConstant n := by
        rw [orderConstant_recurrence hn]
        ring

/-- A single positive-order P_n with the retained small clock at n>=2. -/
def flowBudget (d : PositiveVarianceFlowData (Space D)) (n : ℕ) (t : ℝ) : ℝ :=
  if n = 1 then Real.exp (flowClock d t)
  else flowClock d t*flowScale d^(n-1)*orderConstant n

 theorem original_data_flow_allProper
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (n : ℕ) (hn : 0 < n) (y : Space D) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    AllProper D (actualJetCoeff d n y t) (flowBudget d n t) := by
  by_cases hn1 : n = 1
  · subst n
    simpa [flowBudget] using original_data_first_flow_allProper d hsmall y ht
  · simpa [flowBudget, hn1] using
      original_data_higher_flow_allProper d hsmall n (by omega) y ht

/-- Scalar forcing envelopes are globally continuous, including alpha=0 and H=0. -/
 theorem continuous_scalar_forcing (d : PositiveVarianceFlowData (Space D))
    (n : ℕ) (hn : 0 < n) :
    Continuous (fun s : ℝ => flowAlpha d*s*(flowScale d^(n-1)*forcingConstant n hn)) :=
  (continuous_const.mul continuous_id).mul continuous_const

/-- Curvature zero is covered without dividing by alpha or ell. -/
 theorem higher_flow_cut_zero_of_curvature_zero
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (hell : d.ell = 0) (n : ℕ) (hn : 2 ≤ n) (y : Space D)
    (S : Finset (Fin n ⊕ Unit)) (hS : NontrivialSplit S)
    {t : ℝ} (ht : t ∈ Icc 0 d.b) : splitNorm D S (actualJetCoeff d n y t) = 0 := by
  apply le_antisymm _ (splitNorm_nonneg D S _)
  simpa [flowClock,flowAlpha,hell] using
    original_data_higher_flow_allProper d hsmall n hn y ht S hS

/-- Singleton slab is covered without division by b or by flowScale. -/
 theorem higher_flow_cut_zero_of_terminal_zero
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (hb : d.b = 0) (n : ℕ) (hn : 2 ≤ n) (y : Space D)
    (S : Finset (Fin n ⊕ Unit)) (hS : NontrivialSplit S)
    {t : ℝ} (ht : t ∈ Icc 0 d.b) : splitNorm D S (actualJetCoeff d n y t) = 0 := by
  have ht0 : t = 0 := le_antisymm (ht.2.trans_eq hb) ht.1
  apply le_antisymm _ (splitNorm_nonneg D S _)
  simpa [flowClock,hb,ht0] using
    original_data_higher_flow_allProper d hsmall n hn y ht S hS

/-- Empty coordinate dimension is zero at every time, independently of estimates. -/
 theorem flow_cut_dim_zero (d : PositiveVarianceFlowData (Space 0))
    (n : ℕ) (y : Space 0) (t : ℝ) (S : Finset (Fin n ⊕ Unit)) :
    splitNorm 0 S (actualJetCoeff d n y t) = 0 := by
  have hz : actualJetCoeff d n y t = 0 := by
    ext a
    exact Fin.elim0 (a (.inr ()))
  rw [hz,splitNorm_zero]

end AcceleratedLogConcave.Tensor.FlowInduction
