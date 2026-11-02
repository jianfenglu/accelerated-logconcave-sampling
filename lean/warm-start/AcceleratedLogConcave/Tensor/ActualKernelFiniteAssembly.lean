import AcceleratedLogConcave.Tensor.ActualFirstJetSupplier
import AcceleratedLogConcave.Tensor.ActualCompositionBudget
import AcceleratedLogConcave.Tensor.InverseSubsetLabels
import AcceleratedLogConcave.Conditional.Transport.ActualBackwardSpatialVariations
import AcceleratedLogConcave.Tensor.LegacyNumericalBudgets
import AcceleratedLogConcave.Conditional.Stein.SpatialJacobianExtension

/-!
SOURCE-ONLY SECOND BATCH. No compilation or transitive axiom audit has run.
This module assembles the literal kernel from genuine actual-flow and
actual-inverse derivative bounds. It proves neither of those two premises.
There is no kernel bound, composite-jet bound, recurrence, or domination oracle
in the public final implication. The reviewed first batch remains unchanged.
-/
noncomputable section
set_option autoImplicit false
open Set Function
open scoped Classical BigOperators ContDiff
namespace AcceleratedLogConcave.Tensor.QuantitativeKernel.KernelFiniteAssembly
open Conditional Conditional.Transport
open ActualCoefficient ActualPartitionTree
open LabeledOperatorLeibniz
open LegacyNumericalBudgets LegacyOrderConstantBridge
open AcceleratedLogConcave.Analysis.SpatialPartition

variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)

/-- Monotonicity changes only the scalar, never the tensor or retained cut. -/
theorem budget_mono {X : Type*} [Fintype X] [DecidableEq X]
    {T : Coeff X D} {a b : ℝ} (hT : QuantitativeKernel.AllProper D T a)
    (hab : a ≤ b) : QuantitativeKernel.AllProper D T b :=
  fun S hS => (hT S hS).trans hab

/-- The exact clock bound includes both endpoints and zero curvature. -/
theorem kernelClock_bounds (d : PositiveVarianceFlowData E)
    (hsmall : d.r^2*d.ell ≤ 1/2) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    0 ≤ curvatureTime d.r d.ell d.b t ∧
      curvatureTime d.r d.ell d.b t ≤ 1/4 := by
  have ha : 0 ≤ d.r^2*d.ell := mul_nonneg (sq_nonneg _) d.hell
  have hd : 0 ≤ d.b^2-t^2 := by nlinarith [ht.1,ht.2]
  have hd' : d.b^2-t^2 ≤ 1 := by nlinarith [d.hb0,d.hb1,sq_nonneg t]
  have hm := mul_le_mul hsmall hd' hd (by norm_num : (0:ℝ) ≤ 1/2)
  constructor
  · exact div_nonneg (mul_nonneg ha hd) (by norm_num)
  · unfold curvatureTime
    nlinarith

/-- Literal change between the two retained operator-slot conventions. -/
theorem operatorCoeff_to_legacy (n : ℕ) (f : E → E →L[ℝ] E) (y : E) :
    EdgeClosure.relabel D (Equiv.sumAssoc (Fin n) Unit Unit)
      (operatorCoeff (iteratedFDeriv ℝ n f y)) = operatorJetCoeff n f y := by
  ext a
  rfl

/-- The inverse chart also preserves all derivative, input, and output slots. -/
theorem legacy_to_operatorCoeff (n : ℕ) (f : E → E →L[ℝ] E) (y : E) :
    EdgeClosure.relabel D (Equiv.sumAssoc (Fin n) Unit Unit).symm
      (operatorJetCoeff n f y) = operatorCoeff (iteratedFDeriv ℝ n f y) := by
  ext a
  rfl

/-- A positive Y branch may lose its clock for composition, but not its scale.
The exceptional first branch uses exp(clock) <= flowConstant(1). -/
theorem actualY_coarse_allProper (hFlow : ActualFlowBudgetStatement)
    (d : PositiveVarianceFlowData E) (hsmall : d.r^2*d.ell ≤ 1/2)
    {t : ℝ} (ht : t ∈ Icc 0 d.b) (y : E) (q : ℕ) (hq : 0 < q) :
    QuantitativeKernel.AllProper D (vectorJetCoeff q (actualY d t) y)
      (spatialScale d.b^(q-1)*flowConstant q) := by
  have hclock := kernelClock_bounds d hsmall ht
  have hscale : 0 ≤ spatialScale d.b := div_nonneg d.hb0 (Real.sqrt_nonneg _)
  by_cases hq1 : q = 1
  · subst q
    have h := budget_mono (hFlow D d hsmall t ht y).1
      (Real.exp_le_exp.mpr hclock.2)
    simpa only [Nat.sub_self,pow_zero,one_mul,flowConstant_one,universalExp] using h
  · apply budget_mono ((hFlow D d hsmall t ht y).2 q (by omega))
    calc
      _ ≤ 1 * spatialScale d.b^(q-1) * flowConstant q :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hclock.2.trans (by norm_num))
            (pow_nonneg hscale _)) (flowConstant_nonneg q)
      _ = _ := by ring

/-- No positivity of the scale is needed for the exact partition power count. -/
theorem composition_partition_weight {n : ℕ} (c : OrderedFinpartition n)
    (beta eta : ℝ) :
    (beta*primitiveConstant (c.length+1)*eta^c.length) *
      (∏ i, eta^(c.partSize i-1)*flowConstant (c.partSize i)) =
    beta*eta^n * (primitiveConstant (c.length+1)*∏ i, flowConstant (c.partSize i)) := by
  have hp : (∑ i, (c.partSize i-1)) + c.length = n := by
    have h : ∑ i, ((c.partSize i-1)+1) = n := by
      calc
        _ = ∑ i, c.partSize i := Finset.sum_congr rfl
          (fun i _ => Nat.sub_add_cancel (c.partSize_pos i))
        _ = n := OrderedFinpartition.sum_partSize c
    simpa [Finset.sum_add_distrib] using h
  rw [Finset.prod_mul_distrib,FlowInduction.prod_powers]
  calc
    _ = beta*(eta^c.length*eta^(∑ i, (c.partSize i-1))) *
        (primitiveConstant (c.length+1)*∏ i, flowConstant (c.partSize i)) := by ring
    _ = _ := by rw [← pow_add,show c.length+(∑ i, (c.partSize i-1)) = n by omega]

/-- The actual U1(Y) operator, rather than a postulated composite jet. -/
def actualH (d : PositiveVarianceFlowData E) (t : ℝ) : E → E →L[ℝ] E :=
  firstScaledJet d.F d.x d.r t ∘ actualY d t

/-- Spatial regularity of U1 uses the already dominated posterior expectation. -/
theorem firstScaledJet_contDiff (d : PositiveVarianceFlowData E)
    {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    ContDiff ℝ ∞ (firstScaledJet d.F d.x d.r t) :=
  (contDiffOn_firstScaledJet d.hF d.hlo d.hhi d.x d.r).comp_contDiff
    (contDiff_const.prodMk contDiff_id)
    (fun _ => ⟨by linarith [ht.1],ht.2.trans_lt d.hb1⟩)

/-- Composition is smooth from original regularity, not quantitative jet data. -/
theorem actualH_contDiff (d : PositiveVarianceFlowData E)
    (hsmall : d.r^2*d.ell ≤ 1/2) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    ContDiff ℝ ∞ (actualH d t) :=
  (firstScaledJet_contDiff d ht).comp
    (SpatialFlow.contDiff_backward_spatial d.hF d.hell d.hlo d.hhi
      d.x d.hr d.hb0 d.hb1 hsmall ht)

/-- Every labeled partition is assembled with the original U1 root supplier
and genuine actual Y branches. The n=0 bound is sharp, not the loose factorial
root; in particular this theorem also covers eta=0 and D=0. -/
theorem actualH_allProper (hFlow : ActualFlowBudgetStatement)
    (d : PositiveVarianceFlowData E) (hsmall : d.r^2*d.ell ≤ 1/2)
    {t : ℝ} (ht : t ∈ Icc 0 d.b) (n : ℕ) (y : E) :
    QuantitativeKernel.AllProper D (operatorJetCoeff n (actualH d t) y)
      ((d.r*d.ell)*spatialScale d.b^n*compositionConstant n) := by
  by_cases hn : n = 0
  · subst n
    have he : operatorJetCoeff 0 (actualH d t) y =
        operatorJetCoeff 0 (firstScaledJet d.F d.x d.r t) (actualY d t y) := by
      ext a
      rfl
    rw [he]
    simpa [compositionConstant] using
      firstScaledJet_operatorJetCoeff_zero d ht (actualY d t y)
  have hscale : 0 ≤ spatialScale d.b := div_nonneg d.hb0 (Real.sqrt_nonneg _)
  let CU : ℕ → ℝ := fun k => (d.r*d.ell)*primitiveConstant (k+1)*spatialScale d.b^k
  let CY : ℕ → ℝ := fun k => spatialScale d.b^(k-1)*flowConstant k
  have hCU (k : ℕ) : 0 ≤ CU k := by
    dsimp [CU]
    apply mul_nonneg (mul_nonneg (mul_nonneg d.hr.le d.hell) ?_) (pow_nonneg hscale k)
    unfold primitiveConstant
    split_ifs <;> positivity
  have hCY (k : ℕ) : 0 ≤ CY k :=
    mul_nonneg (pow_nonneg hscale _) (flowConstant_nonneg k)
  have hroot (c : OrderedFinpartition n) : EdgeClosure.AllProper D
      (operatorCoeff (iteratedFDeriv ℝ c.length
        (firstScaledJet d.F d.x d.r t) (actualY d t y))) (CU c.length) := by
    have h : EdgeClosure.AllProper D
        (operatorJetCoeff c.length (firstScaledJet d.F d.x d.r t) (actualY d t y))
        (CU c.length) := firstScaledJet_primitive_allProper d c.length ht (actualY d t y)
    have hc := h.relabel (Equiv.sumAssoc (Fin c.length) Unit Unit).symm
    rwa [legacy_to_operatorCoeff] at hc
  have hbranch (c : OrderedFinpartition n) (i : Fin c.length) : EdgeClosure.AllProper D
      (vectorCoeff (iteratedFDeriv ℝ (c.partSize i) (actualY d t) y)) (CY (c.partSize i)) :=
    actualY_coarse_allProper hFlow d hsmall ht y (c.partSize i) (c.partSize_pos i)
  have h := actual_composition_allProper
    (firstScaledJet d.F d.x d.r t) (actualY d t) y
    (firstScaledJet_contDiff d ht).contDiffAt
    (SpatialFlow.contDiff_backward_spatial d.hF d.hell d.hlo d.hhi
      d.x d.hr d.hb0 d.hb1 hsmall ht).contDiffAt CU CY hCU hCY hroot hbranch
  have hw : (∑ c : OrderedFinpartition n, CU c.length*∏ i, CY (c.partSize i)) =
      (d.r*d.ell)*spatialScale d.b^n*compositionConstant n := by
    dsimp [CU,CY]
    simp_rw [composition_partition_weight]
    rw [← Finset.mul_sum,compositionConstant,ite_eq_right hn]
  rw [hw] at h
  have hc := h.relabel (Equiv.sumAssoc (Fin n) Unit Unit)
  rwa [operatorCoeff_to_legacy] at hc

/-- One contracted edge deletes only the internal operator coordinate.
Both endpoint derivative groups and both external ordinary slots survive. -/
def productExternalChart (A B : Type*) :
    ((A ⊕ Unit) ⊕ (B ⊕ Unit)) ≃ ((A ⊕ B) ⊕ (Unit ⊕ Unit)) where
  toFun
    | .inl (.inl a) => .inl (.inl a)
    | .inl (.inr u) => .inr (.inr u)
    | .inr (.inl b) => .inl (.inr b)
    | .inr (.inr u) => .inr (.inl u)
  invFun
    | .inl (.inl a) => .inl (.inl a)
    | .inl (.inr b) => .inr (.inl b)
    | .inr (.inl u) => .inr (.inr u)
    | .inr (.inr u) => .inl (.inr u)
  left_inv := by intro s; rcases s with (a | u) | (b | u) <;> rfl
  right_inv := by intro s; rcases s with (a | b) | (u | u) <;> rfl

/-- The original increasing derivative labels are restored before summation. -/
def productSplitChart {n : ℕ} (s : Split n) :
    ((Fin (leftCount s) ⊕ Unit) ⊕ (Fin (rightCount s) ⊕ Unit)) ≃
      (Fin n ⊕ (Unit ⊕ Unit)) :=
  (productExternalChart _ _).trans
    (Equiv.sumCongr (InverseFlow.splitLabelEquiv s) (Equiv.refl _))

/-- Exact retained-coordinate Leibniz identity for actual operator products.
Repeated coordinate values are not quotiented; labels range over every split. -/
theorem operatorJetCoeff_product_sum (B H : E → E →L[ℝ] E)
    (hB : ContDiff ℝ ∞ B) (hH : ContDiff ℝ ∞ H) (n : ℕ) (y : E) :
    operatorJetCoeff n (fun z => (B z).comp (H z)) y =
      ∑ s : Split n, EdgeClosure.relabel D (productSplitChart s)
        (composeCoeff (iteratedFDeriv ℝ (leftCount s) B y)
          (iteratedFDeriv ℝ (rightCount s) H y)) := by
  ext a
  rw [coeff_finset_sum_apply]
  let L : (E →L[ℝ] E) →L[ℝ] ℝ :=
    (innerSL ℝ (basis D (a (.inr (.inr ()))))).comp
      (ContinuousLinearMap.apply ℝ E (basis D (a (.inr (.inl ())))))
  have he := congrArg L (iteratedFDeriv_comp_split B H hB hH n y
    (fun i => basis D (a (.inl i))))
  rw [map_sum] at he
  convert he using 1
  all_goals rfl

/-- Exact cardinality fibers of the full labeled subset family. -/
theorem subset_sum_card (n : ℕ) (f : ℕ → ℝ) :
    (∑ S : Finset (Fin n), f S.card) =
      ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ)*f j := by
  have hm : ∀ S ∈ (Finset.univ : Finset (Finset (Fin n))),
      S.card ∈ Finset.range (n+1) := by
    intro S _
    have h := Finset.card_le_card (Finset.subset_univ S)
    simp only [Finset.card_univ,Fintype.card_fin] at h
    exact Finset.mem_range.mpr (by omega)
  rw [← Finset.sum_fiberwise_of_maps_to' hm f]
  apply Finset.sum_congr rfl
  intro j _
  have hf : (Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card = j) =
      (Finset.univ : Finset (Fin n)).powersetCard j := by
    ext S
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_powersetCard]
    exact ⟨fun h => ⟨Finset.subset_univ S,h⟩,fun h => h.2⟩
  rw [hf]
  simp [Finset.card_powersetCard,nsmul_eq_mul]

/-- Genuine single-edge closure plus the labeled Leibniz formula, grouped by
cardinality only after every retained-coefficient term has been bounded. -/
theorem operator_product_allProper (B H : E → E →L[ℝ] E)
    (hB : ContDiff ℝ ∞ B) (hH : ContDiff ℝ ∞ H)
    (CB CH : ℕ → ℝ) (hCB : ∀ k, 0 ≤ CB k) (hCH : ∀ k, 0 ≤ CH k)
    (y : E)
    (hBj : ∀ k, QuantitativeKernel.AllProper D (operatorJetCoeff k B y) (CB k))
    (hHj : ∀ k, QuantitativeKernel.AllProper D (operatorJetCoeff k H y) (CH k))
    (n : ℕ) :
    QuantitativeKernel.AllProper D (operatorJetCoeff n (fun z => (B z).comp (H z)) y)
      (∑ j ∈ Finset.range (n+1), (n.choose j : ℝ)*CB j*CH (n-j)) := by
  rw [operatorJetCoeff_product_sum B H hB hH]
  have hb (k : ℕ) : EdgeClosure.AllProper D
      (operatorCoeff (iteratedFDeriv ℝ k B y)) (CB k) := by
    have h : EdgeClosure.AllProper D (operatorJetCoeff k B y) (CB k) := hBj k
    have hc := h.relabel (Equiv.sumAssoc (Fin k) Unit Unit).symm
    rwa [legacy_to_operatorCoeff] at hc
  have hh (k : ℕ) : EdgeClosure.AllProper D
      (operatorCoeff (iteratedFDeriv ℝ k H y)) (CH k) := by
    have h : EdgeClosure.AllProper D (operatorJetCoeff k H y) (CH k) := hHj k
    have hc := h.relabel (Equiv.sumAssoc (Fin k) Unit Unit).symm
    rwa [legacy_to_operatorCoeff] at hc
  have h := EdgeClosure.allProper_sum D
    (fun s : Split n => EdgeClosure.relabel D (productSplitChart s)
      (composeCoeff (iteratedFDeriv ℝ (leftCount s) B y)
        (iteratedFDeriv ℝ (rightCount s) H y)))
    (fun s => CB (leftCount s)*CH (rightCount s))
    (fun s => (composeCoeff_allProper _ _ (hCB _) (hCH _)
      (hb _) (hh _)).relabel (productSplitChart s))
  have hs : (∑ s : Split n, CB (leftCount s)*CH (rightCount s)) =
      ∑ S : Finset (Fin n), CB S.card*CH (n-S.card) := by
    calc
      _ = ∑ S : Finset (Fin n),
          CB (leftCount ((subsetEquiv n).symm S))*CH (rightCount ((subsetEquiv n).symm S)) :=
        ((subsetEquiv n).symm.sum_comp
          (fun s => CB (leftCount s)*CH (rightCount s))).symm
      _ = _ := by simp only [subset_leftCount,subset_rightCount]
  rw [hs,subset_sum_card n (fun j => CB j * CH (n-j))] at h
  simpa only [EdgeClosure.AllProper, QuantitativeKernel.AllProper, mul_assoc] using h

/-- Bound used for inverse factors only; the zeroth factor has no scale.
Positive-order factors retain eta^k and pay the actual small clock <= 1/4. -/
def kernelInverseWeight (eta : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then universalExp else (1/4)*eta^k*inverseConstant k

theorem kernelInverseWeight_nonneg {eta : ℝ} (heta : 0 ≤ eta) (k : ℕ) :
    0 ≤ kernelInverseWeight eta k := by
  unfold kernelInverseWeight
  split_ifs
  · exact universalExp_nonneg
  · exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg heta _))
      (inverseConstant_nonneg k)

theorem actualB_kernel_allProper (hInverse : ActualInverseBudgetStatement)
    (d : PositiveVarianceFlowData E) (hsmall : d.r^2*d.ell ≤ 1/2)
    {t : ℝ} (ht : t ∈ Icc 0 d.b) (y : E) (k : ℕ) :
    QuantitativeKernel.AllProper D (operatorJetCoeff k (actualB d t) y)
      (kernelInverseWeight (spatialScale d.b) k) := by
  have hc := kernelClock_bounds d hsmall ht
  unfold kernelInverseWeight
  split_ifs with hk
  · subst k
    exact budget_mono (hInverse D d hsmall t ht y).1 (Real.exp_le_exp.mpr hc.2)
  · apply budget_mono ((hInverse D d hsmall t ht y).2 k (by omega))
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc.2
        (pow_nonneg (div_nonneg d.hb0 (Real.sqrt_nonneg _)) _))
      (inverseConstant_nonneg k)

/-- Exact binomial convolution, with the zero-inverse term kept separately.
No cancellation of beta or eta is used, so both may vanish. -/
theorem kernel_convolution_weight (beta eta : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n+1),
      (n.choose j : ℝ)*kernelInverseWeight eta j*(beta*eta^(n-j)*compositionConstant (n-j))) =
    beta*eta^n*kernelConstant n := by
  rw [Finset.sum_range_succ']
  have hw (j : ℕ) (hj : j ∈ Finset.range n) :
      (n.choose (j+1) : ℝ)*kernelInverseWeight eta (j+1)*
        (beta*eta^(n-(j+1))*compositionConstant (n-(j+1))) =
      (beta*eta^n*(1/4))*
        ((n.choose (j+1) : ℝ)*inverseConstant (j+1)*compositionConstant (n-(j+1))) := by
    have hp : j+1+(n-(j+1)) = n := by have := Finset.mem_range.mp hj; omega
    simp only [kernelInverseWeight,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,ite_false]
    calc
      _ = (beta*(eta^(j+1)*eta^(n-(j+1)))*(1/4))*
          ((n.choose (j+1) : ℝ)*inverseConstant (j+1)*compositionConstant (n-(j+1))) := by ring
      _ = _ := by rw [← pow_add,hp]
  simp_rw [show kernelInverseWeight eta 0 = universalExp by simp [kernelInverseWeight]]
  rw [Finset.sum_congr rfl hw,← Finset.mul_sum]
  simp only [Nat.choose_zero_right,Nat.cast_one,one_mul,Nat.sub_zero]
  unfold kernelConstant
  ring

/-- The literal integrand bound, with both primitive and finite algebraic
joins discharged. Only actual flow/inverse derivative suppliers remain. -/
theorem actualKernelIntegrand_allProper
    (hFlow : ActualFlowBudgetStatement) (hInverse : ActualInverseBudgetStatement)
    (d : PositiveVarianceFlowData E) (hsmall : d.r^2*d.ell ≤ 1/2)
    {t : ℝ} (ht : t ∈ Icc 0 d.b) (n : ℕ) (y : E) :
    QuantitativeKernel.AllProper D (operatorJetCoeff n (actualKernelIntegrand d t) y)
      ((d.r*d.ell)*spatialScale d.b^n*kernelConstant n) := by
  have hs : 0 ≤ spatialScale d.b := div_nonneg d.hb0 (Real.sqrt_nonneg _)
  have h := operator_product_allProper (actualB d t) (actualH d t)
    (contDiff_infty_transportedJacobian_spatial d.hF d.hell d.hlo d.hhi
      d.x d.hr d.hb0 d.hb1 hsmall ht)
    (actualH_contDiff d hsmall ht)
    (kernelInverseWeight (spatialScale d.b))
    (fun k => (d.r*d.ell)*spatialScale d.b^k*compositionConstant k)
    (kernelInverseWeight_nonneg hs)
    (fun k => mul_nonneg (mul_nonneg (mul_nonneg d.hr.le d.hell) (pow_nonneg hs k))
      (compositionConstant_nonneg k)) y
    (actualB_kernel_allProper hInverse d hsmall ht y)
    (fun k => actualH_allProper hFlow d hsmall ht k y) n
  rw [kernel_convolution_weight] at h
  exact h

/-- The actual kernel analytic-budget implication, not a kernel oracle wrapper.
The conclusion is the original named statement with its exact legacy constants.
Actual P_n/Q_n suppliers are explicit, separate, indispensable premises. -/
theorem actual_kernel_budget_of_actual_flow_inverse
    (hFlow : ActualFlowBudgetStatement) (hInverse : ActualInverseBudgetStatement) :
    ActualKernelBudgetStatement := by
  intro D d hsmall n y S hS
  have h := actualKernel_splitNorm_le_const_integrand d hsmall n y S
    (fun t ht => actualKernelIntegrand_allProper hFlow hInverse d hsmall ht n y S hS)
  convert h using 1; ring

end AcceleratedLogConcave.Tensor.QuantitativeKernel.KernelFiniteAssembly
