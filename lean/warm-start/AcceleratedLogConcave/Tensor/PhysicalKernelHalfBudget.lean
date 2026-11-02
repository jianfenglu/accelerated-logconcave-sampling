import AcceleratedLogConcave.Tensor.OriginalDataKernelBudget
import AcceleratedLogConcave.Tensor.LegacyNumericalBudgets

/-!
NEW proof source, not recovered historical text.
Validation status is recorded in accompanying receipts; source text is not a receipt.

The genuine original-data all-order kernel theorem is converted to the physical
row/column slot convention and to the half-budget needed by the two-block phase
transport adapter. No derivative bound or coordinate equality is assumed.
Only original positive-variance flow data and the original smallness inequality
are premises. In particular, no positivity of ell or b and no D > 0 is required.
-/
noncomputable section
set_option autoImplicit false
open scoped Classical
namespace AcceleratedLogConcave.Tensor.PhysicalKernelBudget
open Conditional QuantitativeKernel
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)

/-- The source uses input/output, while the physical tensor uses row/column.
Every derivative slot stays fixed; input becomes column 1, output becomes row 0. -/
def physicalKernelSlotChart (n : ℕ) :
    (Fin n ⊕ (Unit ⊕ Unit)) ≃ (Fin n ⊕ Fin 2) where
  toFun
    | .inl i => .inl i
    | .inr (.inl _) => .inr 1
    | .inr (.inr _) => .inr 0
  invFun
    | .inl i => .inl i
    | .inr k => if k = 0 then .inr (.inr ()) else .inr (.inl ())
  left_inv := by
    intro a
    rcases a with i | (u | u)
    · rfl
    · cases u; rfl
    · cases u; rfl
  right_inv := by
    intro a
    rcases a with i | k
    · rfl
    · fin_cases k <;> rfl

/-- Literal Frechet coordinates of a physical operator field: derivative slots
in Fin n, matrix row at inr 0, matrix column at inr 1. This is not a free field. -/
def physicalOperatorJetCoeff (n : ℕ) (f : E → E →L[ℝ] E) (y : E) :
    Coeff (Fin n ⊕ Fin 2) D :=
  WithLp.toLp 2 (fun a => inner ℝ
    (EuclideanSpace.basisFun (Fin D) ℝ (a (.inr 0)))
    ((iteratedFDeriv ℝ n f y
      (fun i => EuclideanSpace.basisFun (Fin D) ℝ (a (.inl i))))
      (EuclideanSpace.basisFun (Fin D) ℝ (a (.inr 1)))))

/-- Exact coefficients, not an assumed tensor representation or an estimate. -/
theorem physicalOperatorJetCoeff_eq_relabel (n : ℕ)
    (f : E → E →L[ℝ] E) (y : E) :
    physicalOperatorJetCoeff n f y =
      EdgeClosure.relabel D (physicalKernelSlotChart n) (operatorJetCoeff n f y) := by
  ext a
  rfl

/-- Every proper cut is preserved, including mixed derivative/row/column cuts. -/
theorem original_data_physicalKernel_allProper
    (d : PositiveVarianceFlowData E) (hsmall : d.r^2*d.ell ≤ 1/2)
    (n : ℕ) (y : E) :
    AllProper D (physicalOperatorJetCoeff n (actualK d) y)
      ((d.r*d.ell)*d.b*spatialScale d.b^n*kernelConstant n) := by
  rw [physicalOperatorJetCoeff_eq_relabel]
  have h : EdgeClosure.AllProper D (operatorJetCoeff n (actualK d) y)
      ((d.r*d.ell)*d.b*spatialScale d.b^n*kernelConstant n) :=
    OriginalDataKernel.original_data_actualKernelBudgetStatement D d hsmall n y
  exact h.relabel (physicalKernelSlotChart n)

/-- Absorb the universal kernel envelope into the exact two-block allowance.
The extra power of c pays order zero, where kernelConstant 0 is exp(1/4), not 1. -/
theorem kernelConstant_le_physical_halfBudget {c : ℝ} (hc : 128 ≤ c) (n : ℕ) :
    kernelConstant n ≤ c^(2+n)*((2+n).factorial : ℝ)/2 := by
  have hc0 : 0 ≤ c := by linarith
  have hf : (n.factorial : ℝ) ≤ ((2+n).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : n ≤ 2+n)
  have hp : 2*c^(n+1) ≤ c^(2+n) := by
    have h := mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ c by linarith)
      (pow_nonneg hc0 (n+1))
    convert h using 1
    rw [show 2+n = (n+1)+1 by omega, pow_succ]
    ring
  have hp' := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg n.factorial)
  have hf' := mul_le_mul_of_nonneg_left hf (pow_nonneg hc0 (2+n))
  have hk := LegacyNumericalBudgets.kernelConstant_le_universal_threshold hc n
  linarith

/-- The endpoint b is not divided out: this estimate is valid also for b=0,
including n=0 with the ordinary convention 0^0=1. -/
theorem endpoint_spatialScale_le_radius {b R : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hR : 0 < R) (n : ℕ) :
    b*(b/R)^n ≤ R^(-(n : ℝ)) := by
  have hp : b^n ≤ 1 := pow_le_one₀ hb0 hb1
  have hb : b*b^n ≤ 1 := by
    have h := mul_le_mul hb1 hp (pow_nonneg hb0 n) (by norm_num : (0 : ℝ) ≤ 1)
    simpa using h
  calc
    b*(b/R)^n = (b*b^n)*(R^n)⁻¹ := by rw [div_pow]; simp only [div_eq_mul_inv]; ring
    _ ≤ 1*(R^n)⁻¹ := mul_le_mul_of_nonneg_right hb (by positivity)
    _ = R^(-(n : ℝ)) := by rw [Real.rpow_neg hR.le, Real.rpow_natCast]; ring

/-- Pure numerical conversion, separated from all analytic input. -/
theorem kernelScalar_le_physical_halfBudget {beta b R c : ℝ}
    (hbeta : 0 ≤ beta) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hR : 0 < R) (hc : 128 ≤ c) (n : ℕ) :
    beta*b*(b/R)^n*kernelConstant n ≤
      beta*(c^(2+n)*((2+n).factorial : ℝ)*R^(-(n : ℝ)))/2 := by
  have hr := endpoint_spatialScale_le_radius hb0 hb1 hR n
  have hk := kernelConstant_le_physical_halfBudget hc n
  have h := mul_le_mul hr hk (LegacyNumericalBudgets.kernelConstant_nonneg n)
    (Real.rpow_nonneg hR.le _)
  have hm := mul_le_mul_of_nonneg_left h hbeta
  calc
    beta*b*(b/R)^n*kernelConstant n = beta*((b*(b/R)^n)*kernelConstant n) := by ring
    _ ≤ beta*(R^(-(n : ℝ))*(c^(2+n)*((2+n).factorial : ℝ)/2)) := hm
    _ = _ := by ring

/-- Original-data physical all-order half-budget at the original variance radius.
The only hypotheses beyond data are r² ell ≤ 1/2 and the universal c ≥ 128. -/
theorem original_data_physicalKernel_halfBudget
    (d : PositiveVarianceFlowData E) (hsmall : d.r^2*d.ell ≤ 1/2)
    {c : ℝ} (hc : 128 ≤ c) (n : ℕ) (y : E)
    (S : Finset (Fin n ⊕ Fin 2)) (hS : NontrivialSplit S) :
    splitNorm D S (physicalOperatorJetCoeff n (actualK d) y) ≤
      (d.r*d.ell)*(c^(2+n)*((2+n).factorial : ℝ)*
        (Real.sqrt (1-d.b^2))^(-(n : ℝ)))/2 := by
  have hR : 0 < Real.sqrt (1-d.b^2) := by
    apply Real.sqrt_pos.mpr
    exact conditionalVariance_pos (by linarith [d.hb0]) d.hb1
  apply (original_data_physicalKernel_allProper d hsmall n y S hS).trans
  exact kernelScalar_le_physical_halfBudget (mul_nonneg d.hr.le d.hell)
    d.hb0 d.hb1.le hR hc n

/-- Explicit finite-order interface; there is no N-dependent constant or premise. -/
theorem original_data_physicalKernel_finiteHalfBudgets
    (d : PositiveVarianceFlowData E) (hsmall : d.r^2*d.ell ≤ 1/2)
    {c : ℝ} (hc : 128 ≤ c) (N : ℕ) :
    ∀ n ≤ N, ∀ (y : E) (S : Finset (Fin n ⊕ Fin 2)), NontrivialSplit S →
      splitNorm D S (physicalOperatorJetCoeff n (actualK d) y) ≤
        (d.r*d.ell)*(c^(2+n)*((2+n).factorial : ℝ)*
          (Real.sqrt (1-d.b^2))^(-(n : ℝ)))/2 := by
  intro n _ y S hS
  exact original_data_physicalKernel_halfBudget d hsmall hc n y S hS

/-- The L=a=r ell normalization also has a total, zero-safe half-budget.
The positive-curvature case cancels beta; the zero case uses inverse zero. -/
theorem original_data_normalizedPhysicalKernel_halfBudget
    (d : PositiveVarianceFlowData E) (hsmall : d.r^2*d.ell ≤ 1/2)
    {c : ℝ} (hc : 128 ≤ c) (n : ℕ) (y : E)
    (S : Finset (Fin n ⊕ Fin 2)) (hS : NontrivialSplit S) :
    |(d.r*d.ell)⁻¹| *splitNorm D S (physicalOperatorJetCoeff n (actualK d) y) ≤
      (c^(2+n)*((2+n).factorial : ℝ)*(Real.sqrt (1-d.b^2))^(-(n : ℝ)))/2 := by
  have hc0 : 0 ≤ c := by linarith
  by_cases hb : d.r*d.ell = 0
  · simp only [hb, inv_zero, abs_zero, zero_mul]
    positivity
  · have hbeta : 0 < d.r*d.ell :=
      lt_of_le_of_ne (mul_nonneg d.hr.le d.hell) (Ne.symm hb)
    calc
      _ ≤ |(d.r*d.ell)⁻¹| *((d.r*d.ell)*
          (c^(2+n)*((2+n).factorial : ℝ)*(Real.sqrt (1-d.b^2))^(-(n : ℝ)))/2) :=
        mul_le_mul_of_nonneg_left
          (original_data_physicalKernel_halfBudget d hsmall hc n y S hS) (abs_nonneg _)
      _ = _ := by
        rw [abs_of_pos (inv_pos.mpr hbeta)]
        calc
          _ = ((d.r*d.ell)⁻¹*(d.r*d.ell))*
            ((c^(2+n)*((2+n).factorial : ℝ)*(Real.sqrt (1-d.b^2))^(-(n : ℝ)))/2) := by ring
          _ = _ := by rw [inv_mul_cancel₀ hb, one_mul]

/-- Exact zero split bounds at zero curvature, with no division by ell. -/
theorem physicalKernel_allProper_zero_curvature
    (d : PositiveVarianceFlowData E) (hsmall : d.r^2*d.ell ≤ 1/2)
    (hell : d.ell = 0) (n : ℕ) (y : E) :
    AllProper D (physicalOperatorJetCoeff n (actualK d) y) 0 := by
  simpa only [hell, mul_zero, zero_mul] using
    original_data_physicalKernel_allProper d hsmall n y

/-- Exact zero split bounds on the singleton slab, including order zero. -/
theorem physicalKernel_allProper_zero_endpoint
    (d : PositiveVarianceFlowData E) (hsmall : d.r^2*d.ell ≤ 1/2)
    (hb : d.b = 0) (n : ℕ) (y : E) :
    AllProper D (physicalOperatorJetCoeff n (actualK d) y) 0 := by
  simpa only [hb, mul_zero, zero_mul] using
    original_data_physicalKernel_allProper d hsmall n y

/-- In zero dimension the literal coefficient vanishes; no coordinate is chosen. -/
theorem physicalOperatorJetCoeff_dimension_zero (n : ℕ)
    (f : EuclideanSpace ℝ (Fin 0) →
      EuclideanSpace ℝ (Fin 0) →L[ℝ] EuclideanSpace ℝ (Fin 0))
    (y : EuclideanSpace ℝ (Fin 0)) : physicalOperatorJetCoeff n f y = 0 := by
  ext a
  exact Fin.elim0 (a (.inr 0))

end AcceleratedLogConcave.Tensor.PhysicalKernelBudget
