import AcceleratedLogConcave.Analysis.Poisson.StrongMultiplier
import AcceleratedLogConcave.Analysis.Poisson.MovingForms
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Strong differentiation of multiplier energy forms

The energy coefficient is differentiated through the pointwise matrix field
`M(t,x)† M(t,x)`. This requires only strong differentiation on fixed L2 vectors.
-/
noncomputable section
open MeasureTheory InnerProductSpace Filter
open scoped Topology RealInnerProductSpace

namespace AcceleratedLogConcave.Analysis.Poisson

section Algebra
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Pointwise coefficient of the energy form. -/
def matrixEnergy (A : E →L[ℝ] E) : E →L[ℝ] E := A.adjoint.comp A

/-- Its pointwise derivative in the direction `A'`. -/
def matrixEnergyDerivative (A A' : E →L[ℝ] E) : E →L[ℝ] E :=
  A'.adjoint.comp A + A.adjoint.comp A'

theorem matrixEnergy_hasDerivAt {A : ℝ → E →L[ℝ] E} {A' : E →L[ℝ] E} {t : ℝ}
    (h : HasDerivAt A A' t) :
    HasDerivAt (fun s => matrixEnergy (A s)) (matrixEnergyDerivative (A t) A') t := by
  have ha : HasDerivAt (fun s => (A s).adjoint) A'.adjoint t :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := E)).hasFDerivAt.comp_hasDerivAt t h
  have hh := ha.clm_comp h
  convert hh using 1 <;> rfl

theorem matrixEnergy_norm_le (A : E →L[ℝ] E) : ‖matrixEnergy A‖ ≤ ‖A‖ ^ 2 := by
  simpa [matrixEnergy, pow_two] using A.adjoint.opNorm_comp_le A

theorem matrixEnergyDerivative_norm_le (A A' : E →L[ℝ] E) :
    ‖matrixEnergyDerivative A A'‖ ≤ 2 * ‖A‖ * ‖A'‖ := by
  calc
    _ ≤ ‖A'.adjoint.comp A‖ + ‖A.adjoint.comp A'‖ := norm_add_le _ _
    _ ≤ ‖A'‖ * ‖A‖ + ‖A‖ * ‖A'‖ := by
      exact add_le_add (by simpa using A'.adjoint.opNorm_comp_le A)
        (by simpa using A.adjoint.opNorm_comp_le A')
    _ = _ := by ring

theorem matrixEnergy_slope (A : ℝ → E →L[ℝ] E) (s t : ℝ) :
    slope (fun r => matrixEnergy (A r)) s t =
      (slope A s t).adjoint.comp (A t) + (A s).adjoint.comp (slope A s t) := by
  simp only [slope_def_module, matrixEnergy, map_smul, map_sub,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.sub_comp,
    ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_sub]
  module

theorem matrixEnergy_slope_norm_le (A : ℝ → E →L[ℝ] E) (s t C K : ℝ)
    (hs : ‖A s‖ ≤ K) (ht : ‖A t‖ ≤ K) (hq : ‖slope A s t‖ ≤ C) :
    ‖slope (fun r => matrixEnergy (A r)) s t‖ ≤ 2 * K * C := by
  have hK : 0 ≤ K := (norm_nonneg _).trans hs
  have hC : 0 ≤ C := (norm_nonneg _).trans hq
  rw [matrixEnergy_slope]
  calc
    _ ≤ ‖(slope A s t).adjoint.comp (A t)‖ + ‖(A s).adjoint.comp (slope A s t)‖ := norm_add_le _ _
    _ ≤ C * K + K * C := by
      apply add_le_add
      · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul (by simpa using hq) ht (norm_nonneg _) hC)
      · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul (by simpa using hs) hq (norm_nonneg _) hK)
    _ = _ := by ring


/-- For the material derivative `A' = c H A` with symmetric `H`, the energy
matrix derivative is twice the curvature form. -/
theorem matrixEnergyDerivative_symmetric (A H : E →L[ℝ] E) (c : ℝ)
    (hH : H.IsSymmetric) :
    matrixEnergyDerivative A (c • H.comp A) =
      (2 * c) • A.adjoint.comp (H.comp A) := by
  simp only [matrixEnergyDerivative, map_smul, ContinuousLinearMap.adjoint_comp,
    hH.clm_adjoint_eq, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.comp_assoc]
  module

end Algebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Multiplier by the energy matrix. -/
def energyFieldMultiplier (μ : Measure E) (A : E → E →L[ℝ] E) (hA : Continuous A)
    (K : ℝ) (hK : ∀ x, ‖A x‖ ≤ K) : Lp E 2 μ →L[ℝ] Lp E 2 μ :=
  fieldMultiplier μ (fun x => matrixEnergy (A x))
    ((ContinuousLinearMap.adjoint.continuous.comp hA).clm_comp hA) (K ^ 2)
    (fun x => (matrixEnergy_norm_le (A x)).trans
      ((sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans (hK x))).mpr (hK x)))

/-- Multiplier by the derivative of the energy matrix. -/
def energyDerivativeFieldMultiplier (μ : Measure E)
    (A A' : E → E →L[ℝ] E) (hA : Continuous A) (hA' : Continuous A')
    (K K' : ℝ) (hK : ∀ x, ‖A x‖ ≤ K) (hK' : ∀ x, ‖A' x‖ ≤ K') :
    Lp E 2 μ →L[ℝ] Lp E 2 μ :=
  fieldMultiplier μ (fun x => matrixEnergyDerivative (A x) (A' x))
    (((ContinuousLinearMap.adjoint.continuous.comp hA').clm_comp hA).add
      ((ContinuousLinearMap.adjoint.continuous.comp hA).clm_comp hA')) (2 * K * K')
    (fun x => (matrixEnergyDerivative_norm_le (A x) (A' x)).trans (by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hK x) (by norm_num))
        (hK' x) (norm_nonneg _)
        (mul_nonneg (by norm_num) ((norm_nonneg _).trans (hK x)))))

theorem energyDerivativeFieldMultiplier_coe (μ : Measure E)
    (A A' : E → E →L[ℝ] E) (hA : Continuous A) (hA' : Continuous A')
    (K K' : ℝ) (hK : ∀ x, ‖A x‖ ≤ K) (hK' : ∀ x, ‖A' x‖ ≤ K') (G : Lp E 2 μ) :
    energyDerivativeFieldMultiplier μ A A' hA hA' K K' hK hK' G =ᵐ[μ]
      fun x => matrixEnergyDerivative (A x) (A' x) (G x) := by
  unfold energyDerivativeFieldMultiplier
  exact fieldMultiplier_coe _ _ _ _ _ _

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The actual energy coefficient equals the multiplier by `A†A`, pulled back to
its fixed Hilbert domain. -/
theorem energyCoefficient_fieldMultiplier (μ : Measure E)
    (A : E → E →L[ℝ] E) (hA : Continuous A) (K : ℝ) (hK : ∀ x, ‖A x‖ ≤ K)
    (D : V →L[ℝ] Lp E 2 μ) :
    MovingForms.energyCoefficient ((fieldMultiplier μ A hA K hK).comp D) =
      D.adjoint.comp ((energyFieldMultiplier μ A hA K hK).comp D) := by
  ext u
  apply ext_inner_right ℝ
  intro v
  rw [MovingForms.energyCoefficient_inner]
  simp only [ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_left]
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fieldMultiplier_coe μ A hA K hK (D u),
    fieldMultiplier_coe μ A hA K hK (D v),
    fieldMultiplier_coe μ (fun x => matrixEnergy (A x))
      ((ContinuousLinearMap.adjoint.continuous.comp hA).clm_comp hA) (K ^ 2)
      (fun x => (matrixEnergy_norm_le (A x)).trans
        ((sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans (hK x))).mpr (hK x))) (D u)] with x hu hv hq
  change (energyFieldMultiplier μ A hA K hK (D u)) x = _ at hq
  rw [hu, hv, hq]
  exact (ContinuousLinearMap.adjoint_inner_left (A x) (D v x) (A x (D u x))).symm


/-- Strong differentiation of the energy matrix multiplier, proved from its
pointwise derivative and the product difference-quotient estimate. -/
theorem hasDerivAt_energyFieldMultiplier (μ : Measure E)
    (A : ℝ → E → E →L[ℝ] E) (hA : ∀ t, Continuous (A t))
    (K : ℝ) (hK : ∀ t x, ‖A t x‖ ≤ K)
    (A' : E → E →L[ℝ] E) (hA' : Continuous A') (K' : ℝ) (hK' : ∀ x, ‖A' x‖ ≤ K')
    (t₀ C : ℝ)
    (hquot : ∀ᶠ t in 𝓝[≠] t₀, ∀ x, ‖slope (fun s => A s x) t₀ t‖ ≤ C)
    (hderiv : ∀ x, HasDerivAt (fun t => A t x) (A' x) t₀) (G : Lp E 2 μ) :
    HasDerivAt (fun t => energyFieldMultiplier μ (A t) (hA t) K (hK t) G)
      (energyDerivativeFieldMultiplier μ (A t₀) A' (hA t₀) hA' K K' (hK t₀) hK' G) t₀ := by
  apply hasDerivAt_fieldMultiplier
    (C := 2 * K * C)
  · filter_upwards [hquot] with t ht
    exact fun x => matrixEnergy_slope_norm_le (fun s => A s x) t₀ t C K
      (hK t₀ x) (hK t x) (ht x)
  · exact fun x => matrixEnergy_hasDerivAt (hderiv x)

/-- Operator norm continuity of the energy matrix multiplier follows from the
uniform local quotient bound; differentiability is only claimed strongly. -/
theorem continuousAt_energyFieldMultiplier (μ : Measure E)
    (A : ℝ → E → E →L[ℝ] E) (hA : ∀ t, Continuous (A t))
    (K : ℝ) (hK : ∀ t x, ‖A t x‖ ≤ K) (t₀ C : ℝ)
    (hquot : ∀ᶠ t in 𝓝[≠] t₀, ∀ x, ‖slope (fun s => A s x) t₀ t‖ ≤ C) :
    ContinuousAt (fun t => energyFieldMultiplier μ (A t) (hA t) K (hK t)) t₀ := by
  apply continuousAt_fieldMultiplier_of_quotient_bound (C := 2 * K * C)
  filter_upwards [hquot] with t ht
  exact fun x => matrixEnergy_slope_norm_le (fun s => A s x) t₀ t C K
    (hK t₀ x) (hK t x) (ht x)

/-- Strong derivative of the actual common-domain energy coefficient. -/
theorem hasDerivAt_energyCoefficient_fieldMultiplier (μ : Measure E)
    (A : ℝ → E → E →L[ℝ] E) (hA : ∀ t, Continuous (A t))
    (K : ℝ) (hK : ∀ t x, ‖A t x‖ ≤ K)
    (A' : E → E →L[ℝ] E) (hA' : Continuous A') (K' : ℝ) (hK' : ∀ x, ‖A' x‖ ≤ K')
    (t₀ C : ℝ)
    (hquot : ∀ᶠ t in 𝓝[≠] t₀, ∀ x, ‖slope (fun s => A s x) t₀ t‖ ≤ C)
    (hderiv : ∀ x, HasDerivAt (fun t => A t x) (A' x) t₀)
    (D : V →L[ℝ] Lp E 2 μ) (u : V) :
    HasDerivAt (fun t => MovingForms.energyCoefficient
      ((fieldMultiplier μ (A t) (hA t) K (hK t)).comp D) u)
      (D.adjoint (energyDerivativeFieldMultiplier μ (A t₀) A' (hA t₀) hA' K K'
        (hK t₀) hK' (D u))) t₀ := by
  simp only [energyCoefficient_fieldMultiplier, ContinuousLinearMap.comp_apply]
  exact D.adjoint.hasFDerivAt.comp_hasDerivAt t₀
    (hasDerivAt_energyFieldMultiplier μ A hA K hK A' hA' K' hK' t₀ C hquot hderiv (D u))

/-- Norm continuity needed by the coercive inverse derivative theorem. -/
theorem continuousAt_energyCoefficient_fieldMultiplier (μ : Measure E)
    (A : ℝ → E → E →L[ℝ] E) (hA : ∀ t, Continuous (A t))
    (K : ℝ) (hK : ∀ t x, ‖A t x‖ ≤ K) (t₀ C : ℝ)
    (hquot : ∀ᶠ t in 𝓝[≠] t₀, ∀ x, ‖slope (fun s => A s x) t₀ t‖ ≤ C)
    (D : V →L[ℝ] Lp E 2 μ) :
    ContinuousAt (fun t => MovingForms.energyCoefficient
      ((fieldMultiplier μ (A t) (hA t) K (hK t)).comp D)) t₀ := by
  simp only [energyCoefficient_fieldMultiplier]
  exact continuousAt_const.clm_comp
    ((continuousAt_energyFieldMultiplier μ A hA K hK t₀ C hquot).clm_comp continuousAt_const)

end AcceleratedLogConcave.Analysis.Poisson
