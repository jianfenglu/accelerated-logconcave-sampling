import AcceleratedLogConcave.Analysis.Poisson.StrongForm
import AcceleratedLogConcave.Analysis.Poisson.InverseJacobian

/-!
# Strong material differentiation of the actual reference gradient multiplier

The inverse-transpose Jacobian is extended by the identity outside the open
interval. All derivative statements are at interior times.
-/
noncomputable section
open MeasureTheory InnerProductSpace Filter Set
open scoped Topology RealInnerProductSpace NNReal
namespace AcceleratedLogConcave.Analysis.Poisson

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable (U : ℝ → E → ℝ) (c : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
  (hU : ∀ t, ContDiff ℝ 2 (U t))
  (hG : Continuous (Function.uncurry (fun t => gradient (U t))))
  (hH : Continuous (Function.uncurry (fun t => hessianOperator (U t))))
  (hc : Continuous c) (C : ℝ≥0)
  (hC : ∀ t ∈ Icc a b, |c t| ≤ C)
  (hlo : ∀ t ∈ Icc a b, ∀ x v, 0 ≤ fderiv ℝ (fderiv ℝ (U t)) x v v)
  (hup : ∀ t ∈ Icc a b, ∀ x v, fderiv ℝ (fderiv ℝ (U t)) x v v ≤ ‖v‖ ^ 2)

/-- Identity extension preserves coercivity of a reference gradient outside the
interval while agreeing with the genuine transported coefficient inside. -/
def extendedReferenceGradientMatrix (t : ℝ) (x : E) : E →L[ℝ] E :=
  if t ∈ Ioo a b then referenceGradientMatrix U c hab hU hG hH hc C hC hlo hup t x
  else ContinuousLinearMap.id ℝ E

theorem extendedReferenceGradientMatrix_eq (t : ℝ) (ht : t ∈ Ioo a b) (x : E) :
    extendedReferenceGradientMatrix U c hab hU hG hH hc C hC hlo hup t x =
      referenceGradientMatrix U c hab hU hG hH hc C hC hlo hup t x := by
  simp [extendedReferenceGradientMatrix, ht]

theorem extendedReferenceGradientMatrix_continuous (t : ℝ) :
    Continuous (extendedReferenceGradientMatrix U c hab hU hG hH hc C hC hlo hup t) := by
  change Continuous (fun x => if t ∈ Ioo a b then
    referenceGradientMatrix U c hab hU hG hH hc C hC hlo hup t x else ContinuousLinearMap.id ℝ E)
  by_cases ht : t ∈ Ioo a b
  · simpa only [extendedReferenceGradientMatrix, ite_eq_left ht] using
      referenceGradientMatrix_continuous U c hab hU hG hH hc C hC hlo hup ⟨t, ht.1.le, ht.2.le⟩
  · simpa only [extendedReferenceGradientMatrix, ite_eq_right ht] using
      (continuous_const : Continuous (fun _ : E => ContinuousLinearMap.id ℝ E))

theorem extendedReferenceGradientMatrix_norm_le (t : ℝ) (x : E) :
    ‖extendedReferenceGradientMatrix U c hab hU hG hH hc C hC hlo hup t x‖ ≤
      Real.exp ((C : ℝ) * (b - a)) := by
  by_cases ht : t ∈ Ioo a b
  · rw [extendedReferenceGradientMatrix_eq U c hab hU hG hH hc C hC hlo hup t ht]
    exact referenceGradientMatrix_uniform_norm_le U c hab hU hG hH hc C hC hlo hup x
      ⟨t, ht.1.le, ht.2.le⟩
  · simp only [extendedReferenceGradientMatrix, ite_eq_right ht]
    exact ContinuousLinearMap.norm_id_le.trans
      (Real.one_le_exp (mul_nonneg C.coe_nonneg (sub_nonneg.mpr hab)))

/-- Actual pointwise material velocity of the inverse-transpose field. -/
def referenceGradientMatrixVelocity (t : ℝ) (x : E) : E →L[ℝ] E :=
  (c t) • (hessianOperator (U t)
    (referenceFlow U c (fun t _ => hU t) hG hc C hC hlo hup ⟨a, le_rfl, hab⟩ x t)).comp
      (referenceGradientMatrix U c hab hU hG hH hc C hC hlo hup t x)

theorem referenceGradientMatrixVelocity_continuous (t : ℝ) (ht : t ∈ Ioo a b) :
    Continuous (referenceGradientMatrixVelocity U c hab hU hG hH hc C hC hlo hup t) := by
  have hflow : Continuous (fun x =>
      referenceFlow U c (fun t _ => hU t) hG hc C hC hlo hup ⟨a, le_rfl, hab⟩ x t) :=
    (referenceFlowHomeomorph U c (fun t _ => hU t) hG hc C hC hlo hup
      ⟨a, le_rfl, hab⟩ ⟨t, ht.1.le, ht.2.le⟩).continuous
  exact ((hH.comp (continuous_const.prodMk hflow)).clm_comp
    (referenceGradientMatrix_continuous U c hab hU hG hH hc C hC hlo hup
      ⟨t, ht.1.le, ht.2.le⟩)).const_smul (c t)

theorem referenceGradientMatrixVelocity_norm_le (t : ℝ) (ht : t ∈ Ioo a b) (x : E) :
    ‖referenceGradientMatrixVelocity U c hab hU hG hH hc C hC hlo hup t x‖ ≤
      (C : ℝ) * Real.exp ((C : ℝ) * (b - a)) := by
  unfold referenceGradientMatrixVelocity
  rw [← (referenceGradientMatrix_hasDerivAt U c hab hU hG hH hc C hC hlo hup x t ht).deriv]
  exact referenceGradientMatrix_deriv_norm_le U c hab hU hG hH hc C hC hlo hup x t ht

theorem extendedReferenceGradientMatrix_hasDerivAt (t : ℝ) (ht : t ∈ Ioo a b) (x : E) :
    HasDerivAt (fun s => extendedReferenceGradientMatrix U c hab hU hG hH hc C hC hlo hup s x)
      (referenceGradientMatrixVelocity U c hab hU hG hH hc C hC hlo hup t x) t := by
  apply (referenceGradientMatrix_hasDerivAt U c hab hU hG hH hc C hC hlo hup x t ht).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  exact extendedReferenceGradientMatrix_eq U c hab hU hG hH hc C hC hlo hup s hs x

theorem extendedReferenceGradientMatrix_slope_bound (t : ℝ) (ht : t ∈ Ioo a b) :
    ∀ᶠ s in 𝓝[≠] t, ∀ x,
      ‖slope (fun r => extendedReferenceGradientMatrix U c hab hU hG hH hc C hC hlo hup r x) t s‖ ≤
        (C : ℝ) * Real.exp ((C : ℝ) * (b - a)) := by
  filter_upwards [nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds ht)] with s hs
  intro x
  simpa only [slope_def_module, extendedReferenceGradientMatrix, ite_eq_left ht, ite_eq_left hs] using
    referenceGradientMatrix_slope_norm_le U c hab hU hG hH hc C hC hlo hup x t s ht hs

variable [MeasurableSpace E] [BorelSpace E]

/-- Actual bounded multiplier of the reference gradient coefficient. -/
def referenceGradientMultiplier (μ : Measure E) (t : ℝ) : Lp E 2 μ →L[ℝ] Lp E 2 μ :=
  fieldMultiplier μ (extendedReferenceGradientMatrix U c hab hU hG hH hc C hC hlo hup t)
    (extendedReferenceGradientMatrix_continuous U c hab hU hG hH hc C hC hlo hup t)
    (Real.exp ((C : ℝ) * (b - a)))
    (extendedReferenceGradientMatrix_norm_le U c hab hU hG hH hc C hC hlo hup t)

/-- Actual material velocity multiplier at an interior time. -/
def referenceGradientMultiplierVelocity (μ : Measure E) (t : ℝ) (ht : t ∈ Ioo a b) :
    Lp E 2 μ →L[ℝ] Lp E 2 μ :=
  fieldMultiplier μ (referenceGradientMatrixVelocity U c hab hU hG hH hc C hC hlo hup t)
    (referenceGradientMatrixVelocity_continuous U c hab hU hG hH hc C hC hlo hup t ht)
    ((C : ℝ) * Real.exp ((C : ℝ) * (b - a)))
    (referenceGradientMatrixVelocity_norm_le U c hab hU hG hH hc C hC hlo hup t ht)

theorem referenceGradientMultiplier_hasDerivAt (μ : Measure E) (t : ℝ)
    (ht : t ∈ Ioo a b) (G : Lp E 2 μ) :
    HasDerivAt (fun s => referenceGradientMultiplier U c hab hU hG hH hc C hC hlo hup μ s G)
      (referenceGradientMultiplierVelocity U c hab hU hG hH hc C hC hlo hup μ t ht G) t := by
  apply hasDerivAt_fieldMultiplier (C := (C : ℝ) * Real.exp ((C : ℝ) * (b - a)))
  · exact extendedReferenceGradientMatrix_slope_bound U c hab hU hG hH hc C hC hlo hup t ht
  · exact extendedReferenceGradientMatrix_hasDerivAt U c hab hU hG hH hc C hC hlo hup t ht

theorem referenceGradientMultiplier_continuousAt (μ : Measure E) (t : ℝ)
    (ht : t ∈ Ioo a b) :
    ContinuousAt (referenceGradientMultiplier U c hab hU hG hH hc C hC hlo hup μ) t := by
  apply continuousAt_fieldMultiplier_of_quotient_bound
    (C := (C : ℝ) * Real.exp ((C : ℝ) * (b - a)))
  exact extendedReferenceGradientMatrix_slope_bound U c hab hU hG hH hc C hC hlo hup t ht



/-- Hessian of the current potential, evaluated along the genuine reference flow. -/
def referenceHessianField (t : ℝ) (x : E) : E →L[ℝ] E :=
  hessianOperator (U t)
    (referenceFlow U c (fun t _ => hU t) hG hc C hC hlo hup ⟨a, le_rfl, hab⟩ x t)

include hH in
omit [MeasurableSpace E] [BorelSpace E] in
theorem referenceHessianField_continuous (t : ℝ) (ht : t ∈ Ioo a b) :
    Continuous (referenceHessianField U c hab hU hG hc C hC hlo hup t) := by
  exact hH.comp (continuous_const.prodMk
    (referenceFlowHomeomorph U c (fun t _ => hU t) hG hc C hC hlo hup
      ⟨a, le_rfl, hab⟩ ⟨t, ht.1.le, ht.2.le⟩).continuous)

omit [MeasurableSpace E] [BorelSpace E] in
theorem referenceHessianField_norm_le (t : ℝ) (ht : t ∈ Ioo a b) (x : E) :
    ‖referenceHessianField U c hab hU hG hc C hC hlo hup t x‖ ≤ 1 := by
  simpa [referenceHessianField] using hessianOperator_norm_le (hU t) (m := 0) (L := 1)
    (by simpa using hlo t ⟨ht.1.le, ht.2.le⟩)
    (by simpa using hup t ⟨ht.1.le, ht.2.le⟩)
    (referenceFlow U c (fun t _ => hU t) hG hc C hC hlo hup ⟨a, le_rfl, hab⟩ x t)

/-- The actual bounded material Hessian multiplier. -/
def referenceHessianMultiplier (μ : Measure E) (t : ℝ) (ht : t ∈ Ioo a b) :
    Lp E 2 μ →L[ℝ] Lp E 2 μ :=
  fieldMultiplier μ (referenceHessianField U c hab hU hG hc C hC hlo hup t)
    (referenceHessianField_continuous U c hab hU hG hH hc C hC hlo hup t ht) 1
    (referenceHessianField_norm_le U c hab hU hG hc C hC hlo hup t ht)

theorem referenceHessianMultiplier_coe (μ : Measure E) (t : ℝ) (ht : t ∈ Ioo a b)
    (G : Lp E 2 μ) :
    referenceHessianMultiplier U c hab hU hG hH hc C hC hlo hup μ t ht G =ᵐ[μ]
      fun x => hessianOperator (U t)
        (referenceFlow U c (fun t _ => hU t) hG hc C hC hlo hup ⟨a, le_rfl, hab⟩ x t) (G x) := by
  unfold referenceHessianMultiplier
  exact fieldMultiplier_coe _ _ _ _ _ _

theorem referenceHessianMultiplier_norm_le (μ : Measure E) (t : ℝ) (ht : t ∈ Ioo a b) :
    ‖referenceHessianMultiplier U c hab hU hG hH hc C hC hlo hup μ t ht‖ ≤ 1 :=
  fieldMultiplier_norm_le _ _ _ _ _

theorem referenceGradientMultiplier_coe (μ : Measure E) (t : ℝ) (ht : t ∈ Ioo a b)
    (G : Lp E 2 μ) :
    referenceGradientMultiplier U c hab hU hG hH hc C hC hlo hup μ t G =ᵐ[μ]
      fun x => referenceGradientMatrix U c hab hU hG hH hc C hC hlo hup t x (G x) := by
  apply (fieldMultiplier_coe _ _ _ _ _ _).trans
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [extendedReferenceGradientMatrix_eq U c hab hU hG hH hc C hC hlo hup t ht]

theorem referenceGradientMultiplierVelocity_eq (μ : Measure E) (t : ℝ) (ht : t ∈ Ioo a b)
    (G : Lp E 2 μ) :
    referenceGradientMultiplierVelocity U c hab hU hG hH hc C hC hlo hup μ t ht G =
      (c t) • referenceHessianMultiplier U c hab hU hG hH hc C hC hlo hup μ t ht
        (referenceGradientMultiplier U c hab hU hG hH hc C hC hlo hup μ t G) := by
  apply Lp.ext
  filter_upwards [fieldMultiplier_coe μ
      (referenceGradientMatrixVelocity U c hab hU hG hH hc C hC hlo hup t)
      (referenceGradientMatrixVelocity_continuous U c hab hU hG hH hc C hC hlo hup t ht)
      ((C : ℝ) * Real.exp ((C : ℝ) * (b - a)))
      (referenceGradientMatrixVelocity_norm_le U c hab hU hG hH hc C hC hlo hup t ht) G,
    Lp.coeFn_smul (c t) (referenceHessianMultiplier U c hab hU hG hH hc C hC hlo hup μ t ht
      (referenceGradientMultiplier U c hab hU hG hH hc C hC hlo hup μ t G)),
    referenceHessianMultiplier_coe U c hab hU hG hH hc C hC hlo hup μ t ht
      (referenceGradientMultiplier U c hab hU hG hH hc C hC hlo hup μ t G),
    referenceGradientMultiplier_coe U c hab hU hG hH hc C hC hlo hup μ t ht G] with x hv hs hh hg
  change (referenceGradientMultiplierVelocity U c hab hU hG hH hc C hC hlo hup μ t ht G) x = _ at hv
  rw [hv, hs, Pi.smul_apply, hh, hg]
  rfl

/-- Source form of the strong gradient derivative. -/
theorem referenceGradientMultiplier_hasDerivAt_curvature (μ : Measure E) (t : ℝ)
    (ht : t ∈ Ioo a b) (G : Lp E 2 μ) :
    HasDerivAt (fun s => referenceGradientMultiplier U c hab hU hG hH hc C hC hlo hup μ s G)
      ((c t) • referenceHessianMultiplier U c hab hU hG hH hc C hC hlo hup μ t ht
        (referenceGradientMultiplier U c hab hU hG hH hc C hC hlo hup μ t G)) t := by
  rw [← referenceGradientMultiplierVelocity_eq U c hab hU hG hH hc C hC hlo hup]
  exact referenceGradientMultiplier_hasDerivAt U c hab hU hG hH hc C hC hlo hup μ t ht G

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The concrete derivative coefficient on a fixed Hilbert domain. -/
def referenceEnergyCoefficientVelocity (μ : Measure E) (t : ℝ) (ht : t ∈ Ioo a b)
    (D : V →L[ℝ] Lp E 2 μ) : V →L[ℝ] V :=
  D.adjoint.comp ((energyDerivativeFieldMultiplier μ
    (extendedReferenceGradientMatrix U c hab hU hG hH hc C hC hlo hup t)
    (referenceGradientMatrixVelocity U c hab hU hG hH hc C hC hlo hup t)
    (extendedReferenceGradientMatrix_continuous U c hab hU hG hH hc C hC hlo hup t)
    (referenceGradientMatrixVelocity_continuous U c hab hU hG hH hc C hC hlo hup t ht)
    (Real.exp ((C : ℝ) * (b - a))) ((C : ℝ) * Real.exp ((C : ℝ) * (b - a)))
    (extendedReferenceGradientMatrix_norm_le U c hab hU hG hH hc C hC hlo hup t)
    (referenceGradientMatrixVelocity_norm_le U c hab hU hG hH hc C hC hlo hup t ht)).comp D)

/-- Actual strong energy derivative for the reference flow; no derivative of the
Hessian, nor operator norm differentiability, is assumed. -/
theorem referenceGradientEnergyCoefficient_hasDerivAt (μ : Measure E) (t : ℝ)
    (ht : t ∈ Ioo a b) (D : V →L[ℝ] Lp E 2 μ) (u : V) :
    HasDerivAt (fun s => MovingForms.energyCoefficient
      ((referenceGradientMultiplier U c hab hU hG hH hc C hC hlo hup μ s).comp D) u)
      (referenceEnergyCoefficientVelocity U c hab hU hG hH hc C hC hlo hup μ t ht D u) t := by
  apply hasDerivAt_energyCoefficient_fieldMultiplier
    (hA' := referenceGradientMatrixVelocity_continuous U c hab hU hG hH hc C hC hlo hup t ht)
    (K' := (C : ℝ) * Real.exp ((C : ℝ) * (b - a)))
    (hK' := referenceGradientMatrixVelocity_norm_le U c hab hU hG hH hc C hC hlo hup t ht)
    (C := (C : ℝ) * Real.exp ((C : ℝ) * (b - a)))
  · exact extendedReferenceGradientMatrix_slope_bound U c hab hU hG hH hc C hC hlo hup t ht
  · exact extendedReferenceGradientMatrix_hasDerivAt U c hab hU hG hH hc C hC hlo hup t ht

/-- The coefficient also has the norm continuity required to differentiate the
coercive inverse on the common domain. -/
theorem referenceGradientEnergyCoefficient_continuousAt (μ : Measure E) (t : ℝ)
    (ht : t ∈ Ioo a b) (D : V →L[ℝ] Lp E 2 μ) :
    ContinuousAt (fun s => MovingForms.energyCoefficient
      ((referenceGradientMultiplier U c hab hU hG hH hc C hC hlo hup μ s).comp D)) t := by
  apply continuousAt_energyCoefficient_fieldMultiplier
    (C := (C : ℝ) * Real.exp ((C : ℝ) * (b - a)))
  exact extendedReferenceGradientMatrix_slope_bound U c hab hU hG hH hc C hC hlo hup t ht

omit [MeasurableSpace E] [BorelSpace E] in
/-- The differentiated energy matrix is the actual curvature matrix along the
flow, with the source factor `2 c(t)`. -/
theorem referenceEnergyMatrixVelocity_eq (t : ℝ) (ht : t ∈ Ioo a b) (x : E) :
    matrixEnergyDerivative
      (extendedReferenceGradientMatrix U c hab hU hG hH hc C hC hlo hup t x)
      (referenceGradientMatrixVelocity U c hab hU hG hH hc C hC hlo hup t x) =
    (2 * c t) • (referenceGradientMatrix U c hab hU hG hH hc C hC hlo hup t x).adjoint.comp
      ((hessianOperator (U t)
        (referenceFlow U c (fun t _ => hU t) hG hc C hC hlo hup ⟨a, le_rfl, hab⟩ x t)).comp
        (referenceGradientMatrix U c hab hU hG hH hc C hC hlo hup t x)) := by
  rw [extendedReferenceGradientMatrix_eq U c hab hU hG hH hc C hC hlo hup t ht]
  exact matrixEnergyDerivative_symmetric _ _ _ (hessianOperator_symmetric (hU t) _)


/-- Source form of the differentiated energy coefficient, as a variational
right-hand side with the actual material Hessian. -/
theorem referenceEnergyCoefficientVelocity_eq (μ : Measure E) (t : ℝ) (ht : t ∈ Ioo a b)
    (D : V →L[ℝ] Lp E 2 μ) (u : V) :
    referenceEnergyCoefficientVelocity U c hab hU hG hH hc C hC hlo hup μ t ht D u =
      MovingForms.variationalRHS
        ((referenceGradientMultiplier U c hab hU hG hH hc C hC hlo hup μ t).comp D)
        ((2 * c t) • referenceHessianMultiplier U c hab hU hG hH hc C hC hlo hup μ t ht
          (referenceGradientMultiplier U c hab hU hG hH hc C hC hlo hup μ t (D u))) := by
  let Q := energyDerivativeFieldMultiplier μ
    (extendedReferenceGradientMatrix U c hab hU hG hH hc C hC hlo hup t)
    (referenceGradientMatrixVelocity U c hab hU hG hH hc C hC hlo hup t)
    (extendedReferenceGradientMatrix_continuous U c hab hU hG hH hc C hC hlo hup t)
    (referenceGradientMatrixVelocity_continuous U c hab hU hG hH hc C hC hlo hup t ht)
    (Real.exp ((C : ℝ) * (b - a))) ((C : ℝ) * Real.exp ((C : ℝ) * (b - a)))
    (extendedReferenceGradientMatrix_norm_le U c hab hU hG hH hc C hC hlo hup t)
    (referenceGradientMatrixVelocity_norm_le U c hab hU hG hH hc C hC hlo hup t ht)
  have hq : Q (D u) =ᵐ[μ] fun x => matrixEnergyDerivative
      (extendedReferenceGradientMatrix U c hab hU hG hH hc C hC hlo hup t x)
      (referenceGradientMatrixVelocity U c hab hU hG hH hc C hC hlo hup t x) (D u x) :=
    energyDerivativeFieldMultiplier_coe _ _ _ _ _ _ _ _ _ _
  apply ext_inner_right ℝ
  intro v
  change inner ℝ (D.adjoint (Q (D u))) v = _
  rw [ContinuousLinearMap.adjoint_inner_left, MovingForms.variationalRHS_inner]
  simp only [ContinuousLinearMap.comp_apply]
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hq,
    Lp.coeFn_smul (2 * c t) (referenceHessianMultiplier U c hab hU hG hH hc C hC hlo hup μ t ht
      (referenceGradientMultiplier U c hab hU hG hH hc C hC hlo hup μ t (D u))),
    referenceHessianMultiplier_coe U c hab hU hG hH hc C hC hlo hup μ t ht
      (referenceGradientMultiplier U c hab hU hG hH hc C hC hlo hup μ t (D u)),
    referenceGradientMultiplier_coe U c hab hU hG hH hc C hC hlo hup μ t ht (D u),
    referenceGradientMultiplier_coe U c hab hU hG hH hc C hC hlo hup μ t ht (D v)]
      with x hq hs hh hu hv
  rw [hq, hs, Pi.smul_apply, hh, hu, hv,
    referenceEnergyMatrixVelocity_eq U c hab hU hG hH hc C hC hlo hup t ht]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    real_inner_smul_left, ContinuousLinearMap.adjoint_inner_left]

/-- Source-ready strong derivative of the common-domain energy coefficient. -/
theorem referenceGradientEnergyCoefficient_hasDerivAt_curvature (μ : Measure E) (t : ℝ)
    (ht : t ∈ Ioo a b) (D : V →L[ℝ] Lp E 2 μ) (u : V) :
    HasDerivAt (fun s => MovingForms.energyCoefficient
      ((referenceGradientMultiplier U c hab hU hG hH hc C hC hlo hup μ s).comp D) u)
      (MovingForms.variationalRHS
        ((referenceGradientMultiplier U c hab hU hG hH hc C hC hlo hup μ t).comp D)
        ((2 * c t) • referenceHessianMultiplier U c hab hU hG hH hc C hC hlo hup μ t ht
          (referenceGradientMultiplier U c hab hU hG hH hc C hC hlo hup μ t (D u)))) t := by
  rw [← referenceEnergyCoefficientVelocity_eq U c hab hU hG hH hc C hC hlo hup]
  exact referenceGradientEnergyCoefficient_hasDerivAt U c hab hU hG hH hc C hC hlo hup μ t ht D u

end AcceleratedLogConcave.Analysis.Poisson
