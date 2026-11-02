import AcceleratedLogConcave.Analysis.Poisson.Solvability

noncomputable section
open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace

namespace AcceleratedLogConcave.Analysis.Poisson

section Center
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

/-- The orthogonal centering map on scalar weighted L2. -/
def centerForcing : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  ContinuousLinearMap.id ℝ _ - (mean μ).smulRight (oneL2 μ)

@[simp] theorem centerForcing_apply (f : Lp ℝ 2 μ) :
    centerForcing μ f = f - mean μ f • oneL2 μ := rfl

@[simp] theorem mean_centerForcing (f : Lp ℝ 2 μ) : mean μ (centerForcing μ f) = 0 := by
  simp only [centerForcing_apply, map_sub, map_smul, mean_oneL2, smul_eq_mul, mul_one, sub_self]

@[simp] theorem centerForcing_const (c : ℝ) : centerForcing μ (c • oneL2 μ) = 0 := by
  simp only [map_smul, centerForcing_apply, mean_oneL2, one_smul, sub_self, smul_zero]

theorem norm_centerForcing_le (f : Lp ℝ 2 μ) : ‖centerForcing μ f‖ ≤ ‖f‖ := by
  have hone : inner ℝ (oneL2 μ) (oneL2 μ) = 1 := mean_oneL2 μ
  have hmean : inner ℝ (oneL2 μ) f = mean μ f := rfl
  have hmean' : inner ℝ f (oneL2 μ) = mean μ f := (real_inner_comm _ _).trans hmean
  have hid : ‖centerForcing μ f‖ ^ 2 = ‖f‖ ^ 2 - (mean μ f) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, centerForcing_apply]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      RCLike.conj_to_real, hone, hmean, hmean', real_inner_self_eq_norm_sq]
    ring
  nlinarith [sq_nonneg (mean μ f), norm_nonneg f, norm_nonneg (centerForcing μ f)]
end Center

section Weighted
open WeightedGradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [IsProbabilityMeasure μ] (V : E → ℝ)
  (hV : ContDiff ℝ 2 V) (hI : Integrable (fun x => Real.exp (-V x)))
  (hμ : μ = volume.tilted (fun x => -V x))
  (m L : ℝ) (hm : 0 < m)
  (hlower : ∀ x a, m * ‖a‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x a a)
  (hupper : ∀ x a, fderiv ℝ (fderiv ℝ V) x a a ≤ L * ‖a‖ ^ 2)

/-- The genuine centered weak Poisson solution for arbitrary scalar L2 forcing. -/
def poissonSolution (f : Lp ℝ 2 μ) : Sobolev μ V (hV.of_le (by norm_num)) hI hμ :=
  (existsUnique_weak_poisson μ V hV hI hμ m L hm hlower hupper (centerForcing μ f)
    ((mean_apply μ _).symm.trans (mean_centerForcing μ f))).choose

variable {μ V hV hI hμ m L hm hlower hupper}

theorem poissonSolution_spec (f : Lp ℝ 2 μ) :
    (∫ x, (poissonSolution μ V hV hI hμ m L hm hlower hupper f : Lp ℝ 2 μ) x ∂μ) = 0 ∧
    ∀ v : Sobolev μ V (hV.of_le (by norm_num)) hI hμ,
      inner ℝ (closedGradient μ V (hV.of_le (by norm_num)) hI hμ
        (poissonSolution μ V hV hI hμ m L hm hlower hupper f))
        (closedGradient μ V (hV.of_le (by norm_num)) hI hμ v) =
      inner ℝ (centerForcing μ f) (v : Lp ℝ 2 μ) :=
  (existsUnique_weak_poisson μ V hV hI hμ m L hm hlower hupper (centerForcing μ f)
    ((mean_apply μ _).symm.trans (mean_centerForcing μ f))).choose_spec.1

private theorem poissonSolution_unique (f : Lp ℝ 2 μ)
    (u : Sobolev μ V (hV.of_le (by norm_num)) hI hμ)
    (hu : (∫ x, (u : Lp ℝ 2 μ) x ∂μ) = 0)
    (he : ∀ v : Sobolev μ V (hV.of_le (by norm_num)) hI hμ,
      inner ℝ (closedGradient μ V (hV.of_le (by norm_num)) hI hμ u)
        (closedGradient μ V (hV.of_le (by norm_num)) hI hμ v) =
        inner ℝ (centerForcing μ f) (v : Lp ℝ 2 μ)) :
    u = poissonSolution μ V hV hI hμ m L hm hlower hupper f :=
  (existsUnique_weak_poisson μ V hV hI hμ m L hm hlower hupper (centerForcing μ f)
    ((mean_apply μ _).symm.trans (mean_centerForcing μ f))).choose_spec.2 u ⟨hu, he⟩

theorem poissonSolution_add (f g : Lp ℝ 2 μ) :
    poissonSolution μ V hV hI hμ m L hm hlower hupper (f + g) =
      poissonSolution μ V hV hI hμ m L hm hlower hupper f +
      poissonSolution μ V hV hI hμ m L hm hlower hupper g := by
  symm
  apply poissonSolution_unique
  · rw [← mean_apply]
    change mean μ ((_ : Lp ℝ 2 μ) + (_ : Lp ℝ 2 μ)) = 0
    rw [map_add, mean_apply, mean_apply, (poissonSolution_spec f).1,
      (poissonSolution_spec g).1, add_zero]
  · intro v
    rw [LinearPMap.map_add, inner_add_left, (poissonSolution_spec f).2 v,
      (poissonSolution_spec g).2 v, map_add, inner_add_left]

theorem poissonSolution_smul (c : ℝ) (f : Lp ℝ 2 μ) :
    poissonSolution μ V hV hI hμ m L hm hlower hupper (c • f) =
      c • poissonSolution μ V hV hI hμ m L hm hlower hupper f := by
  symm
  apply poissonSolution_unique
  · rw [← mean_apply]
    change mean μ (c • (_ : Lp ℝ 2 μ)) = 0
    rw [map_smul, mean_apply, (poissonSolution_spec f).1, smul_zero]
  · intro v
    rw [LinearPMap.map_smul, inner_smul_left, (poissonSolution_spec f).2 v,
      map_smul, inner_smul_left]

theorem poissonSolution_norm_le (f : Lp ℝ 2 μ) :
    ‖(poissonSolution μ V hV hI hμ m L hm hlower hupper f : Lp ℝ 2 μ)‖ ≤
      m⁻¹ * ‖f‖ := by
  have hs := poissonSolution_spec (μ := μ) (V := V) (hV := hV) (hI := hI)
    (hμ := hμ) (m := m) (L := L) (hm := hm) (hlower := hlower) (hupper := hupper) f
  have hb := (weak_poisson_estimates μ V hV hI hμ m L hm hlower hupper
    (centerForcing μ f) _ hs.1 hs.2).2.1
  rw [← div_eq_inv_mul, le_div_iff₀ hm]
  exact le_trans (by simpa [mul_comm] using hb) (norm_centerForcing_le μ f)

variable (μ V hV hI hμ m L hm hlower hupper)

/-- The scalar Poisson inverse, extended by zero on the constants. -/
def poissonInverse : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun f => (poissonSolution μ V hV hI hμ m L hm hlower hupper f : Lp ℝ 2 μ)
      map_add' := fun f g => congrArg Subtype.val (poissonSolution_add f g)
      map_smul' := fun c f => congrArg Subtype.val (poissonSolution_smul c f) }
    m⁻¹ (fun f => poissonSolution_norm_le f)

@[simp] theorem poissonInverse_apply (f : Lp ℝ 2 μ) :
    poissonInverse μ V hV hI hμ m L hm hlower hupper f =
      (poissonSolution μ V hV hI hμ m L hm hlower hupper f : Lp ℝ 2 μ) := rfl

theorem poissonInverse_norm_le :
    ‖poissonInverse μ V hV hI hμ m L hm hlower hupper‖ ≤ m⁻¹ :=
  LinearMap.mkContinuous_norm_le _ (inv_nonneg.mpr hm.le) _

theorem poissonInverse_centered (f : Lp ℝ 2 μ) :
    mean μ (poissonInverse μ V hV hI hμ m L hm hlower hupper f) = 0 := by
  rw [poissonInverse_apply, mean_apply]
  exact (poissonSolution_spec f).1

@[simp] theorem poissonInverse_const (c : ℝ) :
    poissonInverse μ V hV hI hμ m L hm hlower hupper (c • oneL2 μ) = 0 := by
  have hz : (0 : Sobolev μ V (hV.of_le (by norm_num)) hI hμ) =
      poissonSolution μ V hV hI hμ m L hm hlower hupper (c • oneL2 μ) := by
    apply poissonSolution_unique
    · simp
    · intro v
      rw [LinearPMap.map_zero, centerForcing_const]
      simp
  rw [poissonInverse_apply, ← hz]
  rfl


include hm hlower hupper in
/-- Vector forcing has a unique centered solution on the entire closed gradient domain. -/
theorem existsUnique_gradient_poisson (f : Lp E 2 μ) :
    ∃! u : Sobolev μ V (hV.of_le (by norm_num)) hI hμ,
      (∫ x, (u : Lp ℝ 2 μ) x ∂μ) = 0 ∧
      ∀ v : Sobolev μ V (hV.of_le (by norm_num)) hI hμ,
        inner ℝ (closedGradient μ V (hV.of_le (by norm_num)) hI hμ u)
          (closedGradient μ V (hV.of_le (by norm_num)) hI hμ v) =
        inner ℝ f (closedGradient μ V (hV.of_le (by norm_num)) hI hμ v) := by
  obtain ⟨u, hu, huniq⟩ := existsUnique_centered_gradient_solution
    (closedGradient μ V (hV.of_le (by norm_num)) hI hμ)
    (closedGradient_isClosed μ V (hV.of_le (by norm_num)) hI hμ)
    (mean μ) hm (fun u hu => Gibbs.closedGradient_poincare
      μ V hV hI hμ m L hm hlower hupper u ((mean_apply μ u).symm.trans hu)) f
  refine ⟨u, ⟨(mean_apply μ u).symm.trans hu.1, ?_⟩, ?_⟩
  · intro v
    obtain ⟨w, hw, hDw, _⟩ := exists_centered_subtract μ V (hV.of_le (by norm_num)) hI hμ v
    have he := hu.2 w ((mean_apply μ w).trans hw)
    simpa only [hDw] using he
  · intro w hw
    exact huniq w ⟨(mean_apply μ w).trans hw.1, fun v _ => hw.2 v⟩

/-- The vector variational solution uses arbitrary L2 vector data without differentiation. -/
def vectorPoissonSolution (f : Lp E 2 μ) : Sobolev μ V (hV.of_le (by norm_num)) hI hμ :=
  (existsUnique_gradient_poisson μ V hV hI hμ m L hm hlower hupper f).choose

variable {μ V hV hI hμ m L hm hlower hupper}

theorem vectorPoissonSolution_spec (f : Lp E 2 μ) :
    (∫ x, (vectorPoissonSolution μ V hV hI hμ m L hm hlower hupper f : Lp ℝ 2 μ) x ∂μ) = 0 ∧
    ∀ v : Sobolev μ V (hV.of_le (by norm_num)) hI hμ,
      inner ℝ (closedGradient μ V (hV.of_le (by norm_num)) hI hμ
        (vectorPoissonSolution μ V hV hI hμ m L hm hlower hupper f))
        (closedGradient μ V (hV.of_le (by norm_num)) hI hμ v) =
      inner ℝ f (closedGradient μ V (hV.of_le (by norm_num)) hI hμ v) :=
  (existsUnique_gradient_poisson μ V hV hI hμ m L hm hlower hupper f).choose_spec.1

private theorem vectorPoissonSolution_unique (f : Lp E 2 μ)
    (u : Sobolev μ V (hV.of_le (by norm_num)) hI hμ)
    (hu : (∫ x, (u : Lp ℝ 2 μ) x ∂μ) = 0)
    (he : ∀ v : Sobolev μ V (hV.of_le (by norm_num)) hI hμ,
      inner ℝ (closedGradient μ V (hV.of_le (by norm_num)) hI hμ u)
        (closedGradient μ V (hV.of_le (by norm_num)) hI hμ v) =
        inner ℝ f (closedGradient μ V (hV.of_le (by norm_num)) hI hμ v)) :
    u = vectorPoissonSolution μ V hV hI hμ m L hm hlower hupper f :=
  (existsUnique_gradient_poisson μ V hV hI hμ m L hm hlower hupper f).choose_spec.2 u ⟨hu, he⟩

theorem vectorPoissonSolution_add (f g : Lp E 2 μ) :
    vectorPoissonSolution μ V hV hI hμ m L hm hlower hupper (f + g) =
      vectorPoissonSolution μ V hV hI hμ m L hm hlower hupper f +
      vectorPoissonSolution μ V hV hI hμ m L hm hlower hupper g := by
  symm
  apply vectorPoissonSolution_unique
  · rw [← mean_apply]
    change mean μ ((_ : Lp ℝ 2 μ) + (_ : Lp ℝ 2 μ)) = 0
    rw [map_add, mean_apply, mean_apply, (vectorPoissonSolution_spec f).1,
      (vectorPoissonSolution_spec g).1, add_zero]
  · intro v
    rw [LinearPMap.map_add, inner_add_left, (vectorPoissonSolution_spec f).2 v,
      (vectorPoissonSolution_spec g).2 v, inner_add_left]

theorem vectorPoissonSolution_smul (c : ℝ) (f : Lp E 2 μ) :
    vectorPoissonSolution μ V hV hI hμ m L hm hlower hupper (c • f) =
      c • vectorPoissonSolution μ V hV hI hμ m L hm hlower hupper f := by
  symm
  apply vectorPoissonSolution_unique
  · rw [← mean_apply]
    change mean μ (c • (_ : Lp ℝ 2 μ)) = 0
    rw [map_smul, mean_apply, (vectorPoissonSolution_spec f).1, smul_zero]
  · intro v
    rw [LinearPMap.map_smul, inner_smul_left, (vectorPoissonSolution_spec f).2 v,
      inner_smul_left]

theorem vectorPoissonSolution_estimates (f : Lp E 2 μ) :
    ‖closedGradient μ V (hV.of_le (by norm_num)) hI hμ
      (vectorPoissonSolution μ V hV hI hμ m L hm hlower hupper f)‖ ≤ ‖f‖ ∧
    m * ‖(vectorPoissonSolution μ V hV hI hμ m L hm hlower hupper f : Lp ℝ 2 μ)‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  let u := vectorPoissonSolution μ V hV hI hμ m L hm hlower hupper f
  let D := closedGradient μ V (hV.of_le (by norm_num)) hI hμ
  have hs := vectorPoissonSolution_spec (μ := μ) (V := V) (hV := hV) (hI := hI)
    (hμ := hμ) (m := m) (L := L) (hm := hm) (hlower := hlower) (hupper := hupper) f
  have he := hs.2 u
  rw [real_inner_self_eq_norm_sq] at he
  have hcs := real_inner_le_norm f (D u)
  have hg : ‖D u‖ ≤ ‖f‖ := by
    by_cases hz : ‖D u‖ = 0
    · simp only [hz, norm_nonneg]
    · have hp : 0 < ‖D u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      nlinarith
  refine ⟨hg, ?_⟩
  have hp := Gibbs.closedGradient_poincare μ V hV hI hμ m L hm hlower hupper u hs.1
  have hn := norm_nonneg (D u)
  nlinarith


theorem vectorPoissonSolution_norm_le (f : Lp E 2 μ) :
    ‖(vectorPoissonSolution μ V hV hI hμ m L hm hlower hupper f : Lp ℝ 2 μ)‖ ≤
      (Real.sqrt m)⁻¹ * ‖f‖ := by
  rw [← div_eq_inv_mul, le_div_iff₀ (Real.sqrt_pos.mpr hm)]
  apply (sq_le_sq₀ (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg m)) (norm_nonneg f)).mp
  rw [mul_pow, Real.sq_sqrt hm.le, mul_comm]
  exact (vectorPoissonSolution_estimates f).2

variable (μ V hV hI hμ m L hm hlower hupper)

/-- The bounded inverse-divergence map defined by its full-domain variational equation. -/
def vectorPoissonInverse : Lp E 2 μ →L[ℝ] Lp ℝ 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun f => (vectorPoissonSolution μ V hV hI hμ m L hm hlower hupper f : Lp ℝ 2 μ)
      map_add' := fun f g => congrArg Subtype.val (vectorPoissonSolution_add f g)
      map_smul' := fun c f => congrArg Subtype.val (vectorPoissonSolution_smul c f) }
    (Real.sqrt m)⁻¹ (fun f => vectorPoissonSolution_norm_le f)

@[simp] theorem vectorPoissonInverse_apply (f : Lp E 2 μ) :
    vectorPoissonInverse μ V hV hI hμ m L hm hlower hupper f =
      (vectorPoissonSolution μ V hV hI hμ m L hm hlower hupper f : Lp ℝ 2 μ) := rfl

theorem vectorPoissonInverse_norm_le :
    ‖vectorPoissonInverse μ V hV hI hμ m L hm hlower hupper‖ ≤ (Real.sqrt m)⁻¹ :=
  LinearMap.mkContinuous_norm_le _ (inv_nonneg.mpr (Real.sqrt_nonneg m)) _

/-- The bounded map taking vector forcing to the gradient of its variational solution. -/
def weightedGradientProjection : Lp E 2 μ →L[ℝ] Lp E 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun f => closedGradient μ V (hV.of_le (by norm_num)) hI hμ
        (vectorPoissonSolution μ V hV hI hμ m L hm hlower hupper f)
      map_add' := fun f g => by rw [vectorPoissonSolution_add, LinearPMap.map_add]
      map_smul' := fun c f => by rw [vectorPoissonSolution_smul, LinearPMap.map_smul]; rfl }
    1 (fun f => by
      change ‖closedGradient μ V (hV.of_le (by norm_num)) hI hμ
        (vectorPoissonSolution μ V hV hI hμ m L hm hlower hupper f)‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using (vectorPoissonSolution_estimates f).1)

@[simp] theorem weightedGradientProjection_apply (f : Lp E 2 μ) :
    weightedGradientProjection μ V hV hI hμ m L hm hlower hupper f =
      closedGradient μ V (hV.of_le (by norm_num)) hI hμ
        (vectorPoissonSolution μ V hV hI hμ m L hm hlower hupper f) := rfl

theorem weightedGradientProjection_norm_le :
    ‖weightedGradientProjection μ V hV hI hμ m L hm hlower hupper‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end Weighted
end AcceleratedLogConcave.Analysis.Poisson
