import AcceleratedLogConcave.Analysis.Poisson.ReferenceFlow

/-! Time clamping turns data on a compact positive-time interval into the global
continuous coefficients required by the ODE construction. It preserves every
interior temporal derivative and requires no regularity outside the interval. -/
noncomputable section
open Set Filter Function InnerProductSpace
open scoped Topology
namespace AcceleratedLogConcave.Analysis.Poisson

/-- Extend a family constantly beyond its two endpoint values. -/
def timeExtend {A : Type*} {a b : ℝ} (hab : a ≤ b) (f : ℝ → A) (t : ℝ) : A :=
  f (projIcc a b hab t)

@[simp] theorem timeExtend_eq_of_mem {A : Type*} {a b : ℝ} (hab : a ≤ b)
    (f : ℝ → A) {t : ℝ} (ht : t ∈ Icc a b) : timeExtend hab f t = f t := by
  simp only [timeExtend, projIcc_of_mem _ ht]

theorem timeExtend_eventuallyEq {A : Type*} {a b t : ℝ} (hab : a ≤ b)
    (f : ℝ → A) (ht : t ∈ Ioo a b) : timeExtend hab f =ᶠ[𝓝 t] f := by
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
  exact timeExtend_eq_of_mem hab f hs

/-- Local interval continuity suffices for a globally continuous extension. -/
theorem continuous_timeExtend {A : Type*} [TopologicalSpace A] {a b : ℝ}
    (hab : a ≤ b) (f : ℝ → A) (hf : ContinuousOn f (Icc a b)) :
    Continuous (timeExtend hab f) :=
  hf.comp_continuous
    (continuous_subtype_val.comp (continuous_projIcc (h := hab)))
    (fun t => (projIcc a b hab t).property)

/-- Joint continuity on the closed time strip suffices for global joint continuity. -/
theorem continuous_uncurry_timeExtend {X A : Type*} [TopologicalSpace X]
    [TopologicalSpace A] {a b : ℝ} (hab : a ≤ b) (f : ℝ → X → A)
    (hf : ContinuousOn (uncurry f) (Icc a b ×ˢ (univ : Set X))) :
    Continuous (uncurry (timeExtend hab f)) :=
  hf.comp_continuous
    (((continuous_subtype_val.comp (continuous_projIcc (h := hab))).comp continuous_fst).prodMk
      continuous_snd)
    (fun p => ⟨(projIcc a b hab p.1).property, mem_univ _⟩)

/-- Clamping does not change an interior strong derivative. -/
theorem hasDerivAt_timeExtend {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a b t : ℝ} (hab : a ≤ b) (f : ℝ → F) (f' : F) (ht : t ∈ Ioo a b)
    (hf : HasDerivAt f f' t) : HasDerivAt (timeExtend hab f) f' t :=
  hf.congr_of_eventuallyEq (timeExtend_eventuallyEq hab f ht)

/-- The original interior derivative can also be recovered from the extended family. -/
theorem hasDerivAt_of_timeExtend {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a b t : ℝ} (hab : a ≤ b) (f : ℝ → F) (f' : F) (ht : t ∈ Ioo a b)
    (hf : HasDerivAt (timeExtend hab f) f' t) : HasDerivAt f f' t :=
  hf.congr_of_eventuallyEq (timeExtend_eventuallyEq hab f ht).symm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {a b : ℝ} (hab : a ≤ b) (U : ℝ → E → ℝ)

omit [FiniteDimensional ℝ E] in
/-- The extension needs spatial C2 regularity only at times in the chosen interval. -/
theorem timeExtend_contDiff (hU : ∀ t ∈ Icc a b, ContDiff ℝ 2 (U t)) (t : ℝ) :
    ContDiff ℝ 2 (timeExtend hab U t) :=
  hU (projIcc a b hab t) (projIcc a b hab t).property

/-- The actual extended gradient is jointly continuous from local source data. -/
theorem timeExtend_gradient_continuous
    (hG : ContinuousOn (uncurry (fun t => gradient (U t)))
      (Icc a b ×ˢ (univ : Set E))) :
    Continuous (uncurry (fun t => gradient (timeExtend hab U t))) :=
  continuous_uncurry_timeExtend hab (fun t => gradient (U t)) hG

/-- The actual extended Hessian is jointly continuous from local source data. -/
theorem timeExtend_hessian_continuous
    (hH : ContinuousOn (uncurry (fun t => hessianOperator (U t)))
      (Icc a b ×ˢ (univ : Set E))) :
    Continuous (uncurry (fun t => hessianOperator (timeExtend hab U t))) :=
  continuous_uncurry_timeExtend hab (fun t => hessianOperator (U t)) hH

end AcceleratedLogConcave.Analysis.Poisson
