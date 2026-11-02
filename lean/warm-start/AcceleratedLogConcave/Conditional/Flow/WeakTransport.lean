import AcceleratedLogConcave.Analysis.Poisson.ReferenceTransportLaw

/-!
# Exact transport from the weak continuity equation

The equation is tested against compactly supported time-dependent C1 tests.
It is an equation for the actual measures, without an assumed flow or density.
Backward tests constructed from the OAI complete flow identify its marginals.
-/

noncomputable section
open Set Function MeasureTheory
open scoped Topology NNReal

namespace AcceleratedLogConcave.Conditional
open Analysis.Poisson OAI.LogConcaveSampling.GlobalODE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Weak continuity on a closed interval, with the time derivative placed on
an arbitrary compact C1 space-time test. Endpoint continuity is included. -/
def HasWeakContinuityEquationOn (μ : ℝ → Measure E) (v : ℝ → E → E)
    (a b : ℝ) : Prop :=
  ∀ ψ : ℝ × E → ℝ, Continuous ψ →
    (∀ p, p.1 ∈ Ioo a b → ContDiffAt ℝ 1 ψ p) →
    (∃ K : Set E, IsCompact K ∧ ∀ t x, x ∉ K → ψ (t, x) = 0) →
    ContinuousOn (fun t => ∫ x, ψ (t, x) ∂μ t) (Icc a b) ∧
      ∀ t ∈ Ioo a b,
        HasDerivAt (fun s => ∫ x, ψ (s, x) ∂μ s)
          (∫ x, fderiv ℝ ψ (t, x) (1, v t x) ∂μ t) t

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Only the velocity at interior times enters the weak equation. -/
theorem HasWeakContinuityEquationOn.congr_velocity
    {μ : ℝ → Measure E} {v w : ℝ → E → E} {a b : ℝ}
    (h : HasWeakContinuityEquationOn μ v a b)
    (heq : ∀ t ∈ Ioo a b, ∀ x, v t x = w t x) :
    HasWeakContinuityEquationOn μ w a b := by
  intro ψ hc hd hK
  obtain ⟨hcont, hderiv⟩ := h ψ hc hd hK
  refine ⟨hcont, fun t ht => ?_⟩
  simpa only [heq t ht] using hderiv t ht

/-- A weak continuity equation identifies the endpoint pushforward of the
constructed flow. The proof uses compact C1 tests and ODE uniqueness. -/
theorem measurePreserving_flow_of_weak_continuity
    {a b : ℝ} (hab : a < b) {v : ℝ → E → E}
    (hv : Continuous (uncurry v)) {C : ℝ≥0}
    (hL : ∀ t ∈ Icc a b, LipschitzWith C (v t))
    {D : ℝ → E → E →L[ℝ] E} (hD : Continuous (uncurry D))
    (hvd : ∀ t x, HasFDerivAt (v t) (D t x) x)
    (μ : ℝ → Measure E) [∀ t, IsFiniteMeasure (μ t)]
    (hCE : HasWeakContinuityEquationOn μ v a b) :
    MeasurePreserving
      (flowHomeomorph hL hv ⟨a, le_rfl, hab.le⟩ ⟨b, hab.le, le_rfl⟩)
      (μ a) (μ b) := by
  let T : Icc a b := ⟨b, hab.le, le_rfl⟩
  let S : Icc a b := ⟨a, le_rfl, hab.le⟩
  refine ⟨(flowHomeomorph hL hv S T).continuous.measurable, ?_⟩
  apply measure_eq_of_compact_contDiff
  intro φ hφ hφK
  rw [integral_map (flowHomeomorph hL hv S T).continuous.measurable.aemeasurable
    hφ.continuous.aestronglyMeasurable]
  let ψ := backwardTest hab.le hv hL T φ
  obtain ⟨hc, hd⟩ := hCE ψ (backwardTest_continuous hab.le hv hL T hφ.continuous)
    (backwardTest_contDiffAt_one hab.le hv hL hD hvd T hφ)
    (backwardTest_common_compact_support hab.le hv hL T hφK)
  have hz (t : ℝ) (ht : t ∈ Ioo a b) (x : E) :
      fderiv ℝ ψ (t, x) (1, v t x) = 0 :=
    backwardTest_material_zero hab.le hv hL hD hvd T hφ.differentiable_one (t, x) ht
  have hd0 (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (fun s => ∫ x, ψ (s, x) ∂μ s) 0 t := by
    simpa only [hz t ht, integral_zero] using hd t ht
  obtain ⟨t, ht, he⟩ := exists_deriv_eq_slope
    (fun s => ∫ x, ψ (s, x) ∂μ s) hab hc
    (fun t ht => (hd0 t ht).differentiableAt.differentiableWithinAt)
  rw [(hd0 t ht).deriv] at he
  have heq : (∫ x, ψ (b, x) ∂μ b) = ∫ x, ψ (a, x) ∂μ a :=
    sub_eq_zero.mp ((div_eq_zero_iff).mp he.symm |>.resolve_right (sub_ne_zero.mpr hab.ne'))
  have ha : (fun x => ψ (a, x)) = fun x => φ (flowHomeomorph hL hv S T x) := by
    funext x
    dsimp [ψ]
    rw [backwardTest_eq, projIcc_of_mem hab.le S.2]
    rfl
  have hb : (fun x => ψ (b, x)) = φ := by
    funext x
    dsimp [ψ]
    rw [backwardTest_eq, projIcc_of_mem hab.le T.2, flow_initial]
  rw [ha, hb] at heq
  exact heq.symm

end AcceleratedLogConcave.Conditional
