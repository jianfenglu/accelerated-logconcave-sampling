import AcceleratedLogConcave.Kinetic.ReferenceChannelLaw

/-! The actual measure-valued reference channel is iterated by weighting the
same coupling at each step with the current input law. No output law or
operator identity is assumed at later times. -/
noncomputable section
open MeasureTheory
set_option autoImplicit false
namespace AcceleratedLogConcave.Kinetic.ReferenceChannelIteration
open Analysis.Poisson
open ReferenceChannelLaw

variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  {μ ν : Measure X} {η : Measure Ω}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
  {p q : Ω → X}

/-- Repeated genuine output laws, with the full current input measure at each
step. The original law may be an arbitrarily dependent joint phase law. -/
def iterateLaw (η : Measure Ω) (μ : Measure X) (p q : Ω → X)
    (ν : Measure X) : ℕ → Measure X
  | 0 => ν
  | n+1 => outputLaw (iterateLaw η μ p q ν n) η μ p q

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure η] in
@[simp] theorem iterateLaw_zero : iterateLaw η μ p q ν 0 = ν := rfl
omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure η] in
@[simp] theorem iterateLaw_succ (n : ℕ) :
    iterateLaw η μ p q ν (n+1) =
      outputLaw (iterateLaw η μ p q ν n) η μ p q := rfl

omit [IsProbabilityMeasure η] in
theorem iterateLaw_probability (hp : MeasurePreserving p η μ)
    (hq : MeasurePreserving q η μ) (hν : ν ≪ μ) (n : ℕ) :
    IsProbabilityMeasure (iterateLaw η μ p q ν n) := by
  induction n with
  | zero => simpa using (inferInstance : IsProbabilityMeasure ν)
  | succ n ih =>
    let : IsProbabilityMeasure (iterateLaw η μ p q ν n) := ih
    exact outputLaw_probability hp hq
      (by
        cases n with
        | zero => simpa using hν
        | succ n => exact outputLaw_absolutelyContinuous hq)

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure η] in
theorem iterateLaw_absolutelyContinuous (hq : MeasurePreserving q η μ)
    (hν : ν ≪ μ) (n : ℕ) : iterateLaw η μ p q ν n ≪ μ := by
  cases n with
  | zero => exact hν
  | succ n => exact outputLaw_absolutelyContinuous hq

/-- Every genuinely constructed iterate is warm, and its centered RN density
is exactly the corresponding power of the density adjoint. -/
theorem iterateLaw_warm_centered (hp : MeasurePreserving p η μ)
    (hq : MeasurePreserving q η μ) {B : ℝ}
    (h : AcceleratedLogConcave.Probability.L2Warm μ ν B) (n : ℕ) :
    ∃ _hw : AcceleratedLogConcave.Probability.L2Warm μ
        (iterateLaw η μ p q ν n)
        (1 + ‖((referenceChannel hp hq).adjoint ^ n)
          (h.centeredDensity : Lp ℝ 2 μ)‖ ^ 2),
      (fun x => ((iterateLaw η μ p q ν n).rnDeriv μ x).toReal - 1) =ᵐ[μ]
        (((referenceChannel hp hq).adjoint ^ n)
          (h.centeredDensity : Lp ℝ 2 μ) : X → ℝ) := by
  let T := (referenceChannel hp hq).adjoint
  induction n with
  | zero =>
    have hbound : AcceleratedLogConcave.Probability.L2Warm μ ν
        (1 + ‖(h.centeredDensity : Lp ℝ 2 μ)‖ ^ 2) := by
      refine ⟨h.absolutelyContinuous, h.integrable_sq, ?_⟩
      have he := h.norm_centeredDensity_sq
      change ‖(h.centeredDensity : Lp ℝ 2 μ)‖ ^ 2 =
        (∫ x, ((ν.rnDeriv μ x).toReal) ^ 2 ∂μ) - 1 at he
      linarith
    have hw : AcceleratedLogConcave.Probability.L2Warm μ
        (iterateLaw η μ p q ν 0)
        (1 + ‖(T ^ 0) (h.centeredDensity : Lp ℝ 2 μ)‖ ^ 2) := by
      simpa [iterateLaw, T] using hbound
    refine ⟨hw, ?_⟩
    simpa [iterateLaw, T] using h.centeredDensity_coe_ae.symm
  | succ n ih =>
    let : IsProbabilityMeasure (iterateLaw η μ p q ν n) :=
      iterateLaw_probability hp hq h.absolutelyContinuous n
    obtain ⟨hw, hcenterAe⟩ := ih
    have hcenter : (hw.centeredDensity : Lp ℝ 2 μ) =
        (T ^ n) (h.centeredDensity : Lp ℝ 2 μ) := by
      apply Lp.ext
      filter_upwards [hw.centeredDensity_coe_ae, hcenterAe] with x hx hy
      exact hx.trans hy
    have hpower : T ((T ^ n) (h.centeredDensity : Lp ℝ 2 μ)) =
        (T ^ (n + 1)) (h.centeredDensity : Lp ℝ 2 μ) := by
      rw [pow_succ', mul_apply_eq_comp]
    have hw' : AcceleratedLogConcave.Probability.L2Warm μ
        (iterateLaw η μ p q ν (n + 1))
        (1 + ‖(T ^ (n + 1)) (h.centeredDensity : Lp ℝ 2 μ)‖ ^ 2) := by
      have hb := output_warm hp hq hw
      rw [hcenter, hpower] at hb
      exact hb
    refine ⟨hw', ?_⟩
    have ha := output_centered_rnDeriv hp hq hw
    rw [hcenter, hpower] at ha
    exact ha

/-- Exact warmness of each measure-valued iterate, with no warmness
certificate postulated for later laws. -/
theorem iterateLaw_warm (hp : MeasurePreserving p η μ)
    (hq : MeasurePreserving q η μ) {B : ℝ}
    (h : AcceleratedLogConcave.Probability.L2Warm μ ν B) (n : ℕ) :
    AcceleratedLogConcave.Probability.L2Warm μ
      (iterateLaw η μ p q ν n)
      (1 + ‖((referenceChannel hp hq).adjoint ^ n)
        (h.centeredDensity : Lp ℝ 2 μ)‖ ^ 2) :=
  (iterateLaw_warm_centered hp hq h n).choose

/-- The centered Radon–Nikodym density of the genuine n-step output measure
is the n-th adjoint power of the original joint input density. -/
theorem iterateLaw_centered_rnDeriv (hp : MeasurePreserving p η μ)
    (hq : MeasurePreserving q η μ) {B : ℝ}
    (h : AcceleratedLogConcave.Probability.L2Warm μ ν B) (n : ℕ) :
    (fun x => ((iterateLaw η μ p q ν n).rnDeriv μ x).toReal - 1) =ᵐ[μ]
      (((referenceChannel hp hq).adjoint ^ n)
        (h.centeredDensity : Lp ℝ 2 μ) : X → ℝ) :=
  (iterateLaw_warm_centered hp hq h n).choose_spec

/-- The same identity as an equality in the actual centered L² space. -/
theorem iterateLaw_centeredDensity (hp : MeasurePreserving p η μ)
    (hq : MeasurePreserving q η μ) {B : ℝ}
    (h : AcceleratedLogConcave.Probability.L2Warm μ ν B) (n : ℕ) :
    let : IsProbabilityMeasure (iterateLaw η μ p q ν n) :=
      iterateLaw_probability hp hq h.absolutelyContinuous n
    ((iterateLaw_warm hp hq h n).centeredDensity : Lp ℝ 2 μ) =
      ((referenceChannel hp hq).adjoint ^ n)
        (h.centeredDensity : Lp ℝ 2 μ) := by
  let : IsProbabilityMeasure (iterateLaw η μ p q ν n) :=
    iterateLaw_probability hp hq h.absolutelyContinuous n
  apply Lp.ext
  filter_upwards [(iterateLaw_warm hp hq h n).centeredDensity_coe_ae,
    iterateLaw_centered_rnDeriv hp hq h n] with x hx hy
  exact hx.trans hy

/-- The probability-event factor one half applies to the actual iterated
output law, not merely to a formal operator expression. -/
theorem iterateLaw_totalVariation_le (hp : MeasurePreserving p η μ)
    (hq : MeasurePreserving q η μ) {B : ℝ}
    (h : AcceleratedLogConcave.Probability.L2Warm μ ν B) (n : ℕ) :
    let : IsProbabilityMeasure (iterateLaw η μ p q ν n) :=
      iterateLaw_probability hp hq h.absolutelyContinuous n
    AcceleratedLogConcave.Probability.totalVariationDistance
      (iterateLaw η μ p q ν n) μ ≤
        ‖((referenceChannel hp hq).adjoint ^ n)
          (h.centeredDensity : Lp ℝ 2 μ)‖ / 2 := by
  let : IsProbabilityMeasure (iterateLaw η μ p q ν n) :=
    iterateLaw_probability hp hq h.absolutelyContinuous n
  have ht := (iterateLaw_warm hp hq h n).totalVariationDistance_le
  simpa only [add_sub_cancel_left, Real.sqrt_sq (norm_nonneg _)] using ht

end AcceleratedLogConcave.Kinetic.ReferenceChannelIteration
