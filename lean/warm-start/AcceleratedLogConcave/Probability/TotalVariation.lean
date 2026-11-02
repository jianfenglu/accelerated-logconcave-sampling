import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic.Linarith

/-!
# Total variation of probability laws

For probability measures, `totalVariationDistance P Q` is the supremum of
`|P A - Q A|` over measurable events, equal to half the L¹ density distance.
The probability hypotheses keep this real supremum bounded.
-/

open MeasureTheory

namespace AcceleratedLogConcave.Probability

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Total variation distance, normalized as the supremum over measurable events. -/
noncomputable def totalVariationDistance (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] : ℝ :=
  sSup {r : ℝ | ∃ s : Set Ω, MeasurableSet s ∧ r = |P.real s - Q.real s|}

private theorem eventDistances_nonempty (P Q : Measure Ω) :
    Set.Nonempty {r : ℝ | ∃ s : Set Ω, MeasurableSet s ∧ r = |P.real s - Q.real s|} := by
  exact ⟨0, ∅, MeasurableSet.empty, by simp⟩

private theorem abs_measureReal_sub_le_one (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (s : Set Ω) :
    |P.real s - Q.real s| ≤ 1 := by
  have hP0 : 0 ≤ P.real s := measureReal_nonneg
  have hQ0 : 0 ≤ Q.real s := measureReal_nonneg
  have hP1 : P.real s ≤ 1 := measureReal_le_one
  have hQ1 : Q.real s ≤ 1 := measureReal_le_one
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem eventDistances_bddAbove (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    BddAbove {r : ℝ | ∃ s : Set Ω, MeasurableSet s ∧ r = |P.real s - Q.real s|} := by
  refine ⟨1, ?_⟩
  rintro r ⟨s, _hs, rfl⟩
  exact abs_measureReal_sub_le_one P Q s

theorem totalVariationDistance_le_of_forall (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (C : ℝ)
    (h : ∀ s : Set Ω, MeasurableSet s → |P.real s - Q.real s| ≤ C) :
    totalVariationDistance P Q ≤ C := by
  apply csSup_le (eventDistances_nonempty P Q)
  rintro r ⟨s, hs, rfl⟩
  exact h s hs

theorem abs_measureReal_sub_le_totalVariationDistance (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (s : Set Ω) (hs : MeasurableSet s) :
    |P.real s - Q.real s| ≤ totalVariationDistance P Q :=
  le_csSup (eventDistances_bddAbove P Q) ⟨s, hs, rfl⟩

theorem totalVariationDistance_nonneg (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    0 ≤ totalVariationDistance P Q := by
  simpa using abs_measureReal_sub_le_totalVariationDistance P Q ∅ MeasurableSet.empty

theorem totalVariationDistance_le_one (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    totalVariationDistance P Q ≤ 1 :=
  totalVariationDistance_le_of_forall P Q 1 (fun s _ ↦ abs_measureReal_sub_le_one P Q s)

@[simp]
theorem totalVariationDistance_self (P : Measure Ω) [IsProbabilityMeasure P] :
    totalVariationDistance P P = 0 := by
  apply le_antisymm _ (totalVariationDistance_nonneg P P)
  apply totalVariationDistance_le_of_forall
  intro s _
  simp

theorem totalVariationDistance_comm (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    totalVariationDistance P Q = totalVariationDistance Q P := by
  apply le_antisymm
  · apply totalVariationDistance_le_of_forall
    intro s hs
    rw [abs_sub_comm]
    exact abs_measureReal_sub_le_totalVariationDistance Q P s hs
  · apply totalVariationDistance_le_of_forall
    intro s hs
    rw [abs_sub_comm]
    exact abs_measureReal_sub_le_totalVariationDistance P Q s hs

theorem totalVariationDistance_triangle (P Q R : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure R] :
    totalVariationDistance P R ≤ totalVariationDistance P Q + totalVariationDistance Q R := by
  apply totalVariationDistance_le_of_forall
  intro s hs
  exact (abs_sub_le (P.real s) (Q.real s) (R.real s)).trans
    (add_le_add (abs_measureReal_sub_le_totalVariationDistance P Q s hs)
      (abs_measureReal_sub_le_totalVariationDistance Q R s hs))

theorem totalVariationDistance_map_le {β : Type*} [MeasurableSpace β]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f : Ω → β) (hf : Measurable f) :
    totalVariationDistance (P.map f) (Q.map f) ≤ totalVariationDistance P Q := by
  apply totalVariationDistance_le_of_forall
  intro s hs
  simpa only [measureReal_def, Measure.map_apply hf hs] using
    abs_measureReal_sub_le_totalVariationDistance P Q (f ⁻¹' s) (hf hs)

/-- Mathlib's `Measure.integrable_toReal_rnDeriv`, in the argument order used below. -/
private theorem integrable_toReal_rnDeriv (ρ P : Measure Ω) [IsFiniteMeasure P] :
    Integrable (fun x ↦ (P.rnDeriv ρ x).toReal) ρ :=
  Measure.integrable_toReal_rnDeriv

/-- On probability measures the event-supremum definition is the half-L¹ density formula. -/
theorem totalVariationDistance_eq_integral_abs (P Q ρ : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [SigmaFinite ρ]
    (hP : P ≪ ρ) (hQ : Q ≪ ρ) :
    totalVariationDistance P Q =
      (∫ x, |(P.rnDeriv ρ x).toReal - (Q.rnDeriv ρ x).toReal| ∂ρ) / 2 := by
  classical
  let d := fun x ↦ (P.rnDeriv ρ x).toReal - (Q.rnDeriv ρ x).toReal
  have hd : Integrable d ρ := (integrable_toReal_rnDeriv ρ P).sub (integrable_toReal_rnDeriv ρ Q)
  have hmd : Measurable d := (Measure.measurable_rnDeriv P ρ).ennreal_toReal.sub
    (Measure.measurable_rnDeriv Q ρ).ennreal_toReal
  have hev (s : Set Ω) : (∫ x in s, d x ∂ρ) = P.real s - Q.real s := by
    change (∫ x in s, (P.rnDeriv ρ x).toReal - (Q.rnDeriv ρ x).toReal ∂ρ) = _
    rw [integral_sub (integrable_toReal_rnDeriv ρ P).integrableOn
      (integrable_toReal_rnDeriv ρ Q).integrableOn,
      Measure.setIntegral_toReal_rnDeriv hP, Measure.setIntegral_toReal_rnDeriv hQ]
  have hz : (∫ x, d x ∂ρ) = 0 := by simpa using hev Set.univ
  change totalVariationDistance P Q = (∫ x, |d x| ∂ρ) / 2
  apply le_antisymm
  · apply totalVariationDistance_le_of_forall
    intro s hs
    have h₁ := abs_integral_le_integral_abs (f := d) (μ := ρ.restrict s)
    have h₂ := abs_integral_le_integral_abs (f := d) (μ := ρ.restrict sᶜ)
    have hsums := integral_add_compl hs hd.abs
    rw [hev s] at h₁
    have hc' : |∫ x in sᶜ, d x ∂ρ| = |P.real s - Q.real s| := by
      rw [setIntegral_compl hs hd, hz, zero_sub, abs_neg, hev s]
    rw [hc'] at h₂
    linarith
  · let A := {x | 0 ≤ d x}
    have hA : MeasurableSet A := measurableSet_le measurable_const hmd
    have hp : (∫ x, (d x)⁺ ∂ρ) = ∫ x in A, d x ∂ρ := by
      rw [← integral_indicator hA]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        by_cases hx : 0 ≤ d x
        · simp [A, hx, PosPart.posPart]
        · simp [A, hx, PosPart.posPart, max_eq_right (le_of_not_ge hx)]
    have habs := integral_abs_eq_two_mul_integral_posPart_sub_integral hd
    rw [hz, sub_zero, hp, hev A] at habs
    have hbound := (le_abs_self (P.real A - Q.real A)).trans
      (abs_measureReal_sub_le_totalVariationDistance P Q A hA)
    linarith

end AcceleratedLogConcave.Probability
