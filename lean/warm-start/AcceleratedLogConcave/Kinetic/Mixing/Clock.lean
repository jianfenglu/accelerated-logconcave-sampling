import AcceleratedLogConcave.Kinetic.Mixing.Energy
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Strong averaging of the actual stopping-time operators. Only integrability
on each fixed input is required; operator-norm measurability is not assumed. -/
noncomputable section
open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (T : Ω → H →L[ℝ] H)
  (hI : ∀ f, Integrable (fun r => T r f) μ)
  (hT : ∀ r, ‖T r‖ ≤ 1)

/-- The actual strong average over the independently drawn clock. -/
def clockAverage : H →L[ℝ] H :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ r, T r f ∂μ
      map_add' := fun f g => by
        simp only [map_add]
        exact integral_add (hI f) (hI g)
      map_smul' := fun c f => by
        simp only [map_smul]
        exact integral_smul c _ }
    1 (fun f => by
      have hn : ∀ᵐ r ∂μ, ‖T r f‖ ≤ ‖f‖ := Filter.Eventually.of_forall fun r =>
        ((T r).le_opNorm f).trans (by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right (hT r) (norm_nonneg f))
      simpa using norm_integral_le_of_norm_le_const hn)

omit [CompleteSpace H] in
@[simp] theorem clockAverage_apply (f : H) :
    clockAverage μ T hI hT f = ∫ r, T r f ∂μ := rfl

omit [CompleteSpace H] in
theorem clockAverage_norm_le : ‖clockAverage μ T hI hT‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  have hn : ∀ᵐ r ∂μ, ‖T r f‖ ≤ ‖f‖ := Filter.Eventually.of_forall fun r =>
    ((T r).le_opNorm f).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hT r) (norm_nonneg f))
  simpa only [clockAverage_apply, probReal_univ, mul_one, one_mul] using
    norm_integral_le_of_norm_le_const hn

/-- Exact clock expectation identity for the constructed average. -/
theorem clockAverage_pairing (f g : H) :
    inner ℝ f (clockAverage μ T hI hT g) = ∫ r, inner ℝ f (T r g) ∂μ :=
  ((innerSL ℝ f).integral_comp_comm (hI g)).symm

/-- The actual adjoint equals the strong average of the actual component
adjoints when that family is strongly integrable on each input. -/
theorem clockAverage_adjoint
    (hIa : ∀ f, Integrable (fun r => (T r).adjoint f) μ) :
    (clockAverage μ T hI hT).adjoint =
      clockAverage μ (fun r => (T r).adjoint) hIa
        (fun r => by simpa only [ContinuousLinearMap.adjoint.norm_map] using hT r) := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℝ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_right, real_inner_comm,
    clockAverage_pairing, clockAverage_pairing]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun r => by
    change inner ℝ f (T r g) = inner ℝ g ((T r).adjoint f)
    rw [ContinuousLinearMap.adjoint_inner_right, real_inner_comm]

/-- Linear invariants survive the actual clock average. -/
theorem clockAverage_invariant (L : H →L[ℝ] ℝ)
    (hL : ∀ r f, L (T r f) = L f) (f : H) :
    L (clockAverage μ T hI hT f) = L f := by
  rw [clockAverage_apply, ← L.integral_comp_comm (hI f)]
  simp only [hL, integral_const, probReal_univ, one_smul]

/-- The source convex energy is bounded by the clock-average endpoint energy. -/
theorem clockAverage_energy_le (A : H →L[ℝ] H) (ε : ℝ)
    (hpos : ∀ f, 0 ≤ quadraticEnergy A ε f) (f : H)
    (hE : Integrable (fun r => quadraticEnergy A ε (T r f)) μ) :
    quadraticEnergy A ε (clockAverage μ T hI hT f) ≤
      ∫ r, quadraticEnergy A ε (T r f) ∂μ :=
  quadraticEnergy_integral_le μ A ε hpos _ (hI f) hE

end AcceleratedLogConcave.Kinetic
