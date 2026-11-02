import AcceleratedLogConcave.Numerics.SmoothConditionalDerivatives

/-!
Exact L² identities and a non-sharp intermediate moment bound for conditional
time jets. The constants C and N are the qualitative polynomial-envelope
constants. No explicit algorithmic CellRegularity budget is supplied.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace AcceleratedLogConcave.Numerics.MeanResidualBridge
open MeanFlowLp AffineGraph Analysis.PositiveVarianceSlab ConditionalSmoothing
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
variable (d : MeanFlowLp.Data ι m) (j : Fin m) (ρ : d.G.Kernel)

/-- The actual joint center/input moment. This keeps the common seed and makes
no independence assertion. Its exponent is twice the envelope degree. -/
def conditionalInputMoment (N : ℕ) : ℝ :=
  ∫ w, (1+‖conditionalInput d j ρ w‖)^(2*N) ∂seedMeasure d

theorem conditionalInputMoment_integrable (N : ℕ) :
    Integrable (fun w => (1+‖conditionalInput d j ρ w‖)^(2*N)) (seedMeasure d) := by
  simpa only [← pow_mul, Nat.mul_comm] using
    (conditionalInput_polynomial_memLp d j ρ N).integrable_sq

theorem conditionalInputMoment_nonneg (N : ℕ) : 0 ≤ conditionalInputMoment d j ρ N :=
  integral_nonneg (fun _ => pow_nonneg (by positivity) _)

theorem norm_sq_conditionalJetLp (k : ℕ) (t : ℝ) :
    ‖conditionalJetLp d j ρ k t‖^2 =
      ∫ w, ‖conditionalJet d j ρ k t w‖^2 ∂seedMeasure d :=
  Analysis.DominatedLp.norm_sq_toLp (conditionalJet_memLp d j ρ k t)

/-- Exact receiver derivative norm, with the literal local radius exposed. -/
theorem norm_sq_iteratedDeriv_replacement_conditionalMean (U : H d → ℝ → H d)
    (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U) (k : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (left conditionalEnd) (right conditionalEnd)) :
    ‖iteratedDeriv k ((curvesWithConditional d).conditionalMean d.G U 0 d.r j ρ) t‖^2 =
      (d.r*Real.sqrt (d.G.variance ρ))⁻¹^2 *
        ∫ w, ‖conditionalJet d j ρ (k+1) t w‖^2 ∂seedMeasure d := by
  rw [iteratedDeriv_replacement_conditionalMean d j ρ U hu k ht,
    norm_smul, Real.norm_eq_abs, abs_inv, abs_neg,
    abs_of_pos (conditionalData d ρ).hr, mul_pow, norm_sq_conditionalJetLp]
  rfl

/-- A finite original-data envelope/moment bound, uniform in probability time.
The existential C,N are not an explicit dimension/order/parameter budget. -/
theorem exists_conditionalJetLp_moment_bound (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ t,
      ‖conditionalJetLp d j ρ k t‖^2 ≤ C^2 * conditionalInputMoment d j ρ N := by
  obtain ⟨C,hC,N,hjet⟩ := exists_jet_polynomial_bound (conditionalData d ρ) k
  refine ⟨C,hC,N,fun t => ?_⟩
  rw [norm_sq_conditionalJetLp]
  have hpoint (w : Seed d) :
      ‖conditionalJet d j ρ k t w‖^2 ≤ C^2*(1+‖conditionalInput d j ρ w‖)^(2*N) := by
    have h := (norm_snd_le _).trans (hjet t (conditionalInput d j ρ w))
    have hh := pow_le_pow_left₀ (norm_nonneg (conditionalJet d j ρ k t w)) h 2
    simpa only [mul_pow, ← pow_mul, Nat.mul_comm] using hh
  have hi := integral_mono (conditionalJet_memLp d j ρ k t).norm.integrable_sq
    ((conditionalInputMoment_integrable d j ρ N).const_mul (C^2)) hpoint
  simpa only [integral_const_mul, conditionalInputMoment] using hi

/-- Intermediate mean-derivative bound: the order is shifted by one and the
inverse local radius is explicit. The original data discharge all moments.
The remaining envelope constants are deliberately visible as existential. -/
theorem exists_replacement_conditionalMean_moment_bound (U : H d → ℝ → H d)
    (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
      ∀ t ∈ Ioo (left conditionalEnd) (right conditionalEnd),
        ‖iteratedDeriv k ((curvesWithConditional d).conditionalMean d.G U 0 d.r j ρ) t‖ ≤
          (d.r*Real.sqrt (d.G.variance ρ))⁻¹ * C *
            Real.sqrt (conditionalInputMoment d j ρ N) := by
  obtain ⟨C,hC,N,hjet⟩ := exists_conditionalJetLp_moment_bound d j ρ (k+1)
  refine ⟨C,hC,N,fun t ht => ?_⟩
  have hM := conditionalInputMoment_nonneg d j ρ N
  have hnorm : ‖conditionalJetLp d j ρ (k+1) t‖ ≤
      C * Real.sqrt (conditionalInputMoment d j ρ N) := by
    have he : (C*Real.sqrt (conditionalInputMoment d j ρ N))^2 =
        C^2*conditionalInputMoment d j ρ N := by rw [mul_pow, Real.sq_sqrt hM]
    nlinarith [hjet t, mul_nonneg hC (Real.sqrt_nonneg (conditionalInputMoment d j ρ N))]
  rw [iteratedDeriv_replacement_conditionalMean d j ρ U hu k ht,
    norm_smul, Real.norm_eq_abs, abs_inv, abs_neg, abs_of_pos (conditionalData d ρ).hr]
  simpa only [conditionalData, mul_assoc] using
    mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr (conditionalData d ρ).hr.le)

end AcceleratedLogConcave.Numerics.MeanResidualBridge
