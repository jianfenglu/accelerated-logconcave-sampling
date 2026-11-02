import AcceleratedLogConcave.Conditional.Stein.TransportLaw
import AcceleratedLogConcave.Gibbs.PrimitiveMoments

/-! Actual conditional means have finite quadratic moments under their
interpolation laws, by the constructed Gaussian probability transport. -/
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Topology NNReal

namespace AcceleratedLogConcave.Conditional

section Gaussian
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem memLp_two_stdGaussian_of_lipschitz {f : E → E} {C : ℝ≥0}
    (hf : LipschitzWith C f) : MemLp f 2 (stdGaussian E) := by
  apply Gibbs.memLp_two_stdGaussian_of_affine_bound hf.continuous C ‖f 0‖
  intro z
  apply (norm_le_insert' (f z) (f 0)).trans
  have hd := hf.dist_le_mul z 0
  simp only [dist_eq_norm, sub_zero] at hd
  linarith

end Gaussian

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The terminal posterior mean is genuinely in L², rather than merely
having a finite-valued Bochner integral by convention. -/
theorem memLp_two_conditionalMean
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (hsmall : r ^ 2 * ell ≤ 1 / 2) :
    MemLp (conditionalMean F x r b) 2 (interpolationLaw F x r b) := by
  let T := forwardProbabilityTransport hF hell hlo hup x hr hb hb1 0
  have hT : LipschitzWith ⟨Real.exp 1, (Real.exp_pos _).le⟩ T :=
    lipschitzWith_convexProbabilityFlow_exp_one hF hell hlo hup x hr hb hb1 hsmall
      (projIcc 0 b hb 0) ⟨b, hb, le_rfl⟩
  have hM := lipschitzWith_conditionalMean hF hell hlo hup x hr
    (show -1 < b by linarith) hb1
  have hm := memLp_two_stdGaussian_of_lipschitz (hM.comp hT)
  have hmp := forwardProbabilityTransport_measurePreserving hF hell hlo hup x hr hb hb1
    (ρ := 0) ⟨le_rfl, hb⟩
  rw [interpolationLaw_zero hF hlo x r] at hmp
  rw [← hmp.map_eq]
  exact T.measurableEmbedding.memLp_map_measure_iff.mpr hm

theorem integrable_conditionalMean_sub_norm_sq
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (hsmall : r ^ 2 * ell ≤ 1 / 2) (u : E) :
    Integrable (fun y => ‖conditionalMean F x r b y - u‖ ^ 2) (interpolationLaw F x r b) := by
  let := interpolationLaw_isProbabilityMeasure hF hlo x r b
  exact ((memLp_two_conditionalMean hF hell hlo hup x hr hb hb1 hsmall).sub
    (memLp_const u)).norm.integrable_sq

end AcceleratedLogConcave.Conditional
