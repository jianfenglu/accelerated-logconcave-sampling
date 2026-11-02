import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.Polynomial

/-! The genuine heat quotient has quadratic generator growth uniformly in time.
These estimates supply the integrable envelopes for the core energy identity. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson AcceleratedLogConcave.HeatCalculus
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem compactHeatQuotient_gradient {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (t : ℝ) (ht : t ∈ Icc a b) (x : E) :
    gradient (compactHeatQuotient F f t) x =
      (F.density t x)⁻¹ • gradient (compactHeatNumerator F f t) x +
        compactHeatQuotient F f t x • gradient (F.potential t) x := by
  simp only [gradient, compactHeatQuotient_fderiv F hf hc t ht x, map_add, map_smul]

theorem compactHeatQuotient_generator {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (t : ℝ) (ht : t ∈ Icc a b) (x : E) :
    weightedHeatGenerator (F.potential t) (compactHeatQuotient F f t) x =
      -compactTestLaplacian (compactHeatNumerator F f t) x / F.density t x +
        compactHeatQuotient F f t x *
          (‖gradient (F.potential t) x‖^2 - compactTestLaplacian (F.potential t) x) -
        inner ℝ (gradient (F.potential t) x) (gradient (compactHeatQuotient F f t) x) := by
  have he := compactTestLaplacian_mul (reference_density_C2 F t ht)
    (compactHeatQuotient_C2 F hf hc t ht) x
  rw [← compactHeatNumerator_eq_density_mul F f t ht,
    reference_density_gradient F t ht, reference_density_laplacian F t ht,
    inner_smul_left, RCLike.conj_to_real] at he
  unfold weightedHeatGenerator
  field_simp [(reference_density_pos F t ht x).ne']
  nlinarith

/-- Uniform algebraic growth transfer, also for a parameterized smooth core. -/
theorem compactHeatQuotient_growth_of_numerator_bounds {P : Type*} {a b : ℝ}
    (F : ReferencePoissonFamily E a b) (f : P → E → ℝ)
    (hf : ∀ p, ContDiff ℝ 2 (f p)) (hc : ∀ p, HasCompactSupport (f p))
    (C₀ C₁ C₂ : ℝ) (h₀ : 0 ≤ C₀) (h₁ : 0 ≤ C₁) (h₂ : 0 ≤ C₂)
    (hn : ∀ p t, t ∈ Icc a b → ∀ x,
      ‖compactHeatNumerator F (f p) t x‖ ≤ C₀*F.density t x ∧
      ‖fderiv ℝ (compactHeatNumerator F (f p) t) x‖ ≤ C₁*F.density t x ∧
      ‖compactTestLaplacian (compactHeatNumerator F (f p) t) x‖ ≤ C₂*F.density t x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p t, t ∈ Icc a b → ∀ x,
      ‖compactHeatQuotient F (f p) t x‖ ≤ C ∧
      ‖gradient (compactHeatQuotient F (f p) t) x‖ ≤ C*(1+‖x‖) ∧
      ‖weightedHeatGenerator (F.potential t) (compactHeatQuotient F (f p) t) x‖ ≤
        C*(1+‖x‖^2) := by
  obtain ⟨B,hB,hG⟩ := reference_gradient_linear_bound F
  let N : ℝ := Fintype.card ι
  let A := C₁+C₀*B+C₀
  let K := C₂+C₀*N+4*C₀*B^2+4*C₀+2*C₁*B+2*C₁
  let C := C₀+A+K
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C,hC,fun p t ht x => ?_⟩
  have hp := reference_density_pos F t ht x
  obtain ⟨n₀,n₁,n₂⟩ := hn p t ht x
  have hq : ‖compactHeatQuotient F (f p) t x‖ ≤ C₀ := by
    dsimp only [compactHeatQuotient]
    rw [norm_div, Real.norm_of_nonneg hp.le]
    exact (div_le_iff₀ hp).mpr n₀
  have hDn : ‖gradient (compactHeatNumerator F (f p) t) x‖ ≤ C₁*F.density t x := by
    simpa only [gradient, LinearIsometryEquiv.norm_map] using n₁
  have hDq : ‖gradient (compactHeatQuotient F (f p) t) x‖ ≤
      C₁+C₀*‖gradient (F.potential t) x‖ := by
    rw [compactHeatQuotient_gradient F (hf p) (hc p) t ht x]
    calc
      _ ≤ ‖(F.density t x)⁻¹ • gradient (compactHeatNumerator F (f p) t) x‖ +
          ‖compactHeatQuotient F (f p) t x • gradient (F.potential t) x‖ := norm_add_le _ _
      _ ≤ C₁+C₀*‖gradient (F.potential t) x‖ := by
        rw [norm_smul, norm_inv, Real.norm_of_nonneg hp.le, norm_smul]
        apply add_le_add
        · calc
            _ ≤ (F.density t x)⁻¹*(C₁*F.density t x) :=
              mul_le_mul_of_nonneg_left hDn (inv_nonneg.mpr hp.le)
            _ = C₁ := by field_simp
        · exact mul_le_mul_of_nonneg_right hq (norm_nonneg _)
  have hDq' : ‖gradient (compactHeatQuotient F (f p) t) x‖ ≤ A*(1+‖x‖) := by
    have hi := hG t ht x
    dsimp only [A]
    nlinarith [norm_nonneg x, mul_nonneg h₀ (norm_nonneg x)]
  have hLap := reference_laplacian_bounds F t ht x
  have hk : ‖weightedHeatGenerator (F.potential t) (compactHeatQuotient F (f p) t) x‖ ≤
      C₂+C₀*N+2*C₀*‖gradient (F.potential t) x‖^2+C₁*‖gradient (F.potential t) x‖ := by
    rw [compactHeatQuotient_generator F (hf p) (hc p) t ht x]
    calc
      _ ≤ ‖-compactTestLaplacian (compactHeatNumerator F (f p) t) x / F.density t x‖ +
          ‖compactHeatQuotient F (f p) t x * (‖gradient (F.potential t) x‖^2 -
            compactTestLaplacian (F.potential t) x)‖ +
          ‖inner ℝ (gradient (F.potential t) x) (gradient (compactHeatQuotient F (f p) t) x)‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ C₂ + C₀*(‖gradient (F.potential t) x‖^2+N) +
          ‖gradient (F.potential t) x‖*(C₁+C₀*‖gradient (F.potential t) x‖) := by
        apply add_le_add
        · apply add_le_add
          · rw [norm_div, norm_neg, Real.norm_of_nonneg hp.le]
            exact (div_le_iff₀ hp).mpr n₂
          · rw [norm_mul]
            apply mul_le_mul hq _ (norm_nonneg _) h₀
            exact (norm_sub_le _ _).trans (by
              rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg hLap.1]
              exact add_le_add le_rfl hLap.2)
        · exact (norm_inner_le_norm _ _).trans
            (mul_le_mul_of_nonneg_left hDq (norm_nonneg _))
      _ = _ := by ring
  have hk' : ‖weightedHeatGenerator (F.potential t) (compactHeatQuotient F (f p) t) x‖ ≤
      K*(1+‖x‖^2) := by
    have hi := hG t ht x
    have hr := norm_nonneg x
    have hg := norm_nonneg (gradient (F.potential t) x)
    have hs : ‖gradient (F.potential t) x‖^2 ≤ 2*B^2+2*‖x‖^2 := by nlinarith [sq_nonneg (B-‖x‖)]
    have hlinear : ‖x‖ ≤ 1+‖x‖^2 := by nlinarith [sq_nonneg (‖x‖-1)]
    have hGlin : ‖gradient (F.potential t) x‖ ≤ B+1+‖x‖^2 := by linarith
    dsimp only [K]
    nlinarith [mul_le_mul_of_nonneg_left hs (show 0 ≤ 2*C₀ by positivity),
      mul_le_mul_of_nonneg_left hGlin h₁,
      mul_nonneg (show 0 ≤ C₂+C₀*N+4*C₀*B^2+2*C₁*B+C₁ by positivity) (sq_nonneg ‖x‖),
      mul_nonneg h₁ hB]
  refine ⟨hq.trans (by dsimp only [C]; linarith), hDq'.trans ?_, hk'.trans ?_⟩
  · apply mul_le_mul_of_nonneg_right _ (by positivity)
    dsimp only [C]; linarith
  · apply mul_le_mul_of_nonneg_right _ (by positivity)
    dsimp only [C]; linarith

/-- Uniform bounds without an inverse-time factor. -/
theorem compactHeatQuotient_uniform_growth {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, ∀ x,
      ‖compactHeatQuotient F f t x‖ ≤ C ∧
      ‖gradient (compactHeatQuotient F f t) x‖ ≤ C*(1+‖x‖) ∧
      ‖weightedHeatGenerator (F.potential t) (compactHeatQuotient F f t) x‖ ≤
        C*(1+‖x‖^2) := by
  obtain ⟨C₀,C₁,C₂,h₀,h₁,h₂,hn⟩ := compactHeatNumerator_derivative_bounds F hf hc hheat
  obtain ⟨C,hC,hbound⟩ := compactHeatQuotient_growth_of_numerator_bounds F
    (fun _ : Unit => f) (fun _ => hf) (fun _ => hc) C₀ C₁ C₂ h₀ h₁ h₂ (fun _ => hn)
  exact ⟨C,hC,hbound ()⟩

end AcceleratedLogConcave.Kinetic.Reheating
