import AcceleratedLogConcave.Conditional.Flow.MaterialPointwise

/-! Upgrade the compact-test Stein identity to the exact pointwise sign used
by the stationary centering equation. -/
noncomputable section
open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Conditional.Centering
open Analysis.Poisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem pointwise_stein_of_compact_test {p : E → ℝ} {score M : E → E}
    {Kt : E → E →L[ℝ] E} (u : E)
    (hp : ContDiff ℝ 1 p) (hpos : ∀ y, 0 < p y)
    (hs : Continuous score) (hM : Continuous M) (hK : ContDiff ℝ 1 Kt)
    (hscore : ∀ y, HasFDerivAt p ((-p y) • innerSL ℝ (score y)) y)
    (hweak : ∀ (g : E) (φ : E → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫ y, p y * inner ℝ (M y - u) g * φ y) =
        ∫ y, p y * fderiv ℝ φ y (Kt y g)) :
    ∀ y g, fderiv ℝ p y (Kt y g) +
      p y * fluxDivergence (fun w => Kt w g) y = -p y * inner ℝ (M y - u) g := by
  intro y g
  have hU : ContDiff ℝ 1 (fun w => Kt w g) := hK.clm_apply contDiff_const
  have he := material_eq_weightedAdjoint_of_weak hp hpos
    ((hM.sub continuous_const).inner continuous_const) hs hU hscore (hweak g) y
  rw [(hscore y).fderiv]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
  dsimp [weightedAdjoint] at he
  linear_combination p y * he
end AcceleratedLogConcave.Conditional.Centering
