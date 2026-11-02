import AcceleratedLogConcave.Kinetic.Mixing.CenteredChannel

/-! Restriction of bounded mean-preserving operators and their actual adjoints. -/
noncomputable section
open MeasureTheory InnerProductSpace
namespace AcceleratedLogConcave.Kinetic
open Analysis.Poisson
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

/-- Restrict an actual operator using its proved preservation of the mean. -/
def centeredOperator (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hT : ∀ f, mean μ (T f) = mean μ f) : centered μ →L[ℝ] centered μ :=
  (T.comp (centered μ).subtypeL).codRestrict (centered μ) (fun f => by
    change mean μ (T f) = 0
    rw [hT]
    exact f.property)

@[simp] theorem centeredOperator_coe (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hT : ∀ f, mean μ (T f) = mean μ f) (f : centered μ) :
    (centeredOperator μ T hT f : Lp ℝ 2 μ) = T f := rfl

/-- The centered density operator is still the genuine Hilbert adjoint. -/
theorem centeredOperator_adjoint (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hT : ∀ f, mean μ (T f) = mean μ f)
    (hTa : ∀ f, mean μ (T.adjoint f) = mean μ f) :
    (centeredOperator μ T hT).adjoint = centeredOperator μ T.adjoint hTa := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  change inner ℝ (T.adjoint (f : Lp ℝ 2 μ)) (g : Lp ℝ 2 μ) =
    inner ℝ (f : Lp ℝ 2 μ) (T (g : Lp ℝ 2 μ))
  exact ContinuousLinearMap.adjoint_inner_left T g f

end AcceleratedLogConcave.Kinetic
