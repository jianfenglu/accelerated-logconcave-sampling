import AcceleratedLogConcave.Analysis.AnglePhaseConstantJets

/-! The only unpaid quantitative Gaussian phase primitive is the literal
normalized displacement gradient. All other primitive and score estimates
are discharged here, rather than added as hypotheses. -/
noncomputable section
namespace AcceleratedLogConcave.Analysis.AnglePhase
open Tensor Tensor.Ordered.Graph Tensor.PhaseExpression Kinetic.Reheating
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))

theorem anglePrimitiveBudgets_of_gradient (T : E → E) (M : E) (q a S : ℝ)
    (hS : 0 < S)
    (hgrad : ∀ j (z : EP) (A : Finset (Fin j ⊕ Fin 2)), NontrivialSplit A →
      splitNorm (D+D) A
        (phaseCoefficientJet (angleCoefficients T M q a) .observableGradient j z) ≤
          (256:ℝ)^(2+j) * ((2+j).factorial : ℝ) * S^(-((1:ℝ)+(j:ℝ)))) :
    PhasePrimitiveBudgets (angleCoefficients T M q a) gaussianPotential 256 S := by
  constructor
  · intro c j z A hA
    by_cases hc : c = .observableGradient
    · subst c
      exact hgrad j z A hA
    · by_cases hj : j = 0
      · subst j
        have hzero : splitNorm (D+D) A
            (phaseCoefficientJet (angleCoefficients T M q a) c 0 z) ≤ 1 := by
          cases c with
          | transport => exact angle_transport_zero_split T M q a z A hA
          | scoreHessian => exact angle_identity_zero_split T M q a _ (Or.inl rfl) z A hA
          | positionProjection => exact angle_identity_zero_split T M q a _ (Or.inr rfl) z A hA
          | observableGradient => exact False.elim (hc rfl)
        apply hzero.trans
        have hw : signature.weight c = 0 := by cases c <;> simp_all [signature]
        rw [hw]
        norm_num [signature]
      · rw [angle_constant_primitive_higher T M q a c hc j (Nat.pos_of_ne_zero hj),splitNorm_zero]
        positivity
  · intro j hj z A hA
    by_cases hj1 : j = 1
    · subst j
      apply (phaseScoreJet_gaussian_one_split z A hA).trans
      norm_num
    · rw [phaseScoreJet_gaussian_higher j (by omega),splitNorm_zero]
      positivity
end AcceleratedLogConcave.Analysis.AnglePhase
