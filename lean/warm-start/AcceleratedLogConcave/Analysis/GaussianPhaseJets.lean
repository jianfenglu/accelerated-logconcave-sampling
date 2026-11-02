import AcceleratedLogConcave.Analysis.GaussianPhaseEnvironment
import AcceleratedLogConcave.Tensor.PhasePrimitiveBudgets
import AcceleratedLogConcave.Tensor.HessianCoefficientBudget

/-! The standard Gaussian score has one identity jet and no higher jets. -/
noncomputable section
namespace AcceleratedLogConcave.Analysis.AnglePhase
open Tensor Tensor.AdjointReduction Tensor.Ordered.Graph Kinetic.Reheating
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem dir_gaussianPotential (v : E) : dir v gaussianPotential = innerSL ℝ v := by
  funext x
  simp [dir,gaussianPotential_fderiv,real_inner_comm]

theorem partialAlong_linear_of_two_le {I : Type*} (d : I → E) (J : List I)
    (L : E →L[ℝ] ℝ) (hJ : 2 ≤ J.length) : partialAlong d J L = fun _ => 0 := by
  induction J with
  | nil => simp at hJ
  | cons i J ih =>
    cases J with
    | nil => simp at hJ
    | cons j K =>
      cases K with
      | nil =>
        have hL : dir (d j) L = fun _ => L (d j) := by
          funext x
          exact congrArg (fun A : E →L[ℝ] ℝ => A (d j)) (L.fderiv)
        change dir (d i) (dir (d j) L) = _
        rw [hL]
        funext x
        change fderiv ℝ (fun _ : E => L (d j)) x (d i) = 0
        simp only [fderiv_const_apply,zero_apply]
      | cons k K =>
        rw [partialAlong,ih (by simp)]
        funext x
        change fderiv ℝ (fun _ : E => (0 : ℝ)) x (d i) = 0
        simp only [fderiv_const_apply,zero_apply]

theorem phaseScoreJet_gaussian_one {D : ℕ} (x : EuclideanSpace ℝ (Fin D)) :
    phaseScoreJet gaussianPotential 1 x = WithLp.toLp 2
      (fun a : Fin 1 ⊕ Unit → Fin D => inner ℝ (coordinateDirection D (a (.inr ())))
        (coordinateDirection D (a (.inl 0)))) := by
  ext a
  change dir (coordinateDirection D (a (.inl 0)))
    (dir (coordinateDirection D (a (.inr ()))) gaussianPotential) x = _
  rw [dir_gaussianPotential]
  change fderiv ℝ (innerSL ℝ (coordinateDirection D (a (.inr ())))) x
    (coordinateDirection D (a (.inl 0))) = _
  exact congrArg (fun L : EuclideanSpace ℝ (Fin D) →L[ℝ] ℝ =>
    L (coordinateDirection D (a (.inl 0))))
    ((innerSL ℝ (coordinateDirection D (a (.inr ())))).fderiv)

theorem phaseScoreJet_gaussian_higher {D : ℕ} (j : ℕ) (hj : 2 ≤ j)
    (x : EuclideanSpace ℝ (Fin D)) : phaseScoreJet gaussianPotential j x = 0 := by
  ext a
  change partialAlong _ (List.finRange j)
    (dir (coordinateDirection D (a (.inr ()))) gaussianPotential) x = 0
  rw [dir_gaussianPotential,partialAlong_linear_of_two_le _ _ _ (by simpa using hj)]

theorem phaseScoreJet_gaussian_one_split {D : ℕ} (x : EuclideanSpace ℝ (Fin D))
    (S : Finset (Fin 1 ⊕ Unit)) (hS : NontrivialSplit S) :
    splitNorm D S (phaseScoreJet gaussianPotential 1 x) ≤ 1 := by
  rw [phaseScoreJet_gaussian_one]
  exact ActualCoefficientIntegrability.pairIdentity_splitNorm_le
    (Slot := Fin 1 ⊕ Unit) (D := D) (by decide)
    (.inr ()) (.inl 0) (by simp) S hS
end AcceleratedLogConcave.Analysis.AnglePhase
