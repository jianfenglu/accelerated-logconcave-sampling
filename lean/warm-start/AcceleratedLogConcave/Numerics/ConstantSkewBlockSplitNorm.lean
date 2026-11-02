import AcceleratedLogConcave.Numerics.CenterMeanPhaseCoordinates
import AcceleratedLogConcave.Tensor.PairMatrixCoefficient
import AcceleratedLogConcave.Tensor.OrderedContraction

/-! The constant quarter-turn [0,-I;I,0] has operator norm at most one,
and so do every proper split of its literal rank-two coefficient tensor. -/
noncomputable section
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Tensor
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)

theorem negativeIdentity_skewBlock_norm_le :
    ‖matrixCLMEquiv (skewBlockEntry (-ContinuousLinearMap.id ℝ E))‖ ≤ 1 := by
  apply opNorm_le_of_energyBound _ 1 zero_le_one
  intro v
  simp [skewBlockEntry, Fintype.sum_sum_type,
    EuclideanSpace.basisFun_apply, EuclideanSpace.single,
    EuclideanSpace.inner_single_left, PiLp.single_apply, add_comm]

theorem negativeIdentity_phaseBlock_norm_le :
    ‖matrixCLMEquiv (fun i j : Fin (D+D) =>
      skewBlockEntry (-ContinuousLinearMap.id ℝ E)
        (finSumFinEquiv.symm i) (finSumFinEquiv.symm j))‖ ≤ 1 := by
  have h := matrixCLM_reindex_norm
    (skewBlockEntry (-ContinuousLinearMap.id ℝ E) :
      Matrix (Fin D ⊕ Fin D) (Fin D ⊕ Fin D) ℝ)
    (finSumFinEquiv.symm : Fin (D+D) ≃ Fin D ⊕ Fin D)
    (finSumFinEquiv.symm : Fin (D+D) ≃ Fin D ⊕ Fin D)
  exact h.le.trans (negativeIdentity_skewBlock_norm_le (D := D))

theorem negativeIdentity_phaseBlock_splitNorm_le
    {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (hcard : Fintype.card Slot = 2) (p q : Slot) (hpq : p ≠ q)
    (S : Finset Slot) (hS : NontrivialSplit S) :
    splitNorm (D+D) S (WithLp.toLp 2 (fun a : Slot → Fin (D+D) =>
      skewBlockEntry (-ContinuousLinearMap.id ℝ E)
        (finSumFinEquiv.symm (a p)) (finSumFinEquiv.symm (a q)))) ≤ 1 :=
  (pairMatrixCoefficient_splitNorm_le (D := D+D) hcard p q hpq
    (fun i j => skewBlockEntry (-ContinuousLinearMap.id ℝ E)
      (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)) S hS).trans
    (negativeIdentity_phaseBlock_norm_le (D := D))

/-- Engine transport layout, including both orientations of every proper split. -/
theorem negativeIdentity_engine_transport_splitNorm_le
    (S : Finset (Fin 0 ⊕ Fin 2)) (hS : NontrivialSplit S) :
    splitNorm (D+D) S (WithLp.toLp 2 (fun a : (Fin 0 ⊕ Fin 2) → Fin (D+D) =>
      skewBlockEntry (-ContinuousLinearMap.id ℝ E)
        (finSumFinEquiv.symm (a (.inr 0))) (finSumFinEquiv.symm (a (.inr 1))))) ≤ 1 :=
  negativeIdentity_phaseBlock_splitNorm_le (D := D) (Slot := Fin 0 ⊕ Fin 2)
    (by simp) (Sum.inr (0 : Fin 2)) (Sum.inr (1 : Fin 2)) (by decide) S hS

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
