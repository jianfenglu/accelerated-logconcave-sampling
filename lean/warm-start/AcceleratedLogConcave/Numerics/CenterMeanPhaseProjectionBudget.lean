import AcceleratedLogConcave.Numerics.CenterMeanPhaseVectorPadding

/-! NEW reconstruction; SOURCE ONLY. The position projection has precisely
one identity matrix at order zero and zero at positive orders. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Conditional CenteringFlowLp Tensor Tensor.AdjointReduction Tensor.CoordinateReduction
open Tensor.Ordered.Graph Tensor.ActualCoefficientIntegrability
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))

theorem coordinate_eq_inner (i : Fin D) :
    (fun y : E => y i) = innerSL ℝ (coordinateDirection D i) := by
  funext y
  simp [coordinateDirection, EuclideanSpace.inner_single_left]

theorem positionPhysicalJet_eq (n : ℕ) (y : E) :
    physicalVectorGradientJet (fun i (w : E) => w i) n y =
      if n = 0 then WithLp.toLp 2 (fun a : Fin n ⊕ Fin 2 → Fin D =>
        inner ℝ (coordinateDirection D (a (.inr 0)))
          (coordinateDirection D (a (.inr 1)))) else 0 := by
  ext a
  change partialAlong _ _ (dir _ (fun w : E => w (a (.inr 0)))) y = _
  rw [coordinate_eq_inner]
  have he : dir (coordinateDirection D (a (.inr 1)))
      (innerSL ℝ (coordinateDirection D (a (.inr 0)))) = fun _ : E =>
        inner ℝ (coordinateDirection D (a (.inr 0)))
          (coordinateDirection D (a (.inr 1))) := by
    funext w
    exact congrArg (fun A : E →L[ℝ] ℝ => A (coordinateDirection D (a (.inr 1))))
      (innerSL ℝ (coordinateDirection D (a (.inr 0)))).hasFDerivAt.fderiv
  rw [he, partialAlong_eq_jet]
  by_cases hn : n = 0 <;> simp [JetCalculus.jet_const, hn]

theorem phaseProjectionJet_eq_pad (d : Data (Fin D)) (L a : ℝ) (n : ℕ) (z : EP) :
    phaseCoefficientJet (phaseCoefficients d L a) .positionProjection n z =
      coordinatePadCoeff (fun _ : Fin n ⊕ Fin 2 => Fin.castAddEmb D)
        (physicalVectorGradientJet (fun i (w : E) => w i) n (phasePosition z)) := by
  change vectorGradientJet phasePaddedPosition n z = _
  apply vectorGradientJet_eq_pad _ _
  · intro i
    rw [coordinate_eq_inner]
    exact (innerSL ℝ (coordinateDirection D i)).contDiff
  · intro i
    funext w
    exact phaseEmbedPosition_coordinate_castAdd (phasePosition w) i
  · intro i
    funext w
    exact phaseEmbedPosition_coordinate_natAdd (phasePosition w) i

theorem phaseProjectionJet_budget (d : Data (Fin D)) (L a : ℝ)
    {c : ℝ} (hc : 4 ≤ c) (n : ℕ) (z : EP)
    (S : Finset (Fin n ⊕ Fin 2)) (hS : NontrivialSplit S) :
    splitNorm (D+D) S
      (phaseCoefficientJet (phaseCoefficients d L a) .positionProjection n z) ≤
      c^(2+n)*((2+n).factorial : ℝ)*
        (Real.sqrt (conditionalVariance d.b))^(-(n : ℝ)) := by
  rw [phaseProjectionJet_eq_pad]
  apply (splitNorm_coordinatePadCoeff_le _ _ _).trans
  rw [positionPhysicalJet_eq]
  split_ifs with hn
  · subst n
    have hi := pairIdentity_splitNorm_le (Slot := Fin 0 ⊕ Fin 2) (by simp)
      (.inr 0) (.inr 1) (by simp) S hS (D := D)
    apply hi.trans
    norm_num
    nlinarith
  · rw [splitNorm_zero]
    have hc0 : 0 ≤ c := by linarith
    positivity

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
