import AcceleratedLogConcave.Numerics.CenterMeanPhaseVectorPadding

/-! NEW reconstruction; SOURCE ONLY. Exact observable-gradient padding with
normalization r*ell and the actual output/input orientation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Conditional CenteringFlowLp Tensor Tensor.AdjointReduction Tensor.CoordinateReduction
open Tensor.Ordered.Graph Tensor.ActualCoefficientIntegrability
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))

def normalizedObservableCoordinate (d : Data (Fin D)) (i : Fin D) (y : E) : ℝ :=
  (d.r*d.ell)⁻¹ * inner ℝ (coordinateDirection D i) (M d y - meanOffset d)

theorem smooth_normalizedObservableCoordinate (d : Data (Fin D)) (i : Fin D) :
    ContDiff ℝ ∞ (normalizedObservableCoordinate d i) := by
  exact contDiff_const.mul (contDiff_const.inner ℝ ((smooth_M d).sub contDiff_const))

theorem observablePhysicalJet_eq (d : Data (Fin D)) (n : ℕ) (y : E) :
    physicalVectorGradientJet (normalizedObservableCoordinate d) n y =
      WithLp.toLp 2 (fun a => sourceObservableGradientJet d n y
        (a ∘ terminalSlotEquiv 1 n)) := by
  ext a
  rw [show physicalVectorGradientJet (normalizedObservableCoordinate d) n y a =
      JetCalculus.jet (fun i : Fin n => coordinateDirection D (a (.inl i)))
        (List.finRange n) (dir (coordinateDirection D (a (.inr 1)))
          (normalizedObservableCoordinate d (a (.inr 0)))) y by
      exact congrFun (partialAlong_eq_jet _ _ _) y]
  change JetCalculus.jet _ _ _ y = JetCalculus.jet _ _ _ y
  congr 2
  funext z
  change fderiv ℝ (fun w => (d.r*d.ell)⁻¹ *
      inner ℝ (coordinateDirection D (a (.inr 0))) (M d w - meanOffset d)) z
      (coordinateDirection D (a (.inr 1))) = _
  rw [fderiv_const_mul ((contDiff_const.inner ℝ ((smooth_M d).sub contDiff_const)).differentiable
    (by simp) z)]
  rfl

/-- The actual phase observable, with exact normalization and exact terminal
orientation, not a selected tensor sharing only a bound. -/
theorem phaseObservableJet_eq_pad (d : Data (Fin D)) (L : ℝ) (n : ℕ) (z : EP) :
    phaseCoefficientJet (phaseCoefficients d L (d.r*d.ell)) .observableGradient n z =
      coordinatePadCoeff (fun _ : Fin n ⊕ Fin 2 => Fin.castAddEmb D)
        (physicalVectorGradientJet (normalizedObservableCoordinate d) n (phasePosition z)) := by
  change vectorGradientJet (phaseObservable d (d.r*d.ell)) n z = _
  apply vectorGradientJet_eq_pad _ _ (smooth_normalizedObservableCoordinate d)
  · intro i
    funext w
    change (d.r*d.ell)⁻¹ * phaseEmbedPosition (M d (phasePosition w) - meanOffset d)
      (Fin.castAdd D i) = _
    rw [phaseEmbedPosition_coordinate_castAdd]
    simp [normalizedObservableCoordinate, coordinateDirection,
      EuclideanSpace.inner_single_left]
  · intro i
    funext w
    change (d.r*d.ell)⁻¹ * phaseEmbedPosition (M d (phasePosition w) - meanOffset d)
      (Fin.natAdd D i) = 0
    rw [phaseEmbedPosition_coordinate_natAdd, mul_zero]

/-- A stronger weight-zero estimate before the required weight-one weakening.
This theorem remains valid when ell=0; the positive-scale ODE is separate. -/
theorem phaseObservableJet_strong_budget (d : Data (Fin D)) (L : ℝ)
    (n : ℕ) (z : EP) (S : Finset (Fin n ⊕ Fin 2)) (hS : NontrivialSplit S) :
    splitNorm (D+D) S
      (phaseCoefficientJet (phaseCoefficients d L (d.r*d.ell)) .observableGradient n z) ≤
      (2:ℝ)^(2+n)*((2+n).factorial : ℝ)*
        ((Real.sqrt (conditionalVariance d.b))^n)⁻¹ := by
  rw [phaseObservableJet_eq_pad]
  apply (splitNorm_coordinatePadCoeff_le _ _ _).trans
  rw [observablePhysicalJet_eq]
  apply (splitNorm_slotEquiv_le D (terminalSlotEquiv 1 n).symm S
    (sourceObservableGradientJet d n (phasePosition z))).trans
  exact sourceObservableGradientJet_budget d n (phasePosition z) _
    (nontrivialSplit_map_equiv _ hS)

/-- The original positive-variance radius is positive and at most one.
There is no radius-zero substitution or extension to the excluded b=1 endpoint. -/
theorem sourcePhysicalRadius_bounds (d : Data (Fin D)) :
    0 < Real.sqrt (conditionalVariance d.b) ∧
      Real.sqrt (conditionalVariance d.b) ≤ 1 := by
  constructor
  · exact Real.sqrt_pos.mpr (conditionalVariance_pos (by linarith [d.hb]) d.hb1)
  · apply Real.sqrt_le_one.mpr
    simp only [conditionalVariance]
    nlinarith [sq_nonneg d.b]

/-- Exact weight-one allowance. The stronger R^-n estimate is weakened using
R≤1, while all factors and the original normalization remain unchanged. -/
theorem phaseObservableJet_budget (d : Data (Fin D)) (L : ℝ)
    {c : ℝ} (hc : 2 ≤ c) (n : ℕ) (z : EP)
    (S : Finset (Fin n ⊕ Fin 2)) (hS : NontrivialSplit S) :
    splitNorm (D+D) S
      (phaseCoefficientJet (phaseCoefficients d L (d.r*d.ell)) .observableGradient n z) ≤
      c^(2+n)*((2+n).factorial : ℝ)*
        (Real.sqrt (conditionalVariance d.b))^(-((1:ℝ)+(n:ℝ))) := by
  have h := phaseObservableJet_strong_budget d L n z S hS
  have hr := sourcePhysicalRadius_bounds d
  have hrad : (Real.sqrt (conditionalVariance d.b))^(-(n:ℝ)) ≤
      (Real.sqrt (conditionalVariance d.b))^(-((1:ℝ)+(n:ℝ))) :=
    Real.rpow_le_rpow_of_exponent_ge hr.1 hr.2 (by linarith)
  have h' : splitNorm (D+D) S
      (phaseCoefficientJet (phaseCoefficients d L (d.r*d.ell)) .observableGradient n z) ≤
      (2:ℝ)^(2+n)*((2+n).factorial : ℝ)*
        (Real.sqrt (conditionalVariance d.b))^(-(n:ℝ)) := by
    simpa [Real.rpow_neg, Real.rpow_natCast] using h
  apply h'.trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hc _) (by positivity)
  · exact hrad
  · positivity
  · have hc0 : 0 ≤ c := by linarith
    positivity

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
