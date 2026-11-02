import AcceleratedLogConcave.Numerics.CenterMeanPhaseScorePadding

/-! NEW reconstruction; SOURCE ONLY. Actual phase score, with the momentum
identity retained at first order and absent at all higher orders. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Conditional CenteringFlowLp Tensor Tensor.AdjointReduction Tensor.CoordinateReduction
open Tensor.Ordered.Graph Tensor.ActualCoefficientIntegrability
open Analysis.AnglePhase Kinetic.Reheating
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))

theorem phaseScoreJet_add {N : ℕ} (H G : EuclideanSpace ℝ (Fin N) → ℝ)
    (hH : ContDiff ℝ ∞ H) (hG : ContDiff ℝ ∞ G) (j : ℕ)
    (z : EuclideanSpace ℝ (Fin N)) :
    phaseScoreJet (fun x => H x + G x) j z =
      phaseScoreJet H j z + phaseScoreJet G j z := by
  ext a
  change partialAlong _ _ (dir _ (fun x => H x + G x)) z = _
  rw [dir_add _ (hH.differentiable (by simp)) (hG.differentiable (by simp)),
    partialAlong_add _ _ (contDiff_dir hH _) (contDiff_dir hG _)]
  rfl

theorem phaseScoreJet_interpolation_eq (d : Data (Fin D)) (j : ℕ) (y : E) :
    phaseScoreJet (interpolationPotential d.F d.x d.r d.b) j y =
      physicalSourceScoreJet d j y := by
  ext a
  change partialAlong _ _ (dir _ _) _ = _
  rw [sourceScore_direction]
  rfl

/-- No rotated/dilated coordinate map: physical position and independent
standard-Gaussian momentum are the actual two phase blocks. -/
theorem phaseScoreJet_eq_two_pads (d : Data (Fin D)) (j : ℕ) (z : EP) :
    phaseScoreJet (phasePotential d) j z =
      coordinatePadCoeff (fun _ : Fin j ⊕ Unit => Fin.castAddEmb D)
        (physicalSourceScoreJet d j (phasePosition z)) +
      coordinatePadCoeff (fun _ : Fin j ⊕ Unit => Fin.natAddEmb D)
        (phaseScoreJet gaussianPotential j (phaseMomentum z)) := by
  have hH := contDiff_interpolationPotential d.hF d.hlo d.hup d.x d.r
    (by linarith [d.hb] : -1 < d.b) d.hb1
  change phaseScoreJet (fun z =>
    (interpolationPotential d.F d.x d.r d.b ∘ phasePositionCLM) z +
      (gaussianPotential ∘ phaseMomentumCLM) z) j z = _
  rw [phaseScoreJet_add _ _ (hH.comp phasePositionCLM.contDiff)
    (gaussianPotential_smooth.comp phaseMomentumCLM.contDiff),
    phaseScoreJet_position_eq_pad _ hH,
    phaseScoreJet_momentum_eq_pad _ gaussianPotential_smooth,
    phaseScoreJet_interpolation_eq]

/-- c₀=4 absorbs both identity blocks at j=1. For j≥2 only the padded
physical tensor remains. All cuts are proper and no dimension factor occurs. -/
theorem phaseScoreJet_succ_budget (d : Data (Fin D)) (n : ℕ) (z : EP)
    (S : Finset (Fin (n+1) ⊕ Unit)) (hS : NontrivialSplit S) :
    splitNorm (D+D) S (phaseScoreJet (phasePotential d) (n+1) z) ≤
      (4:ℝ)^(n+2)*((n+2).factorial : ℝ)*
        (Real.sqrt (conditionalVariance d.b))^(-(n : ℝ)) := by
  rw [phaseScoreJet_eq_two_pads]
  have hp := physicalSourceScoreJet_succ_budget d n (phasePosition z) S hS
  cases n with
  | zero =>
    have hg := phaseScoreJet_gaussian_one_split (phaseMomentum z) S hS
    have hh := splitNorm_coordinatePadCoeff_add_le
      (fun _ : Fin 1 ⊕ Unit => Fin.castAddEmb D)
      (fun _ : Fin 1 ⊕ Unit => Fin.natAddEmb D) S
      (physicalSourceScoreJet d 1 (phasePosition z))
      (phaseScoreJet gaussianPotential 1 (phaseMomentum z))
    norm_num at hp ⊢
    linarith
  | succ n =>
    rw [phaseScoreJet_gaussian_higher (n+1+1) (by omega)]
    have hz : coordinatePadCoeff (fun _ : Fin (n+1+1) ⊕ Unit => Fin.natAddEmb D)
        (0 : Coeff (Fin (n+1+1) ⊕ Unit) D) = 0 := by
      ext a
      simp [coordinatePadCoeff, coordinatePad]
    rw [hz, add_zero]
    apply (splitNorm_coordinatePadCoeff_le _ _ _).trans (hp.trans ?_)
    have hpow : (2:ℝ)^(n+1+2) ≤ (4:ℝ)^(n+1+2) :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) _
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpow (by positivity)) (by positivity)

/-- The exact score field required by PhasePrimitiveBudgets. There is no j=0
claim, and the natural subtraction j-1 is discharged only after j>0. -/
theorem phaseScoreJet_budget (d : Data (Fin D)) {c : ℝ} (hc : 4 ≤ c)
    (j : ℕ) (hj : 0 < j) (z : EP)
    (S : Finset (Fin j ⊕ Unit)) (hS : NontrivialSplit S) :
    splitNorm (D+D) S (phaseScoreJet (phasePotential d) j z) ≤
      c^(j+1)*((j+1).factorial : ℝ)*
        (Real.sqrt (conditionalVariance d.b))^(-((j-1 : ℕ) : ℝ)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  have h := phaseScoreJet_succ_budget d n z S hS
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at h ⊢
  apply h.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hc _) (by positivity))
    (by positivity)

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
