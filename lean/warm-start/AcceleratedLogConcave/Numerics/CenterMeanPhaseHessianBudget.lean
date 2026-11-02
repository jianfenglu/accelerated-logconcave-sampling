import AcceleratedLogConcave.Numerics.CenterMeanPhaseScoreBudget

/-! NEW reconstruction; SOURCE ONLY. Exact terminal conversion from the actual
positive-order phase score to phase Hessian coefficient jets. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Conditional CenteringFlowLp Tensor Tensor.AdjointReduction Tensor.CoordinateReduction
open Tensor.Ordered.Graph Tensor.ActualCoefficientIntegrability
variable {D : ℕ}
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))

/-- The distinguished leading derivative becomes Hessian terminal 0 and the
score direction becomes Hessian terminal 1; all other derivatives retain order. -/
theorem phaseHessianJet_eq_score (d : Data (Fin D)) (L a : ℝ)
    (n : ℕ) (z : EP) :
    phaseCoefficientJet (phaseCoefficients d L a) .scoreHessian n z =
      WithLp.toLp 2 (fun b => phaseScoreJet (phasePotential d) (n+1) z
        (b ∘ scoreTerminalSlotEquiv n)) := by
  ext b
  symm
  change partialAlong _ (List.finRange (n+1)) (dir _ (phasePotential d)) z = _
  rw [List.finRange_succ,
    nonempty_score_is_hessian _ _ _ (smooth_phasePotential d)]
  simp [phaseCoefficientJet, phaseCoefficients, partialAlong_eq_jet, JetCalculus.jet_map, scoreTerminalSlotEquiv, Function.comp_def]

/-- All orders, including n=0 and ell=0; the scale parameters play no role
in this primitive. The radius exponent is precisely -n. -/
theorem phaseHessianJet_budget (d : Data (Fin D)) (L a : ℝ)
    {c : ℝ} (hc : 4 ≤ c) (n : ℕ) (z : EP)
    (S : Finset (Fin n ⊕ Fin 2)) (hS : NontrivialSplit S) :
    splitNorm (D+D) S
      (phaseCoefficientJet (phaseCoefficients d L a) .scoreHessian n z) ≤
      c^(2+n)*((2+n).factorial : ℝ)*
        (Real.sqrt (conditionalVariance d.b))^(-(n : ℝ)) := by
  rw [phaseHessianJet_eq_score]
  have h := (splitNorm_slotEquiv_le (D+D) (scoreTerminalSlotEquiv n).symm S
      (phaseScoreJet (phasePotential d) (n+1) z)).trans
    (phaseScoreJet_budget d hc (n+1) (by omega) z _
      (nontrivialSplit_map_equiv _ hS))
  simpa only [Equiv.symm_symm, Nat.add_sub_cancel,
    show n+1+1 = 2+n by omega] using h

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
