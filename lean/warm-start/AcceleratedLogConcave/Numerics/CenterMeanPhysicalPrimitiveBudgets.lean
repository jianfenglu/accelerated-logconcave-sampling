import AcceleratedLogConcave.Numerics.CenterMeanPhaseCalculus
import AcceleratedLogConcave.Tensor.HessianDerivativeCoefficient
import AcceleratedLogConcave.Tensor.MeanFlowPhysicalKernelHalfBudget
import AcceleratedLogConcave.Tensor.ActualScoreTerminal
import AcceleratedLogConcave.Tensor.TerminalSlotBound

/-! NEW reconstruction, SOURCE ONLY pending compiler validation.
Literal source-score derivatives are the accepted interpolation Hessian tensors.
These are original-data suppliers, not assumed desired bounds or moment fields.
The nested slot type is kept explicit to avoid silently swapping terminal slots. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Conditional CenteringFlowLp Tensor Tensor.AdjointReduction
open Tensor.ActualCoefficientIntegrability Tensor.PhysicalKernelBudget
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)

/-- Literal source score is the gradient of the same interpolation potential,
not a heat potential at another time or spatial dilation. -/
theorem sourceScore_direction (d : Data (Fin D)) (v : E) :
    dir v (interpolationPotential d.F d.x d.r d.b) =
      fun y => inner ℝ v (sourceScore d y) := by
  funext y
  change dir v (interpolationPotential d.F d.x d.r d.b) y =
    inner ℝ v (y + (d.r*d.b) • conditionalMean d.F d.x d.r d.b y)
  rw [← gradient_interpolationPotential d.hF d.hlo d.hup d.x d.r
    (by linarith [d.hb]) d.hb1 y]
  simp [dir]

/-- n derivatives of the source-score gradient. Terminal `inr ()` is the
first Hessian direction, terminal `inl (inr 0)` is the score direction.
Thus n=0 is a Hessian, NOT the unbounded score itself. -/
def sourceScoreGradientJet (d : Data (Fin D)) (n : ℕ) (y : E) :
    Coeff ((Fin n ⊕ Fin 1) ⊕ Unit) D :=
  WithLp.toLp 2 (fun a => JetCalculus.jet
    (fun i : Fin n => coordinateDirection D (a (.inl (.inl i)))) (List.finRange n)
    (dir (coordinateDirection D (a (.inr ())))
      (fun z => inner ℝ (coordinateDirection D (a (.inl (.inr 0))))
        (sourceScore d z))) y)

theorem sourceScoreGradientJet_eq_hessian (d : Data (Fin D)) (n : ℕ) (y : E) :
    sourceScoreGradientJet d n y =
      hessianDerivativeCoefficient d.F d.x d.ell d.r d.b n y := by
  ext a
  change JetCalculus.jet _ _ _ _ = JetCalculus.jet _ _ _ _
  congr 2
  funext z
  rw [sourceScore_direction]
  simp

/-- Every proper rectangular cut, dimension independent, including ell=0 and
n=0. The identity contribution at n=0 is retained by the accepted supplier. -/
theorem sourceScoreGradientJet_budget (d : Data (Fin D)) (n : ℕ) (y : E)
    (S : Finset ((Fin n ⊕ Fin 1) ⊕ Unit)) (hS : NontrivialSplit S) :
    splitNorm D S (sourceScoreGradientJet d n y) ≤
      (2:ℝ)^(2+n)*((2+n).factorial : ℝ)*
        ((Real.sqrt (conditionalVariance d.b))^n)⁻¹ := by
  rw [sourceScoreGradientJet_eq_hessian]
  exact hessianDerivativeCoefficient_budget (positiveVarianceData d) d.hsmall n
    ⟨by linarith [d.hb], d.hb1⟩ y S hS

/-- Positive-order derivatives have NO identity tensor; the exact coefficient
is r² ell b² and the same derivative order n on normalized J₁. -/
theorem sourceScoreGradientJet_positive (d : Data (Fin D)) {n : ℕ} (hn : 0 < n)
    (y : E) :
    sourceScoreGradientJet d n y = (d.r^2*d.ell*d.b^2) •
      normalizedJetDerivativeCoefficient d.F d.x d.ell d.r d.b 0 n y := by
  rw [sourceScoreGradientJet_eq_hessian]
  have h := hessianDerivativeCoefficient_eq (positiveVarianceData d) n
    ⟨by linarith [d.hb], d.hb1⟩ y
  simpa [positiveVarianceData, Nat.ne_of_gt hn] using h

/-- At zero curvature positive orders vanish; the Hessian at order zero does
not vanish, since the Gaussian identity remains. -/
theorem sourceScoreGradientJet_positive_zero_curvature (d : Data (Fin D))
    (hell : d.ell = 0) {n : ℕ} (hn : 0 < n) (y : E) :
    sourceScoreGradientJet d n y = 0 := by
  rw [sourceScoreGradientJet_positive d hn]
  simp [hell]

/-- The terminal permutation converting a positive-order score tensor into
an n-th Hessian derivative tensor. Its inverse is explicit, so proper cuts
transfer without a rank- or dimension-dependent loss. -/
def sourceScoreTerminalEquiv (n : ℕ) :
    (Fin (n+1) ⊕ Unit) ≃ ((Fin n ⊕ Fin 1) ⊕ Unit) :=
  (scoreTerminalSlotEquiv n).trans (terminalSlotEquiv 1 n).symm

/-- Exact positive-order score tensor. The rank-one, zero-derivative score
is intentionally excluded. -/
def physicalSourceScoreJet (d : Data (Fin D)) (j : ℕ) (y : E) :
    Coeff (Fin j ⊕ Unit) D :=
  WithLp.toLp 2 (fun a => partialAlong
    (fun i : Fin j => coordinateDirection D (a (.inl i))) (List.finRange j)
    (fun z => inner ℝ (coordinateDirection D (a (.inr ()))) (sourceScore d z)) y)

theorem physicalSourceScoreJet_succ (d : Data (Fin D)) (n : ℕ) (y : E) :
    physicalSourceScoreJet d (n+1) y = WithLp.toLp 2
      (fun a => sourceScoreGradientJet d n y (a ∘ (sourceScoreTerminalEquiv n).symm)) := by
  ext a
  rw [sourceScoreGradientJet_eq_hessian]
  change partialAlong _ _ (fun z => inner ℝ _ (sourceScore d z)) y = _
  rw [← sourceScore_direction]
  exact actualScore_terminal (positiveVarianceData d) n
    ⟨by linarith [d.hb], d.hb1⟩ y a

/-- The exact positive-order source-score budget has factorial (j+1)!
and radius loss j-1, not j. -/
theorem physicalSourceScoreJet_succ_budget (d : Data (Fin D)) (n : ℕ) (y : E)
    (S : Finset (Fin (n+1) ⊕ Unit)) (hS : NontrivialSplit S) :
    splitNorm D S (physicalSourceScoreJet d (n+1) y) ≤
      (2:ℝ)^(n+2)*((n+2).factorial : ℝ)*
        (Real.sqrt (conditionalVariance d.b))^(-(n : ℝ)) := by
  rw [physicalSourceScoreJet_succ]
  have h := (splitNorm_slotEquiv_le D (sourceScoreTerminalEquiv n) S
      (sourceScoreGradientJet d n y)).trans
    (sourceScoreGradientJet_budget d n y _
      (nontrivialSplit_map_equiv _ hS))
  simpa [Nat.add_comm, Real.rpow_neg, Real.rpow_natCast] using h

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
