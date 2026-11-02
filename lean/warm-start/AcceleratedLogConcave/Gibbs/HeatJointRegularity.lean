import AcceleratedLogConcave.Conditional.Tilt.HeatIntegral

/-!
# Joint regularity of the actual heat score and Hessian

The mean-displacement score identity and smooth Gaussian posterior expectations
supply joint positive-variance/center regularity from original C² data and a
nonnegative Hessian lower bound. No extra derivative of the original potential,
upper Hessian bound, density evolution assumption, or heat-curvature assumption
is used. The final envelope results match the two first residual fields of
`OriginalHeatEvolutionData` on the full interval [3A/4,R].
-/

noncomputable section
open MeasureTheory Set Function InnerProductSpace
open scoped ContDiff

namespace AcceleratedLogConcave.Gibbs
open Conditional.Tilt Analysis.Poisson

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual score is jointly smooth at positive variance. Only the Gaussian
parameters are differentiated; the original potential remains merely C². -/
theorem contDiffOn_heatGradient {F : E → ℝ} {m : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v) :
    ContDiffOn ℝ ∞ (uncurry (fun t => gradient (heatPotential F t)))
      (gaussianDomain (E := E)) := by
  have hmean := contDiffOn_integral_heatPosterior hF hm hlo
    (continuous_id : Continuous (fun x : E => x)) 0 1 1 (by intro x; simp)
  have ht : ContDiffOn ℝ ∞ (fun p : ℝ × E => p.1) gaussianDomain :=
    contDiff_fst.contDiffOn
  have hs := (ht.inv (fun p hp => ne_of_gt hp)).smul
    (contDiff_snd.contDiffOn.sub hmean)
  apply hs.congr
  intro p hp
  exact (hasGradientAt_heatPotential hF hm hp hlo p.2).gradient

/-- The actual first Frechet derivative is jointly smooth at positive variance. -/
theorem contDiffOn_heatFDeriv {F : E → ℝ} {m : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => fderiv ℝ (heatPotential F p.1) p.2)
      gaussianDomain := by
  have hs := contDiffOn_heatGradient hF hm hlo
  apply ((toDual ℝ E).contDiff.comp_contDiffOn hs).congr
  intro p _
  exact (toDual_gradient (f := heatPotential F p.1) (x := p.2)).symm

/-- The genuine Hessian operator is jointly continuous at positive variance. -/
theorem continuousOn_heatHessian {F : E → ℝ} {m : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v) :
    ContinuousOn (uncurry (fun t => hessianOperator (heatPotential F t)))
      (gaussianDomain (E := E)) := by
  have hs := contDiffOn_heatFDeriv hF hm hlo
  intro p hp
  have hsAt := hs.contDiffAt (isOpen_gaussianDomain.mem_nhds hp)
  have haux : ContDiffAt ℝ ∞
      (uncurry (fun q : ℝ × E => fun c : E => fderiv ℝ (heatPotential F q.1) c))
      (p, p.2) := by
    convert hsAt.comp (p, p.2)
      ((contDiffAt_fst.fst).prodMk contDiffAt_snd) using 1
    rfl
  have hd := haux.fderiv (contDiffAt_snd :
    ContDiffAt ℝ ∞ (fun p : ℝ × E => p.2) p) (by simp)
  unfold Function.uncurry hessianOperator continuousLinearMapOfBilin
  exact (continuousAt_const.clm_comp hd.continuousAt).continuousWithinAt

/-- Exact original-data supplier for the gradient-continuity envelope field.
The upper endpoint R is arbitrary, in particular any R > A is retained. -/
theorem heatGradient_continuous_envelope {F : E → ℝ} {m A R : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (hA : 0 < A)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v) :
    ContinuousOn (uncurry (fun t => gradient (heatPotential F t)))
      (Icc (3 * A / 4) R ×ˢ (univ : Set E)) := by
  apply (contDiffOn_heatGradient hF hm hlo).continuousOn.mono
  intro p hp
  change 0 < p.1
  have ht := hp.1.1
  linarith

/-- Exact original-data supplier for the Hessian-continuity envelope field. -/
theorem heatHessian_continuous_envelope {F : E → ℝ} {m A R : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (hA : 0 < A)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v) :
    ContinuousOn (uncurry (fun t => hessianOperator (heatPotential F t)))
      (Icc (3 * A / 4) R ×ˢ (univ : Set E)) := by
  apply (continuousOn_heatHessian hF hm hlo).mono
  intro p hp
  change 0 < p.1
  have ht := hp.1.1
  linarith

end AcceleratedLogConcave.Gibbs
