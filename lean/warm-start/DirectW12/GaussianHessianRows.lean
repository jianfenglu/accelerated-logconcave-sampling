import AcceleratedLogConcave.Analysis.Poisson.GradientInverse
import AcceleratedLogConcave.Kinetic.GaussianEmbedding

/-!
# Actual weak Hessian rows, with Gaussian momentum energy

The rows are supplied by the actual weighted Poisson solution and retain
membership in the closed-gradient graph. The Gaussian first-chaos isometry
identifies their summed momentum energies with their Hilbert-Schmidt energy.
This is the source-level componentwise version of the spatial estimate used
by direct W12. No smooth Poisson solution or differentiated forcing is assumed.
The vector reconstruction / coupled-path integration is not claimed here.
-/

noncomputable section
open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace

namespace AcceleratedLogConcave.Analysis.Poisson
open WeightedGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The genuine inverse has genuine weak Hessian rows, and their Gaussian
momentum energy is at most the full forcing energy, with no gap loss. -/
theorem gradientPoissonInverse_gaussian_hessian_rows
    (μ : Measure E) [IsProbabilityMeasure μ]
    (V : E → ℝ) (hV : ContDiff ℝ 2 V)
    (hI : Integrable (fun x => Real.exp (-V x)))
    (hμ : μ = volume.tilted (fun x => -V x))
    (m : ℝ) (hm : 0 < m)
    (hlower : ∀ x w, m * ‖w‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x w w)
    (hupper : ∀ x w, fderiv ℝ (fderiv ℝ V) x w w ≤ 1 * ‖w‖ ^ 2)
    (g : Lp ℝ 2 μ) :
    let v := gradientPoissonInverse μ V hV hI hμ m 1 hm hlower hupper g
    ∃ rows : Fin (Module.finrank ℝ E) → Lp E 2 μ,
      (∀ i, ((innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).compLp v, rows i) ∈
        (closedGradient μ V (hV.of_le (by norm_num)) hI hμ).graph) ∧
      ‖centerForcing μ g‖ ^ 2 =
        (∑ i, ‖Kinetic.momentumEmbedding μ (rows i)‖ ^ 2) +
          inner ℝ (hessianMultiplier μ V hV m 1 hlower hupper v) v ∧
      (∑ i, ‖Kinetic.momentumEmbedding μ (rows i)‖ ^ 2) ≤ ‖g‖ ^ 2 ∧
      inner ℝ (hessianMultiplier μ V hV m 1 hlower hupper v) v ≤ ‖g‖ ^ 2 := by
  dsimp only
  let v := gradientPoissonInverse μ V hV hI hμ m 1 hm hlower hupper g
  have hs := poissonSolution_spec (μ := μ) (V := V) (hV := hV) (hI := hI)
    (hμ := hμ) (m := m) (L := 1) (hm := hm) (hlower := hlower) (hupper := hupper) g
  obtain ⟨rows, hrows, he⟩ := weak_poisson_bochner μ V hV hI hμ m 1 hm
    hlower hupper (poissonSolution μ V hV hI hμ m 1 hm hlower hupper g)
    (centerForcing μ g) hs.2
  change ‖centerForcing μ g‖ ^ 2 = (∑ i, ‖rows i‖ ^ 2) +
    inner ℝ (hessianMultiplier μ V hV m 1 hlower hupper v) v at he
  have hcurv : 0 ≤ inner ℝ (hessianMultiplier μ V hV m 1 hlower hupper v) v :=
    (sq_nonneg _).trans (hessianMultiplier_norm_sq_le_curvature_of_bounds μ V hV m 1
      hlower hupper (fun x w => (mul_nonneg hm.le (sq_nonneg _)).trans (hlower x w))
      (fun x w => by simpa only [one_mul] using hupper x w) v)
  have hsum : 0 ≤ ∑ i, ‖rows i‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hc : ‖centerForcing μ g‖ ^ 2 ≤ ‖g‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_centerForcing_le μ g)
  refine ⟨rows, hrows, ?_, ?_, ?_⟩
  · simpa only [LinearIsometry.norm_map] using he
  · simp only [LinearIsometry.norm_map]
    linarith
  · change inner ℝ (hessianMultiplier μ V hV m 1 hlower hupper v) v ≤ ‖g‖ ^ 2
    linarith

end AcceleratedLogConcave.Analysis.Poisson
