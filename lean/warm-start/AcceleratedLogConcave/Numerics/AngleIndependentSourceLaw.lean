import AcceleratedLogConcave.Numerics.AngleIndependentRotation

/-! Full actual observation law in independent midpoint/residual coordinates.
The test function can inspect the entire backward/observation/score triple,
not just one marginal. No moment assumption on the latent base law is added. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option autoImplicit false
namespace AcceleratedLogConcave.Numerics.MeanFlowLp
open Conditional AffineGraph AffineGraph.MeanGeometry
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

theorem lintegral_actual_observation_independent (d : Data ι m) (j : Fin m)
    (k : d.G.Kernel) (f : (E × E) × E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ w, f ((backward d j (d.G.rho k) w,
        observationFromNoise d k (backward d j (d.G.rho k) w) (w.2 j k)),
        score d (centerNode j) w) ∂seedMeasure d) =
      ∫⁻ s, ∫⁻ u, ∫⁻ a, ∫⁻ c,
        f ((d.G.rho k • u+Real.sqrt (d.G.variance k) •
              ((Real.sqrt (1+(d.G.rho k)^2))⁻¹ • (a+d.G.rho k • c)),
            u+Real.sqrt (d.G.variance k) •
              ((Real.sqrt (1+(d.G.rho k)^2))⁻¹ • (-d.G.rho k • a+c))),s)
        ∂stdGaussian E ∂stdGaussian E ∂baseLaw d.F d.x d.r ∂stdGaussian E := by
  rw [lintegral_actual_observation d j k f hf]
  apply lintegral_congr
  intro s
  apply lintegral_congr
  intro u
  let g : E × E → ℝ≥0∞ := fun p =>
    f ((d.G.rho k • u+Real.sqrt (d.G.variance k) • p.1,
      u+Real.sqrt (d.G.variance k) • p.2),s)
  have hg : Measurable g := hf.comp (by fun_prop)
  have he := (normalized_reconstruction_preserving d k).lintegral_comp hg
  rw [lintegral_prod _ hg.aemeasurable] at he
  have hp := lintegral_prod (μ := stdGaussian E) (ν := stdGaussian E) _
    (hg.comp (normalized_reconstruction_preserving d k).measurable).aemeasurable
  simp only [Function.comp_def] at hp
  rw [hp] at he
  exact he.symm
end AcceleratedLogConcave.Numerics.MeanFlowLp
