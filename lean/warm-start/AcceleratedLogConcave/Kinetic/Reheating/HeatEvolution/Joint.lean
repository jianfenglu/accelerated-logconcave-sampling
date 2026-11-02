import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.DerivativeBounds
import Mathlib.Analysis.Calculus.FDeriv.Partial

/-! Joint calculus follows from the actual continuous partial derivatives. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped Topology RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson AcceleratedLogConcave.HeatCalculus
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem hasDerivAt_along_of_partials {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {a b t : ℝ} {q qₜ : ℝ → X → ℝ}
    {qₓ : ℝ → X → X →L[ℝ] ℝ} (ht : t ∈ Ioo a b)
    (hₜ : ∀ s ∈ Ioo a b, ∀ x, HasDerivAt (fun r => q r x) (qₜ s x) s)
    (hₓ : ∀ s ∈ Ioo a b, ∀ x, HasFDerivAt (q s) (qₓ s x) x)
    (hcₜ : ContinuousOn (Function.uncurry qₜ) (Ioo a b ×ˢ (univ : Set X)))
    (hcₓ : ContinuousOn (Function.uncurry qₓ) (Ioo a b ×ˢ (univ : Set X)))
    {z : ℝ → X} {z' : X} (hz : HasDerivAt z z' t) :
    HasDerivAt (fun s => q s (z s)) (qₜ t (z t) + qₓ t (z t) z') t := by
  have hopen : IsOpen (Ioo a b ×ˢ (univ : Set X)) := isOpen_Ioo.prod isOpen_univ
  have hm : (t,z t) ∈ Ioo a b ×ˢ (univ : Set X) := ⟨ht,mem_univ _⟩
  have hs : ∀ᶠ p : ℝ × X in 𝓝 (t,z t), p.1 ∈ Ioo a b :=
    Filter.Eventually.mono (hopen.mem_nhds hm) fun _ h => h.1
  have hd := hasStrictFDerivAt_uncurry_coprod
    (f := q) (f₁ := fun s x => qₜ s x • (1 : ℝ →L[ℝ] ℝ)) (f₂ := qₓ)
    (hs.mono fun p hp => by
      change HasFDerivAt (fun s => q s p.2) (qₜ p.1 p.2 • (1 : ℝ →L[ℝ] ℝ)) p.1
      apply hasFDerivAt_iff_hasDerivAt.mpr
      simpa using hₜ p.1 hp p.2)
    (hs.mono fun p hp => hₓ p.1 hp p.2)
    ((hcₜ.continuousAt (hopen.mem_nhds hm)).smul continuousAt_const)
    (hcₓ.continuousAt (hopen.mem_nhds hm))
  have hh := hd.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hz)
  change HasDerivAt (fun s => q s (z s))
    ((qₜ t (z t) • (1 : ℝ →L[ℝ] ℝ)) 1 + qₓ t (z t) z') t at hh
  simpa using hh

/-- Compact Banach-valued Gaussian averages are jointly continuous in variance
and position, including zero variance. -/
theorem gaussianAverage_joint_continuous {K : Type*} [NormedAddCommGroup K]
    [NormedSpace ℝ K] {h : E → K} (hh : Continuous h) (hc : HasCompactSupport h) :
    Continuous (fun p : ℝ × E => ∫ g, h (p.2 + Real.sqrt p.1 • g) ∂stdGaussian E) := by
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous hh
  apply continuous_of_dominated (F := fun (p : ℝ × E) g => h (p.2 + Real.sqrt p.1 • g))
    (μ := stdGaussian E) (bound := fun _ : E => C)
    (fun p => (by fun_prop : Continuous (fun g : E => h (p.2+Real.sqrt p.1 • g))).aestronglyMeasurable)
    (fun p => Eventually.of_forall fun g => hC _) (integrable_const C)
  exact Eventually.of_forall fun g => by fun_prop

theorem heatAverage_joint_fderiv_continuous {h : E → ℝ} (hh : ContDiff ℝ 2 h)
    (hc : HasCompactSupport h) :
    Continuous (fun p : ℝ × E => fderiv ℝ (heatAverage h p.1) p.2) := by
  simp only [heatAverage_fderiv hh hc]
  exact gaussianAverage_joint_continuous (continuous_compactTest_fderiv hh) (hc.fderiv ℝ)

theorem heatAverage_joint_laplacian_continuous {h : E → ℝ} (hh : ContDiff ℝ 2 h)
    (hc : HasCompactSupport h) :
    Continuous (fun p : ℝ × E => compactTestLaplacian (heatAverage h p.1) p.2) := by
  simp only [heatAverage_laplacian hh hc]
  exact gaussianAverage_joint_continuous (continuous_compactTestLaplacian hh)
    (compactTestLaplacian_compactSupport hc)

end AcceleratedLogConcave.Kinetic.Reheating
