import AcceleratedLogConcave.Kinetic.ConditionalContraction.PoissonTrace
import AcceleratedLogConcave.Kinetic.PhaseMomentumIBP

/-! The actual Poisson trace cancellation against arbitrary compact phase
tests. Integrability is local; no global score-times-gradient L2 premise. -/
noncomputable section
open MeasureTheory InnerProductSpace Set ProbabilityTheory
open scoped ContDiff RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.ConditionalContraction
open Analysis.WeightedGradient Analysis.Poisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem phase_weak_poisson_trace_test (μ : Measure E) [IsProbabilityMeasure μ]
    (V : E → ℝ) (hV : ContDiff ℝ 1 V)
    (hI : Integrable (fun x => Real.exp (-V x))) (hμ : μ = volume.tilted (fun x => -V x))
    (G : Lp E 2 μ) (g : Lp ℝ 2 μ)
    (hweak : ∀ v : Sobolev μ V hV hI hμ,
      inner ℝ G (closedGradient μ V hV hI hμ v) = inner ℝ g (v : Lp ℝ 2 μ))
    (R : Fin (Module.finrank ℝ E) → Lp E 2 μ)
    (hR : ∀ i, ((innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).compLp G, R i) ∈
      (closedGradient μ V hV hI hμ).graph)
    (φ : GaussianPhase E → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    Integrable (fun z => φ z * (∑ i, inner ℝ (R i z.1.1) ((stdOrthonormalBasis ℝ E) i) -
      fderiv ℝ V z.1.1 (G z.1.1))) (gaussianPhaseMeasure μ) ∧
    (∫ z, φ z * (∑ i, inner ℝ (R i z.1.1) ((stdOrthonormalBasis ℝ E) i) -
      fderiv ℝ V z.1.1 (G z.1.1)) ∂gaussianPhaseMeasure μ) =
        -∫ z, φ z * g z.1.1 ∂gaussianPhaseMeasure μ := by
  classical
  let b := stdOrthonormalBasis ℝ E
  have hp : MeasurePreserving (fun z : GaussianPhase E => z.1.1) (gaussianPhaseMeasure μ) μ :=
    (measurePreserving_fst (μ := μ) (ν := stdGaussian E)).comp
      (measurePreserving_fst (μ := μ.prod (stdGaussian E)) (ν := stdGaussian E))
  have hφLp : MemLp φ 2 (gaussianPhaseMeasure μ) :=
    hφ.continuous.memLp_of_hasCompactSupport hc
  have htrace : Integrable (fun z : GaussianPhase E =>
      φ z * ∑ i, inner ℝ (R i z.1.1) (b i)) (gaussianPhaseMeasure μ) := by
    have hi (i : Fin (Module.finrank ℝ E)) : Integrable
        (fun z : GaussianPhase E => φ z * inner ℝ (R i z.1.1) (b i))
        (gaussianPhaseMeasure μ) :=
      hφLp.integrable_mul (((Lp.memLp (R i)).inner_const (b i)).comp_measurePreserving hp)
    simpa only [Finset.mul_sum] using integrable_finsetSum Finset.univ (fun i _ => hi i)
  have hgrad : Continuous (gradient V) := by
    exact (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hV.continuous_fderiv one_ne_zero)
  have hcoef : MemLp (fun z : GaussianPhase E => φ z • gradient V z.1.1) 2
      (gaussianPhaseMeasure μ) :=
    (hφ.continuous.smul (hgrad.comp (continuous_fst.comp continuous_fst))).memLp_of_hasCompactSupport
      hc.smul_right
  have hscore : Integrable (fun z : GaussianPhase E => φ z * fderiv ℝ V z.1.1 (G z.1.1))
      (gaussianPhaseMeasure μ) := by
    have hG := (Lp.memLp G).comp_measurePreserving hp
    have hi := L2.integrable_inner (𝕜 := ℝ) (hG.toLp _) (hcoef.toLp _)
    apply hi.congr
    filter_upwards [hG.coeFn_toLp, hcoef.coeFn_toLp] with z hz hk
    rw [hz, hk, inner_smul_right, inner_gradient_right]
    rfl
  have hf := htrace.sub hscore
  have hg : Integrable (fun z : GaussianPhase E => φ z * g z.1.1) (gaussianPhaseMeasure μ) :=
    hφLp.integrable_mul ((Lp.memLp g).comp_measurePreserving hp)
  have hleft : Integrable (fun z : GaussianPhase E =>
      φ z * (∑ i, inner ℝ (R i z.1.1) (b i) - fderiv ℝ V z.1.1 (G z.1.1)))
      (gaussianPhaseMeasure μ) := by
    convert hf using 1
    funext z
    exact mul_sub _ _ _
  refine ⟨hleft, ?_⟩
  change (∫ z, _ ∂(μ.prod (stdGaussian E)).prod (stdGaussian E)) =
    -∫ z, _ ∂(μ.prod (stdGaussian E)).prod (stdGaussian E)
  rw [integral_prod_symm _ hleft, integral_prod_symm _ hg, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [hleft.prod_left_ae, hg.prod_left_ae] with e hfe hge
  rw [integral_prod_symm _ hfe, integral_prod_symm _ hge, ← integral_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p => by
    have hs : ContDiff ℝ 1 (fun x => φ ((x,p),e)) :=
      hφ.comp ((contDiff_id.prodMk contDiff_const).prodMk contDiff_const)
    have hcs : HasCompactSupport (fun x => φ ((x,p),e)) := by
      apply HasCompactSupport.of_support_subset_isCompact
        (hc.image (continuous_fst.comp continuous_fst))
      intro x hx
      exact ⟨((x,p),e), subset_tsupport _ hx, rfl⟩
    exact (weak_poisson_trace_test μ V hV hI hμ G g hweak R hR _ hs hcs).2

end AcceleratedLogConcave.Kinetic.ConditionalContraction
