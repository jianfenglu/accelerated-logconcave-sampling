import AcceleratedLogConcave.Kinetic.Corrector
import AcceleratedLogConcave.Kinetic.GaussianRows
import AcceleratedLogConcave.Kinetic.PhaseTestSlicing

/-!
# Genuine weak position gradients on Gaussian phase space

The derivative is defined by weighted integration by parts against every
compactly supported C1 function of all phase coordinates. Gradient coordinates
use the standard orthonormal basis of the position space.
-/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace Filter
open scoped RealInnerProductSpace ContDiff
namespace AcceleratedLogConcave.Kinetic
open Analysis.Poisson Analysis.WeightedGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The weighted divergence test in the actual position direction. -/
def positionTestDivergence (V : E → ℝ) (φ : GaussianPhase E → ℝ) (v : E)
    (z : GaussianPhase E) : ℝ :=
  fderiv ℝ φ z ((v, 0), 0) - φ z * fderiv ℝ V z.1.1 v

/-- Distributional position derivative, tested against all compact C1 phase
functions, not merely separated position-momentum tests. -/
def HasWeakPositionDerivative (μ : Measure E) (V : E → ℝ)
    (f g : GaussianPhase E → ℝ) (v : E) : Prop :=
  ∀ (φ : GaussianPhase E → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
    Integrable (fun z => φ z * g z) (gaussianPhaseMeasure μ) ∧
    Integrable (fun z => f z * positionTestDivergence V φ v z) (gaussianPhaseMeasure μ) ∧
    (∫ z, φ z * g z ∂gaussianPhaseMeasure μ) =
      -∫ z, f z * positionTestDivergence V φ v z ∂gaussianPhaseMeasure μ

/-- Coordinates of the genuine weak position gradient in an orthonormal basis. -/
def HasWeakPositionGradient (μ : Measure E) (V : E → ℝ)
    (f : Lp ℝ 2 (gaussianPhaseMeasure μ))
    (K : Fin (Module.finrank ℝ E) → Lp ℝ 2 (gaussianPhaseMeasure μ)) : Prop :=
  ∀ i, HasWeakPositionDerivative μ V f (K i) ((stdOrthonormalBasis ℝ E) i)

omit [BorelSpace E] in
theorem HasWeakPositionDerivative.congr_ae {μ : Measure E} {V : E → ℝ}
    {f g f' g' : GaussianPhase E → ℝ} {v : E}
    (h : HasWeakPositionDerivative μ V f g v)
    (hf : f =ᵐ[gaussianPhaseMeasure μ] f') (hg : g =ᵐ[gaussianPhaseMeasure μ] g') :
    HasWeakPositionDerivative μ V f' g' v := by
  intro φ hφ hc
  obtain ⟨hl, hr, he⟩ := h φ hφ hc
  have hleft : (fun z => φ z * g z) =ᵐ[gaussianPhaseMeasure μ] fun z => φ z * g' z := by
    filter_upwards [hg] with z hz
    rw [hz]
  have hright : (fun z => f z * positionTestDivergence V φ v z) =ᵐ[gaussianPhaseMeasure μ]
      fun z => f' z * positionTestDivergence V φ v z := by
    filter_upwards [hf] with z hz
    rw [hz]
  exact ⟨hl.congr hleft, hr.congr hright, by
    rw [← integral_congr_ae hleft, ← integral_congr_ae hright]
    exact he⟩

omit [BorelSpace E] in
theorem HasWeakPositionDerivative.finset_sum {μ : Measure E} {V : E → ℝ}
    {ι : Type*} (s : Finset ι) (f g : ι → GaussianPhase E → ℝ) (v : E)
    (h : ∀ j ∈ s, HasWeakPositionDerivative μ V (f j) (g j) v) :
    HasWeakPositionDerivative μ V (fun z => ∑ j ∈ s, f j z) (fun z => ∑ j ∈ s, g j z) v := by
  intro φ hφ hc
  have hl (j) (hj : j ∈ s) := (h j hj φ hφ hc).1
  have hr (j) (hj : j ∈ s) := (h j hj φ hφ hc).2.1
  have he (j) (hj : j ∈ s) := (h j hj φ hφ hc).2.2
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine ⟨integrable_finsetSum s hl, integrable_finsetSum s hr, ?_⟩
  rw [integral_finsetSum s hl, integral_finsetSum s hr, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl he


/-- Finite Gaussian-chaos expansion with the actual L2 component representatives. -/
theorem gaussianMomentumEmbedding_coe_components (μ : Measure E) [IsProbabilityMeasure μ]
    (G : Lp E 2 μ) :
    gaussianMomentumEmbedding μ G =ᵐ[gaussianPhaseMeasure μ] fun z =>
      ∑ j : Fin (Module.finrank ℝ E),
        ((innerSL ℝ ((stdOrthonormalBasis ℝ E) j)).compLp G) z.1.1 *
          inner ℝ ((stdOrthonormalBasis ℝ E) j) z.1.2 := by
  have hc : ∀ᵐ x ∂μ, ∀ j : Fin (Module.finrank ℝ E),
      ((innerSL ℝ ((stdOrthonormalBasis ℝ E) j)).compLp G) x =
        inner ℝ ((stdOrthonormalBasis ℝ E) j) (G x) :=
    Filter.eventually_all.mpr (fun j => (innerSL ℝ ((stdOrthonormalBasis ℝ E) j)).coeFn_compLp G)
  filter_upwards [gaussianMomentumEmbedding_coe μ G,
    measurePreserving_fst.quasiMeasurePreserving.ae
      (measurePreserving_fst.quasiMeasurePreserving.ae hc)] with z hG hcoord
  rw [hG]
  have hsum := (stdOrthonormalBasis ℝ E).sum_inner_mul_inner (G z.1.1) z.1.2
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hcoord j, real_inner_comm (G z.1.1)]


/-- Genuine distributional position differentiation of the first Gaussian
chaos. The proof uses arbitrary compact phase tests through weighted Fubini
integration by parts, then reconstructs the vector field from its components. -/
theorem gaussianMomentumEmbedding_hasWeakPositionGradient
    (μ : Measure E) [IsProbabilityMeasure μ] (V : E → ℝ)
    (hV : ContDiff ℝ 1 V) (hI : Integrable (fun x => Real.exp (-V x)))
    (hμ : μ = volume.tilted (fun x => -V x)) (G : Lp E 2 μ)
    (R : Fin (Module.finrank ℝ E) → Lp E 2 μ)
    (hR : ∀ j, ((innerSL ℝ ((stdOrthonormalBasis ℝ E) j)).compLp G, R j) ∈
      (closedGradient μ V hV hI hμ).graph) :
    HasWeakPositionGradient μ V (gaussianMomentumEmbedding μ G)
      (fun i => gaussianMomentumEmbedding μ (transposeGradientRows μ R i)) := by
  intro i
  let b := stdOrthonormalBasis ℝ E
  have hj (j : Fin (Module.finrank ℝ E)) : HasWeakPositionDerivative μ V
      (fun z => ((innerSL ℝ (b j)).compLp G) z.1.1 * inner ℝ (b j) z.1.2)
      (fun z => inner ℝ (R j z.1.1) (b i) * inner ℝ (b j) z.1.2) (b i) := by
    obtain ⟨u, hu, hDu⟩ := (LinearPMap.mem_graph_iff _).mp (hR j)
    intro φ hφ hc
    have hh := phase_test_weighted_ibp μ V hV hI hμ u (b j) (b i) φ hφ hc
    simpa only [hu, hDu, positionTestDivergence, mul_assoc] using hh
  have hsum := HasWeakPositionDerivative.finset_sum Finset.univ
    (fun j z => ((innerSL ℝ (b j)).compLp G) z.1.1 * inner ℝ (b j) z.1.2)
    (fun j z => inner ℝ (R j z.1.1) (b i) * inner ℝ (b j) z.1.2) (b i)
    (fun j _ => hj j)
  apply hsum.congr_ae (gaussianMomentumEmbedding_coe_components μ G).symm
  have hg : gaussianMomentumEmbedding μ (transposeGradientRows μ R i) =ᵐ[gaussianPhaseMeasure μ]
      fun z => ∑ j, inner ℝ (R j z.1.1) (b i) * inner ℝ (b j) z.1.2 := by
    filter_upwards [gaussianMomentumEmbedding_coe μ (transposeGradientRows μ R i),
      measurePreserving_fst.quasiMeasurePreserving.ae
        (measurePreserving_fst.quasiMeasurePreserving.ae (transposeGradientRows_coe μ R i))]
        with z hJ hT
    rw [hJ, hT]
    simp only [sum_inner, real_inner_smul_left]
    apply Finset.sum_congr rfl
    intro j hj
    rw [real_inner_comm (b i) (R j z.1.1)]
  exact hg.symm


/-- Sharp source estimate: the actual full-phase position derivative of the
adjoint corrector has exactly the base Hessian-row energy, bounded by the
macroscopic input energy. -/
theorem gaussianCorrectorAdjoint_weakPositionGradient_sharp
    (μ : Measure E) [IsProbabilityMeasure μ] (V : E → ℝ)
    (hV : ContDiff ℝ 2 V) (hI : Integrable (fun x => Real.exp (-V x)))
    (hμ : μ = volume.tilted (fun x => -V x))
    (m L : ℝ) (hm : 0 < m)
    (hlower : ∀ x a, m * ‖a‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x a a)
    (hupper : ∀ x a, fderiv ℝ (fderiv ℝ V) x a a ≤ L * ‖a‖ ^ 2)
    (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    ∃ R : Fin (Module.finrank ℝ E) → Lp E 2 μ,
      (∀ j, ((innerSL ℝ ((stdOrthonormalBasis ℝ E) j)).compLp
        (gradientPoissonInverse μ V hV hI hμ m L hm hlower hupper (gaussianAverage μ f)), R j) ∈
          (closedGradient μ V (hV.of_le (by norm_num)) hI hμ).graph) ∧
      HasWeakPositionGradient μ V ((gaussianCorrector μ V hV hI hμ m L hm hlower hupper).adjoint f)
        (fun i => gaussianMomentumEmbedding μ (transposeGradientRows μ R i)) ∧
      (∑ i, ‖gaussianMomentumEmbedding μ (transposeGradientRows μ R i)‖ ^ 2) =
        (∑ j, ‖R j‖ ^ 2) ∧
      (∑ j, ‖R j‖ ^ 2) ≤ ‖gaussianAverage μ f‖ ^ 2 := by
  obtain ⟨R, hR, hbound⟩ := gaussianCorrectorAdjoint_spatial_rows μ V hV hI hμ m L hm hlower hupper
    (positionEmbedding μ (gaussianAverage μ f))
  simp only [gaussianAverage_positionEmbedding] at hR
  rw [(positionEmbedding μ).norm_map] at hbound
  refine ⟨R, hR, ?_, gaussianTransposeGradientRows_norm_sq_sum μ R, hbound⟩
  rw [gaussianCorrector_adjoint]
  exact gaussianMomentumEmbedding_hasWeakPositionGradient μ V (hV.of_le (by norm_num)) hI hμ
    (gradientPoissonInverse μ V hV hI hμ m L hm hlower hupper (gaussianAverage μ f)) R hR

/-- The sharp adjoint estimate in terms of the actual phase position projection. -/
theorem gaussianCorrectorAdjoint_weakPositionGradient_macro_bound
    (μ : Measure E) [IsProbabilityMeasure μ] (V : E → ℝ)
    (hV : ContDiff ℝ 2 V) (hI : Integrable (fun x => Real.exp (-V x)))
    (hμ : μ = volume.tilted (fun x => -V x))
    (m L : ℝ) (hm : 0 < m)
    (hlower : ∀ x a, m * ‖a‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x a a)
    (hupper : ∀ x a, fderiv ℝ (fderiv ℝ V) x a a ≤ L * ‖a‖ ^ 2)
    (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    ∃ K : Fin (Module.finrank ℝ E) → Lp ℝ 2 (gaussianPhaseMeasure μ),
      HasWeakPositionGradient μ V ((gaussianCorrector μ V hV hI hμ m L hm hlower hupper).adjoint f) K ∧
      (∑ i, ‖K i‖ ^ 2) ≤ ‖gaussianPositionProjection μ f‖ ^ 2 := by
  obtain ⟨R, _, hgrad, heq, hbound⟩ :=
    gaussianCorrectorAdjoint_weakPositionGradient_sharp μ V hV hI hμ m L hm hlower hupper f
  refine ⟨fun i => gaussianMomentumEmbedding μ (transposeGradientRows μ R i), hgrad, ?_⟩
  rw [heq]
  change (∑ j, ‖R j‖ ^ 2) ≤ ‖positionEmbedding μ (gaussianAverage μ f)‖ ^ 2
  rw [(positionEmbedding μ).norm_map]
  exact hbound

/-- The adjoint corrector has an actual weak position gradient on full phase
space, and Gaussian covariance identifies its energy with the base Hessian
row energy. This proves the source contraction without a phase-domain premise. -/
theorem gaussianCorrectorAdjoint_weakPositionGradient_bound
    (μ : Measure E) [IsProbabilityMeasure μ] (V : E → ℝ)
    (hV : ContDiff ℝ 2 V) (hI : Integrable (fun x => Real.exp (-V x)))
    (hμ : μ = volume.tilted (fun x => -V x))
    (m L : ℝ) (hm : 0 < m)
    (hlower : ∀ x a, m * ‖a‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x a a)
    (hupper : ∀ x a, fderiv ℝ (fderiv ℝ V) x a a ≤ L * ‖a‖ ^ 2)
    (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    ∃ K : Fin (Module.finrank ℝ E) → Lp ℝ 2 (gaussianPhaseMeasure μ),
      HasWeakPositionGradient μ V ((gaussianCorrector μ V hV hI hμ m L hm hlower hupper).adjoint f) K ∧
      (∑ i, ‖K i‖ ^ 2) ≤ ‖f‖ ^ 2 := by
  obtain ⟨R, _, hgrad, heq, hbound⟩ :=
    gaussianCorrectorAdjoint_weakPositionGradient_sharp μ V hV hI hμ m L hm hlower hupper f
  refine ⟨fun i => gaussianMomentumEmbedding μ (transposeGradientRows μ R i), hgrad, ?_⟩
  rw [heq]
  apply hbound.trans
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
  exact ((gaussianAverage μ).le_opNorm f).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (gaussianAverage_norm_le μ) (norm_nonneg f))


/-- The Gaussian position embedding lifts genuine Sobolev derivatives to the
full phase weak-gradient domain. -/
theorem positionEmbedding_hasWeakPositionGradient
    (μ : Measure E) [IsProbabilityMeasure μ] (V : E → ℝ)
    (hV : ContDiff ℝ 1 V) (hI : Integrable (fun x => Real.exp (-V x)))
    (hμ : μ = volume.tilted (fun x => -V x)) (u₀ : Lp ℝ 2 μ) (G : Lp E 2 μ)
    (hgraph : (u₀, G) ∈ (closedGradient μ V hV hI hμ).graph) :
    HasWeakPositionGradient μ V (positionEmbedding μ u₀)
      (fun i => positionEmbedding μ ((innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).compLp G)) := by
  intro i
  obtain ⟨u, hu, hDu⟩ := (LinearPMap.mem_graph_iff _).mp hgraph
  have hraw : HasWeakPositionDerivative μ V (fun z => u₀ z.1.1)
      (fun z => inner ℝ (G z.1.1) ((stdOrthonormalBasis ℝ E) i)) ((stdOrthonormalBasis ℝ E) i) := by
    intro φ hφ hc
    simpa only [hu, hDu, positionTestDivergence] using
      phase_test_weighted_ibp_position μ V hV hI hμ u ((stdOrthonormalBasis ℝ E) i) φ hφ hc
  apply hraw.congr_ae (positionEmbedding_coe μ u₀).symm
  apply Filter.EventuallyEq.symm
  filter_upwards [positionEmbedding_coe μ ((innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).compLp G),
    measurePreserving_fst.quasiMeasurePreserving.ae
      (measurePreserving_fst.quasiMeasurePreserving.ae
        ((innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).coeFn_compLp G))] with z hI hc
  rw [hI, hc]
  exact real_inner_comm _ _

/-- The corrector itself has a genuine full-phase weak position gradient whose
L2 energy is bounded by that of the input. -/
theorem gaussianCorrector_weakPositionGradient_bound
    (μ : Measure E) [IsProbabilityMeasure μ] (V : E → ℝ)
    (hV : ContDiff ℝ 2 V) (hI : Integrable (fun x => Real.exp (-V x)))
    (hμ : μ = volume.tilted (fun x => -V x))
    (m L : ℝ) (hm : 0 < m)
    (hlower : ∀ x a, m * ‖a‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x a a)
    (hupper : ∀ x a, fderiv ℝ (fderiv ℝ V) x a a ≤ L * ‖a‖ ^ 2)
    (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    ∃ K : Fin (Module.finrank ℝ E) → Lp ℝ 2 (gaussianPhaseMeasure μ),
      HasWeakPositionGradient μ V (gaussianCorrector μ V hV hI hμ m L hm hlower hupper f) K ∧
      (∑ i, ‖K i‖ ^ 2) ≤ ‖f‖ ^ 2 := by
  let G := gaussianCorrectorPositionGradient μ V hV hI hμ m L hm hlower hupper f
  refine ⟨fun i => positionEmbedding μ ((innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).compLp G), ?_, ?_⟩
  · exact positionEmbedding_hasWeakPositionGradient μ V (hV.of_le (by norm_num)) hI hμ _ G
      (gaussianCorrectorPositionGradient_graph μ V hV hI hμ m L hm hlower hupper f)
  · rw [gaussianPositionGradientComponents_norm_sq_sum]
    have hnorm : ‖G‖ ≤ ‖f‖ := by
      have hh := (gaussianCorrectorPositionGradient μ V hV hI hμ m L hm hlower hupper).le_opNorm f
      exact hh.trans (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (gaussianCorrectorPositionGradient_norm_le μ V hV hI hμ m L hm hlower hupper) (norm_nonneg f))
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hnorm

end AcceleratedLogConcave.Kinetic
