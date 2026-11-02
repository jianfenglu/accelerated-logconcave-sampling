import DirectW12.PairWeakTransport

noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace Set Function
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.DirectW12
open Analysis.WeightedGradient Analysis.Poisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual vector weak-Hessian cancellation against any compact C¹ vector
test on position/momentum space. Rows must be the actual closed gradients of
the coordinates of v. This is a proved graph theorem, not a transport premise. -/
theorem vector_graph_pair_hamiltonian_ibp
    (μ : Measure E) [IsProbabilityMeasure μ]
    (V : E → ℝ) (hV : ContDiff ℝ 1 V)
    (hI : Integrable (fun x => Real.exp (-V x))) (hμ : μ = volume.tilted (fun x => -V x))
    (v : Lp E 2 μ) (rows : Fin (Module.finrank ℝ E) → Lp E 2 μ)
    (hrows : ∀ i, ((innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).compLp v, rows i) ∈
      (closedGradient μ V hV hI hμ).graph)
    (ψ : E × E → E) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    Integrable (fun z => inner ℝ (v z.1) (fderiv ℝ ψ z (z.2, -gradient V z.1)))
      (μ.prod (stdGaussian E)) ∧
    Integrable (fun z => inner ℝ (gaussianHessianVector μ rows z) (ψ z))
      (μ.prod (stdGaussian E)) ∧
    (∫ z, inner ℝ (v z.1) (fderiv ℝ ψ z (z.2, -gradient V z.1)) ∂μ.prod (stdGaussian E)) =
      -(∫ z, inner ℝ (gaussianHessianVector μ rows z) (ψ z) ∂μ.prod (stdGaussian E)) := by
  classical
  let b := stdOrthonormalBasis ℝ E
  let c (i : Fin (Module.finrank ℝ E)) := (innerSL ℝ (b i)).compLp v
  let φ (i : Fin (Module.finrank ℝ E)) := fun z => inner ℝ (b i) (ψ z)
  have hφ i : ContDiff ℝ 1 (φ i) := (innerSL ℝ (b i)).contDiff.comp hψ
  have hcφ i : HasCompactSupport (φ i) := hc.comp_left (by simp)
  have hd i z : fderiv ℝ (φ i) z = (innerSL ℝ (b i)).comp (fderiv ℝ ψ z) :=
    ((innerSL ℝ (b i)).hasFDerivAt.comp z (hψ.differentiable_one z).hasFDerivAt).fderiv
  let A i (z : E × E) := c i z.1 * fderiv ℝ (φ i) z (z.2, -gradient V z.1)
  let B i (z : E × E) := φ i z * momentumEmbedding μ (rows i) z
  have hi i : Integrable (A i) (μ.prod (stdGaussian E)) ∧
      Integrable (B i) (μ.prod (stdGaussian E)) ∧
      (∫ z, A i z ∂μ.prod (stdGaussian E)) = -(∫ z, B i z ∂μ.prod (stdGaussian E)) :=
    graph_pair_hamiltonian_ibp μ V hV hI hμ (c i) (rows i) (hrows i) (φ i) (hφ i) (hcφ i)
  have hec : ∀ᵐ z ∂μ.prod (stdGaussian E), ∀ i, c i z.1 = inner ℝ (b i) (v z.1) := by
    have hh : ∀ i, ∀ᵐ x ∂μ, c i x = inner ℝ (b i) (v x) :=
      fun i => (innerSL ℝ (b i)).coeFn_compLp v
    exact measurePreserving_fst.quasiMeasurePreserving.ae (ae_all_iff.mpr hh)
  have hA : (fun z => ∑ i, A i z) =ᵐ[μ.prod (stdGaussian E)]
      fun z => inner ℝ (v z.1) (fderiv ℝ ψ z (z.2, -gradient V z.1)) := by
    filter_upwards [hec] with z hz
    simp only [A, hz, hd, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
    simpa only [real_inner_comm] using b.sum_inner_mul_inner (v z.1)
      (fderiv ℝ ψ z (z.2, -gradient V z.1))
  have heG : ∀ᵐ z ∂μ.prod (stdGaussian E), ∀ i,
      momentumEmbedding μ (rows i) z = inner ℝ (b i) (gaussianHessianVector μ rows z) := by
    have hh : ∀ i, ∀ᵐ z ∂μ.prod (stdGaussian E),
        momentumEmbedding μ (rows i) z = inner ℝ (b i) (gaussianHessianVector μ rows z) := by
      intro i
      have h := (innerSL ℝ (b i)).coeFn_compLp (gaussianHessianVector μ rows)
      rw [show (innerSL ℝ (b i)).compLp (gaussianHessianVector μ rows) =
        momentumEmbedding μ (rows i) from reconstructL2_coordinate _ _ i] at h
      exact h
    exact ae_all_iff.mpr hh
  have hB : (fun z => ∑ i, B i z) =ᵐ[μ.prod (stdGaussian E)]
      fun z => inner ℝ (gaussianHessianVector μ rows z) (ψ z) := by
    filter_upwards [heG] with z hz
    simp only [B, φ, hz]
    simpa only [real_inner_comm, mul_comm] using
      b.sum_inner_mul_inner (gaussianHessianVector μ rows z) (ψ z)
  refine ⟨(integrable_finsetSum Finset.univ (fun i _ => (hi i).1)).congr hA,
    (integrable_finsetSum Finset.univ (fun i _ => (hi i).2.1)).congr hB, ?_⟩
  rw [← integral_congr_ae hA, ← integral_congr_ae hB,
    integral_finsetSum Finset.univ (fun i _ => (hi i).1),
    integral_finsetSum Finset.univ (fun i _ => (hi i).2.1)]
  simp only [fun i => (hi i).2.2, Finset.sum_neg_distrib]

/-- The genuine closed weighted Poisson inverse supplies the vector cancellation
and its sharp dimension-free Gaussian Hessian energy for every L² forcing. -/
theorem gradientPoissonInverse_vector_hamiltonian_cancellation
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
      ‖gaussianHessianVector μ rows‖ ^ 2 ≤ ‖g‖ ^ 2 ∧
      ∀ (ψ : E × E → E), ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        Integrable (fun z => inner ℝ (v z.1) (fderiv ℝ ψ z (z.2, -gradient V z.1)))
          (μ.prod (stdGaussian E)) ∧
        Integrable (fun z => inner ℝ (gaussianHessianVector μ rows z) (ψ z))
          (μ.prod (stdGaussian E)) ∧
        (∫ z, inner ℝ (v z.1) (fderiv ℝ ψ z (z.2, -gradient V z.1)) ∂μ.prod (stdGaussian E)) =
          -(∫ z, inner ℝ (gaussianHessianVector μ rows z) (ψ z) ∂μ.prod (stdGaussian E)) := by
  obtain ⟨rows, hrows, _, _, _, hb, _⟩ :=
    gradientPoissonInverse_gaussian_hessian_vector μ V hV hI hμ m hm hlower hupper g
  exact ⟨rows, hrows, hb, fun ψ hψ hc => vector_graph_pair_hamiltonian_ibp
    μ V (hV.of_le (by norm_num)) hI hμ _ rows hrows ψ hψ hc⟩

end AcceleratedLogConcave.Kinetic.DirectW12
