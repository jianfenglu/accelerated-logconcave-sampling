import DirectW12.GaussianHessianRows

noncomputable section
open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace

namespace AcceleratedLogConcave.Analysis.Poisson
open WeightedGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem reconstruct_memLp {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (c : Fin (Module.finrank ℝ E) → Lp ℝ 2 ν) :
    MemLp (fun z => ∑ i, c i z • (stdOrthonormalBasis ℝ E) i) 2 ν := by
  apply memLp_finsetSum
  intro i _
  exact (ContinuousLinearMap.toSpanSingleton ℝ ((stdOrthonormalBasis ℝ E) i)).comp_memLp (c i)

/-- Finite orthonormal reconstruction of scalar L² coordinates. -/
def reconstructL2 {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (c : Fin (Module.finrank ℝ E) → Lp ℝ 2 ν) : Lp E 2 ν :=
  (reconstruct_memLp ν c).toLp _

theorem reconstructL2_coe {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (c : Fin (Module.finrank ℝ E) → Lp ℝ 2 ν) :
    reconstructL2 ν c =ᵐ[ν] fun z => ∑ i, c i z • (stdOrthonormalBasis ℝ E) i :=
  (reconstruct_memLp ν c).coeFn_toLp

theorem reconstructL2_coordinate {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (c : Fin (Module.finrank ℝ E) → Lp ℝ 2 ν) (i : Fin (Module.finrank ℝ E)) :
    (innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).compLp (reconstructL2 ν c) = c i := by
  apply Lp.ext
  filter_upwards [(innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).coeFn_compLp
    (reconstructL2 ν c), reconstructL2_coe ν c] with z hz hr
  rw [hz, hr]
  change inner ℝ _ (∑ j, c j z • (stdOrthonormalBasis ℝ E) j) = _
  simp [inner_sum, inner_smul_right, orthonormal_iff_ite.mp (stdOrthonormalBasis ℝ E).orthonormal]

theorem reconstructL2_norm_sq {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (c : Fin (Module.finrank ℝ E) → Lp ℝ 2 ν) :
    ‖reconstructL2 ν c‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
  have hpoint : ∀ᵐ z ∂ν, ‖reconstructL2 ν c z‖ ^ 2 = ∑ i, (c i z) ^ 2 := by
    have hall : ∀ i, ∀ᵐ z ∂ν, inner ℝ ((stdOrthonormalBasis ℝ E) i)
        (reconstructL2 ν c z) = c i z := by
      intro i
      have h := (innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).coeFn_compLp (reconstructL2 ν c)
      rw [reconstructL2_coordinate] at h
      filter_upwards [h] with z hz using hz.symm
    filter_upwards [ae_all_iff.mpr hall] with z hz
    rw [← (stdOrthonormalBasis ℝ E).sum_sq_inner_right]
    simp only [hz]
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]
  rw [integral_congr_ae hpoint, integral_finsetSum _ (fun i _ => (Lp.memLp (c i)).integrable_sq)]
  apply Finset.sum_congr rfl
  intro i _
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp [Real.norm_eq_abs, sq_abs]

variable [MeasurableSpace E] [BorelSpace E]

/-- The actual E-valued Gaussian action of weak Hessian rows. -/
def gaussianHessianVector (μ : Measure E) [IsProbabilityMeasure μ]
    (rows : Fin (Module.finrank ℝ E) → Lp E 2 μ) :
    Lp E 2 (μ.prod (ProbabilityTheory.stdGaussian E)) :=
  reconstructL2 _ (fun i => Kinetic.momentumEmbedding μ (rows i))

theorem gaussianHessianVector_coe (μ : Measure E) [IsProbabilityMeasure μ]
    (rows : Fin (Module.finrank ℝ E) → Lp E 2 μ) :
    gaussianHessianVector μ rows =ᵐ[μ.prod (ProbabilityTheory.stdGaussian E)]
      fun z => ∑ i, inner ℝ (rows i z.1) z.2 • (stdOrthonormalBasis ℝ E) i := by
  have hall := ae_all_iff.mpr (fun i => Kinetic.momentumEmbedding_coe μ (rows i))
  filter_upwards [reconstructL2_coe (μ.prod (ProbabilityTheory.stdGaussian E))
    (fun i => Kinetic.momentumEmbedding μ (rows i)), hall] with z hz ha
  rw [show gaussianHessianVector μ rows z =
    ∑ i, Kinetic.momentumEmbedding μ (rows i) z • (stdOrthonormalBasis ℝ E) i from hz]
  simp only [ha]

/-- Genuine weak Hessian rows, reconstructed in vector-valued Gaussian L²,
with exact energy and no dimensional loss. The closed-gradient witnesses
are retained. No coupled-path or endpoint assertion is made. -/
theorem gradientPoissonInverse_gaussian_hessian_vector
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
      (∀ i, (innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).compLp
        (gaussianHessianVector μ rows) = Kinetic.momentumEmbedding μ (rows i)) ∧
      ‖gaussianHessianVector μ rows‖ ^ 2 = ∑ i, ‖rows i‖ ^ 2 ∧
      ‖centerForcing μ g‖ ^ 2 = ‖gaussianHessianVector μ rows‖ ^ 2 +
        inner ℝ (hessianMultiplier μ V hV m 1 hlower hupper v) v ∧
      ‖gaussianHessianVector μ rows‖ ^ 2 ≤ ‖g‖ ^ 2 ∧
      inner ℝ (hessianMultiplier μ V hV m 1 hlower hupper v) v ≤ ‖g‖ ^ 2 := by
  obtain ⟨rows, hrows, he, hbound, hcurv⟩ :=
    gradientPoissonInverse_gaussian_hessian_rows μ V hV hI hμ m hm hlower hupper g
  have hn : ‖gaussianHessianVector μ rows‖ ^ 2 =
      ∑ i, ‖Kinetic.momentumEmbedding μ (rows i)‖ ^ 2 :=
    reconstructL2_norm_sq _ _
  refine ⟨rows, hrows, fun i => reconstructL2_coordinate _ _ i, ?_, ?_, ?_, hcurv⟩
  · simpa only [LinearIsometry.norm_map] using hn
  · rwa [hn]
  · rwa [hn]

end AcceleratedLogConcave.Analysis.Poisson
