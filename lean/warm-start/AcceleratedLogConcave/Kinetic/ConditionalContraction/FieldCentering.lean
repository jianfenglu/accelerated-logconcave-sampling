import AcceleratedLogConcave.Kinetic.ConditionalContraction.FieldChaos

/-! The actual position projection annihilates the Hamiltonian chaoses. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.ConditionalContraction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [IsProbabilityMeasure μ]

omit [BorelSpace E] in
/-- Exact tensor pairing with a position observable. -/
theorem inner_phaseTensor_position (a g : Lp ℝ 2 μ)
    (b : Lp ℝ 2 ((stdGaussian E).prod (stdGaussian E))) :
    inner ℝ (phaseTensor μ a b) (positionEmbedding μ g) =
      inner ℝ a g * ∫ z, b z ∂(stdGaussian E).prod (stdGaussian E) := by
  rw [L2.inner_def]
  calc
    _ = ∫ z, (a z.1.1 * g z.1.1) * b (z.1.2,z.2) ∂gaussianPhaseMeasure μ := by
      apply integral_congr_ae
      filter_upwards [phaseTensor_coe μ a b, positionEmbedding_coe μ g] with z ha hg
      rw [ha, hg, real_inner_comm]
      change a z.1.1 * b (z.1.2,z.2) * g z.1.1 = _
      ring
    _ = ∫ z : E × (E × E), (a z.1 * g z.1) * b z.2 ∂μ.prod ((stdGaussian E).prod (stdGaussian E)) :=
      (measurePreserving_prodAssoc μ (stdGaussian E) (stdGaussian E)).integral_comp'
        (fun z : E × (E × E) => (a z.1 * g z.1) * b z.2)
    _ = _ := by
      rw [integral_prod_mul (fun x => a x * g x) (fun z => b z), L2.inner_def]
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun _ => mul_comm _ _)

omit [BorelSpace E] in
/-- A centered Gaussian tensor has exactly zero actual position average. -/
theorem gaussianAverage_phaseTensor_zero (a : Lp ℝ 2 μ)
    (b : Lp ℝ 2 ((stdGaussian E).prod (stdGaussian E)))
    (hb : (∫ z, b z ∂(stdGaussian E).prod (stdGaussian E)) = 0) :
    gaussianAverage μ (phaseTensor μ a b) = 0 := by
  apply ext_inner_left ℝ
  intro g
  change inner ℝ g ((positionEmbedding μ).toContinuousLinearMap.adjoint (phaseTensor μ a b)) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (positionEmbedding μ g) (phaseTensor μ a b) = _
  rw [real_inner_comm, inner_phaseTensor_position, hb, mul_zero, inner_zero_right]

private theorem mean_liftedCoordinate (u v : E) :
    (∫ z, Lp.compMeasurePreservingₗᵢ ℝ Prod.fst
      (measurePreserving_fst (ν := stdGaussian E)) (centeredQuadraticLp u v) z
      ∂(stdGaussian E).prod (stdGaussian E)) = 0 := by
  have he : Lp.compMeasurePreservingₗᵢ ℝ Prod.fst
      (measurePreserving_fst (ν := stdGaussian E)) (centeredQuadraticLp u v) =ᵐ[(stdGaussian E).prod (stdGaussian E)]
      fun z => centeredQuadratic u v z.1 :=
    (Lp.coeFn_compMeasurePreserving _ measurePreserving_fst).trans
      (measurePreserving_fst.quasiMeasurePreserving.ae (centeredQuadraticLp_coe u v))
  rw [integral_congr_ae he, integral_fun_fst, integral_centeredQuadratic]
  simp

private theorem mean_mixedCoordinate (u v : E) :
    (∫ z, mixedCoordinateLp u v z ∂(stdGaussian E).prod (stdGaussian E)) = 0 := by
  rw [integral_congr_ae (mixedCoordinateLp_coe u v)]
  change (∫ z, inner ℝ u z.1 * inner ℝ v z.2 ∂(stdGaussian E).prod (stdGaussian E)) = 0
  rw [integral_prod_mul (fun x => inner ℝ u x) (fun x => inner ℝ v x)]
  have hu := integral_strongDual_stdGaussian (innerSL ℝ u)
  change (∫ x, inner ℝ u x ∂stdGaussian E) = 0 at hu
  rw [hu, zero_mul]

/-- The actual position average annihilates centered quadratic fields. -/
theorem gaussianAverage_quadraticField {ι : Type*} [Fintype ι] (b : ι → E)
    (B : ι → ι → Lp ℝ 2 μ) : gaussianAverage μ (quadraticField μ b B) = 0 := by
  change gaussianAverage μ (∑ i, ∑ j, phaseTensor μ (B i j)
    (Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst
      (centeredQuadraticLp (b i) (b j)))) = 0
  simp only [map_sum, gaussianAverage_phaseTensor_zero μ _ _ (mean_liftedCoordinate _ _),
    Finset.sum_const_zero]

theorem gaussianAverage_mixedField {ι : Type*} [Fintype ι] (b : ι → E)
    (B : ι → ι → Lp ℝ 2 μ) : gaussianAverage μ (mixedField μ b B) = 0 := by
  simp only [mixedField, map_sum, gaussianAverage_phaseTensor_zero μ _ _ (mean_mixedCoordinate _ _),
    Finset.sum_const_zero]

/-- The microscopic Hamiltonian representative is genuinely orthogonal to
all position functions, not merely an algebraic centered expression. -/
theorem gaussianPositionProjection_hamiltonianField {ι : Type*} [Fintype ι] (b : ι → E)
    (B : ι → ι → Lp ℝ 2 μ) (s n : ℝ) :
    gaussianPositionProjection μ (hamiltonianField μ b B s n) = 0 := by
  change positionEmbedding μ (gaussianAverage μ (hamiltonianField μ b B s n)) = 0
  simp only [hamiltonianField, map_add, map_smul, gaussianAverage_quadraticField,
    gaussianAverage_mixedField, smul_zero, add_zero, map_zero]

end AcceleratedLogConcave.Kinetic.ConditionalContraction
