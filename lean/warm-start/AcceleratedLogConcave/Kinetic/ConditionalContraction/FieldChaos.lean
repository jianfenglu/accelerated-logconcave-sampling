import AcceleratedLogConcave.Kinetic.ConditionalContraction.GaussianChaos
import AcceleratedLogConcave.Kinetic.GaussianRows

/-!
# Position-dependent Gaussian chaos

Scalar L2 coefficients are tensored with genuine Gaussian L2 chaoses. The
resulting phase functions and their sharp row-energy estimates are actual L2
objects, suitable for the closed Hessian rows of the Poisson solution.
-/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.ConditionalContraction
section Tensor
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]

private theorem tensor_memLp (a : Lp ℝ 2 μ) (b : Lp ℝ 2 ν) :
    MemLp (fun z : X × Y => a z.1 * b z.2) 2 (μ.prod ν) := by
  apply (memLp_two_iff_integrable_sq
    (((Lp.memLp a).comp_fst ν).aestronglyMeasurable.mul
      ((Lp.memLp b).comp_snd μ).aestronglyMeasurable)).mpr
  simpa only [Pi.mul_apply, mul_pow] using (Lp.memLp a).integrable_sq.mul_prod (Lp.memLp b).integrable_sq

/-- Actual product function in the product-measure L2 space. -/
def tensorLp (a : Lp ℝ 2 μ) (b : Lp ℝ 2 ν) : Lp ℝ 2 (μ.prod ν) :=
  (tensor_memLp μ ν a b).toLp (fun z => a z.1 * b z.2)

theorem tensorLp_coe (a : Lp ℝ 2 μ) (b : Lp ℝ 2 ν) :
    tensorLp μ ν a b =ᵐ[μ.prod ν] fun z => a z.1 * b z.2 :=
  (tensor_memLp μ ν a b).coeFn_toLp

theorem inner_tensorLp (a c : Lp ℝ 2 μ) (b d : Lp ℝ 2 ν) :
    inner ℝ (tensorLp μ ν a b) (tensorLp μ ν c d) = inner ℝ a c * inner ℝ b d := by
  rw [L2.inner_def]
  calc
    _ = ∫ z, (a z.1 * c z.1) * (b z.2 * d z.2) ∂μ.prod ν := by
      apply integral_congr_ae
      filter_upwards [tensorLp_coe μ ν a b, tensorLp_coe μ ν c d] with z hz hw
      rw [hz, hw, real_inner_comm]
      change (a z.1 * b z.2) * (c z.1 * d z.2) = _
      ring
    _ = _ := by
      rw [integral_prod_mul (fun x => a x * c x) (fun y => b y * d y), L2.inner_def, L2.inner_def]
      simp only [RCLike.inner_apply, conj_trivial]
      congr 1 <;> apply integral_congr_ae <;> exact Filter.Eventually.of_forall (fun _ => mul_comm _ _)
end Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [IsProbabilityMeasure μ]

/-- Tensor a position coefficient with a function of the two Gaussian blocks,
using the source's exact phase coordinate order `((x,p),e)`. -/
def phaseTensor (a : Lp ℝ 2 μ) (b : Lp ℝ 2 ((stdGaussian E).prod (stdGaussian E))) :
    Lp ℝ 2 (gaussianPhaseMeasure μ) :=
  Lp.compMeasurePreservingₗᵢ ℝ MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc μ (stdGaussian E) (stdGaussian E))
    (tensorLp μ ((stdGaussian E).prod (stdGaussian E)) a b)

omit [BorelSpace E] in
theorem phaseTensor_coe (a : Lp ℝ 2 μ) (b : Lp ℝ 2 ((stdGaussian E).prod (stdGaussian E))) :
    phaseTensor μ a b =ᵐ[gaussianPhaseMeasure μ] fun z => a z.1.1 * b (z.1.2, z.2) := by
  exact (Lp.coeFn_compMeasurePreserving _
    (measurePreserving_prodAssoc μ (stdGaussian E) (stdGaussian E))).trans
    ((measurePreserving_prodAssoc μ (stdGaussian E) (stdGaussian E)).quasiMeasurePreserving.ae
      (tensorLp_coe μ ((stdGaussian E).prod (stdGaussian E)) a b))

omit [BorelSpace E] in
theorem inner_phaseTensor (a c : Lp ℝ 2 μ)
    (b d : Lp ℝ 2 ((stdGaussian E).prod (stdGaussian E))) :
    inner ℝ (phaseTensor μ a b) (phaseTensor μ c d) = inner ℝ a c * inner ℝ b d := by
  unfold phaseTensor
  exact ((Lp.compMeasurePreservingₗᵢ ℝ MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc μ (stdGaussian E) (stdGaussian E))).inner_map_map _ _).trans
      (inner_tensorLp _ _ _ _ _ _)

private def liftedCoordinate (u v : E) : Lp ℝ 2 ((stdGaussian E).prod (stdGaussian E)) :=
  Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst (centeredQuadraticLp u v)

private theorem inner_liftedCoordinate (u v w z : E) :
    inner ℝ (liftedCoordinate u v) (liftedCoordinate w z) =
      inner ℝ u w * inner ℝ v z + inner ℝ u z * inner ℝ v w := by
  unfold liftedCoordinate
  exact ((Lp.compMeasurePreservingₗᵢ ℝ Prod.fst
    (measurePreserving_fst (μ := stdGaussian E) (ν := stdGaussian E))).inner_map_map _ _).trans
    (inner_centeredQuadraticLp u v w z)

/-- Centered quadratic chaos with arbitrary actual position L2 matrix entries. -/
def quadraticField {ι : Type*} [Fintype ι] (b : ι → E) (B : ι → ι → Lp ℝ 2 μ) :
    Lp ℝ 2 (gaussianPhaseMeasure μ) :=
  ∑ i, ∑ j, phaseTensor μ (B i j) (liftedCoordinate (b i) (b j))

/-- Mixed momentum/auxiliary chaos with arbitrary position L2 matrix entries. -/
def mixedField {ι : Type*} [Fintype ι] (b : ι → E) (B : ι → ι → Lp ℝ 2 μ) :
    Lp ℝ 2 (gaussianPhaseMeasure μ) :=
  ∑ i, ∑ j, phaseTensor μ (B i j) (mixedCoordinateLp (b i) (b j))

omit [BorelSpace E] in
private theorem tensorSum_coe {ι : Type*} [Fintype ι]
    (B : ι → ι → Lp ℝ 2 μ)
    (Z : ι → ι → Lp ℝ 2 ((stdGaussian E).prod (stdGaussian E))) :
    (∑ i, ∑ j, phaseTensor μ (B i j) (Z i j)) =ᵐ[gaussianPhaseMeasure μ]
      fun z => ∑ i, ∑ j, B i j z.1.1 * Z i j (z.1.2, z.2) := by
  classical
  have hi (i : ι) : (∑ j, phaseTensor μ (B i j) (Z i j)) =ᵐ[gaussianPhaseMeasure μ]
      fun z => ∑ j, B i j z.1.1 * Z i j (z.1.2, z.2) := by
    apply (Lp.coeFn_finsetSum _ _).trans
    filter_upwards [ae_all_iff.mpr (fun j => phaseTensor_coe μ (B i j) (Z i j))] with z hz
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl (fun j _ => hz j)
  apply (Lp.coeFn_finsetSum _ _).trans
  filter_upwards [ae_all_iff.mpr hi] with z hz
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun i _ => hz i)

omit [BorelSpace E] in
private theorem momentumPair_preserving : MeasurePreserving
    (fun z : GaussianPhase E => (z.1.2, z.2)) (gaussianPhaseMeasure μ)
      ((stdGaussian E).prod (stdGaussian E)) :=
  (measurePreserving_snd (μ := μ)).comp
    (measurePreserving_prodAssoc μ (stdGaussian E) (stdGaussian E))

/-- Exact representative of the position-dependent centered quadratic chaos. -/
theorem quadraticField_coe {ι : Type*} [Fintype ι] (b : ι → E)
    (B : ι → ι → Lp ℝ 2 μ) :
    quadraticField μ b B =ᵐ[gaussianPhaseMeasure μ] fun z =>
      ∑ i, ∑ j, B i j z.1.1 *
        (inner ℝ (b i) z.1.2 * inner ℝ (b j) z.1.2 - inner ℝ (b i) (b j)) := by
  classical
  have hZ (i j : ι) : liftedCoordinate (b i) (b j) =ᵐ[(stdGaussian E).prod (stdGaussian E)]
      fun z => centeredQuadratic (b i) (b j) z.1 :=
    (Lp.coeFn_compMeasurePreserving _ measurePreserving_fst).trans
      (measurePreserving_fst.quasiMeasurePreserving.ae (centeredQuadraticLp_coe (b i) (b j)))
  filter_upwards [tensorSum_coe μ B (fun i j => liftedCoordinate (b i) (b j)),
    (momentumPair_preserving μ).quasiMeasurePreserving.ae
      (ae_all_iff.mpr (fun i => ae_all_iff.mpr (hZ i)))] with z hz hZz
  change (∑ i, ∑ j, phaseTensor μ (B i j) (liftedCoordinate (b i) (b j))) z = _
  rw [hz]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hZz i j]
  rfl

/-- Exact representative of the mixed position-dependent chaos. -/
theorem mixedField_coe {ι : Type*} [Fintype ι] (b : ι → E)
    (B : ι → ι → Lp ℝ 2 μ) :
    mixedField μ b B =ᵐ[gaussianPhaseMeasure μ] fun z =>
      ∑ i, ∑ j, B i j z.1.1 * (inner ℝ (b i) z.1.2 * inner ℝ (b j) z.2) := by
  classical
  filter_upwards [tensorSum_coe μ B (fun i j => mixedCoordinateLp (b i) (b j)),
    (momentumPair_preserving μ).quasiMeasurePreserving.ae
      (ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => mixedCoordinateLp_coe (b i) (b j))))]
    with z hz hZz
  change (∑ i, ∑ j, phaseTensor μ (B i j) (mixedCoordinateLp (b i) (b j))) z = _
  rw [hz]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hZz i j]
  rfl

theorem inner_quadraticField {ι : Type*} [Fintype ι] (b : ι → E)
    (hb : Orthonormal ℝ b) (B C : ι → ι → Lp ℝ 2 μ) :
    inner ℝ (quadraticField μ b B) (quadraticField μ b C) =
      ∑ i, ∑ j, (inner ℝ (B i j) (C i j) + inner ℝ (B i j) (C j i)) := by
  classical
  simp only [quadraticField, sum_inner, inner_sum, inner_phaseTensor,
    inner_liftedCoordinate, orthonormal_iff_ite.mp hb, mul_add, Finset.sum_add_distrib]
  simp
  rw [Finset.sum_comm (f := fun i j => inner ℝ (B j i) (C i j))]

theorem inner_mixedField {ι : Type*} [Fintype ι] (b : ι → E)
    (hb : Orthonormal ℝ b) (B C : ι → ι → Lp ℝ 2 μ) :
    inner ℝ (mixedField μ b B) (mixedField μ b C) =
      ∑ i, ∑ j, inner ℝ (B i j) (C i j) := by
  classical
  simp only [mixedField, sum_inner, inner_sum, inner_phaseTensor,
    inner_mixedCoordinateLp, orthonormal_iff_ite.mp hb]
  simp

theorem quadraticField_norm_sq_le {ι : Type*} [Fintype ι] (b : ι → E)
    (hb : Orthonormal ℝ b) (B : ι → ι → Lp ℝ 2 μ) :
    ‖quadraticField μ b B‖ ^ 2 ≤ 2 * ∑ i, ∑ j, ‖B i j‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_quadraticField μ b hb]
  simp only [real_inner_self_eq_norm_sq]
  calc
    _ ≤ ∑ i, ∑ j, (‖B i j‖^2 + (‖B i j‖^2 + ‖B j i‖^2) / 2) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have hi := real_inner_le_norm (B i j) (B j i)
      nlinarith [sq_nonneg (‖B i j‖ - ‖B j i‖)]
    _ = _ := by
      simp only [← Finset.sum_div, Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j => ‖B j i‖^2)]
      ring

theorem mixedField_norm_sq {ι : Type*} [Fintype ι] (b : ι → E)
    (hb : Orthonormal ℝ b) (B : ι → ι → Lp ℝ 2 μ) :
    ‖mixedField μ b B‖ ^ 2 = ∑ i, ∑ j, ‖B i j‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_mixedField μ b hb]
  simp only [real_inner_self_eq_norm_sq]

/-- Orthogonality survives arbitrary position-dependent L2 coefficients. -/
theorem inner_quadraticField_mixedField {ι : Type*} [Fintype ι] (b : ι → E)
    (B C : ι → ι → Lp ℝ 2 μ) :
    inner ℝ (quadraticField μ b B) (mixedField μ b C) = 0 := by
  simp only [quadraticField, mixedField, sum_inner, inner_sum, inner_phaseTensor,
    liftedCoordinate, inner_liftedQuadratic_mixedCoordinate, mul_zero, Finset.sum_const_zero]

/-- The two source microscopic Hamiltonian chaoses with L2 matrix coefficients. -/
def hamiltonianField {ι : Type*} [Fintype ι] (b : ι → E)
    (B : ι → ι → Lp ℝ 2 μ) (s n : ℝ) : Lp ℝ 2 (gaussianPhaseMeasure μ) :=
  -s • quadraticField μ b B + n • mixedField μ b B

theorem hamiltonianField_norm_sq_le {ι : Type*} [Fintype ι] (b : ι → E)
    (hb : Orthonormal ℝ b) (B : ι → ι → Lp ℝ 2 μ) (s n : ℝ) :
    ‖hamiltonianField μ b B s n‖ ^ 2 ≤ (2 * s ^ 2 + n ^ 2) * ∑ i, ∑ j, ‖B i j‖^2 := by
  have hq := quadraticField_norm_sq_le μ b hb B
  have hm := mixedField_norm_sq μ b hb B
  have ho := inner_quadraticField_mixedField μ b B B
  simp only [hamiltonianField, norm_add_sq_real, real_inner_smul_left, real_inner_smul_right,
    ho, mul_zero, add_zero, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, neg_sq, hm]
  nlinarith [mul_le_mul_of_nonneg_left hq (sq_nonneg s)]

/-- Coordinate entries of genuine L2 Hessian rows. -/
def rowCoefficients (R : Fin (Module.finrank ℝ E) → Lp E 2 μ)
    (i j : Fin (Module.finrank ℝ E)) : Lp ℝ 2 μ :=
  (innerSL ℝ ((stdOrthonormalBasis ℝ E) j)).compLp (R i)

omit [BorelSpace E] [IsProbabilityMeasure μ] in
theorem rowCoefficients_energy (R : Fin (Module.finrank ℝ E) → Lp E 2 μ) :
    (∑ i, ∑ j, ‖rowCoefficients μ R i j‖^2) = ∑ i, ‖R i‖^2 := by
  unfold rowCoefficients
  simp only [gradientComponents_norm_sq_sum]

/-- Actual phase L2 chaos from the weak Hessian rows, with the exact source
coefficient. No differentiability or symmetry of row representatives is assumed. -/
theorem hamiltonianField_rows_norm_sq_le (R : Fin (Module.finrank ℝ E) → Lp E 2 μ)
    (s n : ℝ) :
    ‖hamiltonianField μ (stdOrthonormalBasis ℝ E) (rowCoefficients μ R) s n‖ ^ 2 ≤
      (2 * s ^ 2 + n ^ 2) * ∑ i, ‖R i‖^2 := by
  have h := hamiltonianField_norm_sq_le μ (stdOrthonormalBasis ℝ E)
    (stdOrthonormalBasis ℝ E).orthonormal (rowCoefficients μ R) s n
  simpa only [rowCoefficients_energy] using h

end AcceleratedLogConcave.Kinetic.ConditionalContraction
