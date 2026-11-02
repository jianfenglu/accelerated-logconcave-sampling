import AcceleratedLogConcave.Oracle.CovarianceSetup
import AcceleratedLogConcave.Oracle.SamplingExecutableStability
import AcceleratedLogConcave.Oracle.RecursiveExecutableDomain
import AcceleratedLogConcave.Conditional.GaussianAssembly
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! Gaussian recombination through the prescribed residual covariance root.
Both the child reference vector and the current residual vector are integrated.
The arbitrary coarse factor is kept, and no conditional independence from the
original designated momentum or the full consumed history is asserted. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Oracle.ResidualGaussianRecombination
open CovarianceSetup
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {α β : Type*} [Fintype α] [Fintype β] {d : ℕ}

private def blockLinear (R : Matrix α β ℝ) :
    PiLp 2 (fun _ : β => Point d) →ₗ[ℝ] PiLp 2 (fun _ : α => Point d) where
  toFun x := WithLp.toLp 2 (fun i => ∑ j, R i j • x j)
  map_add' x y := by
    ext i
    simp [Finset.sum_add_distrib, smul_add]
  map_smul' c x := by
    ext i
    simp [Finset.smul_sum, smul_smul, mul_comm]

private theorem transpose_energy [DecidableEq α] (R : Matrix α β ℝ)
    (hR : R * R.transpose = 1) (x : α → Point d) :
    (∑ j, ‖∑ i, R i j • x i‖^2) = ∑ i, ‖x i‖^2 := by
  have hrow (i k : α) : (∑ j, R i j * R k j) = if i=k then 1 else 0 := by
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
      congrArg (fun A : Matrix α α ℝ => A i k) hR
  simp_rw [← real_inner_self_eq_norm_sq, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right]
  calc
    (∑ j, ∑ i, ∑ k, R i j * (R k j * inner ℝ (x i) (x k))) =
        ∑ i, ∑ k, (∑ j, R i j * R k j) * inner ℝ (x i) (x k) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i, inner ℝ (x i) (x i) := by simp [hrow]

private def transposeIsometry [DecidableEq α] (R : Matrix α β ℝ)
    (hR : R * R.transpose = 1) :
    PiLp 2 (fun _ : α => Point d) →ₗᵢ[ℝ] PiLp 2 (fun _ : β => Point d) :=
  { blockLinear R.transpose with
    norm_map' := fun x => by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      simpa only [PiLp.norm_sq_eq_of_L2, blockLinear, LinearMap.coe_mk,
        AddHom.coe_mk, PiLp.toLp_apply, Matrix.transpose_apply] using transpose_energy R hR x }

private theorem gaussian_adjoint_isometry {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (g : F →ₗᵢ[ℝ] E) :
    (stdGaussian E).map g.toContinuousLinearMap.adjoint = stdGaussian F := by
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_eq_charFunDual_toDualMap, charFunDual_map, charFunDual_stdGaussian,
    charFun_stdGaussian]
  have hd : (InnerProductSpace.toDualMap ℝ F t).comp g.toContinuousLinearMap.adjoint =
      InnerProductSpace.toDualMap ℝ E (g t) := by
    ext x
    exact g.toContinuousLinearMap.adjoint_inner_right t x
  rw [hd, (InnerProductSpace.toDualMap ℝ E).norm_map, g.norm_map]

private theorem adjoint_transposeIsometry [DecidableEq α] (R : Matrix α β ℝ)
    (hR : R * R.transpose = 1) (x : PiLp 2 (fun _ : β => Point d)) :
    (transposeIsometry R hR).toContinuousLinearMap.adjoint x = blockLinear R x := by
  apply ext_inner_right ℝ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  change (∑ j, inner ℝ (x j) (∑ i, R i j • y i)) =
    ∑ i, inner ℝ (∑ j, R i j • x j) (y i)
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  exact Finset.sum_comm

/-- A rectangular real coisometry preserves the full joint law of vector
Gaussian blocks. The proof constructs the transpose isometry and integrates
its adjoint; no output distribution certificate is assumed. -/
theorem matrix_preserving [DecidableEq α] (R : Matrix α β ℝ)
    (hR : R * R.transpose = 1) :
    MeasurePreserving (fun z : β → Point d => fun i => ∑ j, R i j • z j)
      (Measure.pi (fun _ : β => stdGaussian (Point d)))
      (Measure.pi (fun _ : α => stdGaussian (Point d))) := by
  have hm : Measurable (fun z : β → Point d => fun i => ∑ j, R i j • z j) := by
    fun_prop
  refine ⟨hm, ?_⟩
  have ht : Measurable (WithLp.toLp 2 : (α → Point d) → PiLp 2 (fun _ : α => Point d)) :=
    (MeasurableEquiv.toLp 2 (α → Point d)).measurable
  have ht' : Measurable (WithLp.toLp 2 : (β → Point d) → PiLp 2 (fun _ : β => Point d)) :=
    (MeasurableEquiv.toLp 2 (β → Point d)).measurable
  apply (MeasurableEquiv.toLp 2 (α → Point d)).map_measurableEquiv_injective
  rw [MeasurableEquiv.coe_toLp, Measure.map_map ht hm,
    Conditional.GaussianAssembly.pi_stdGaussian_toLp]
  have hg := gaussian_adjoint_isometry (transposeIsometry (d := d) R hR)
  rw [← Conditional.GaussianAssembly.pi_stdGaussian_toLp,
    Measure.map_map (by fun_prop) ht'] at hg
  convert hg using 1
  congr 1
  funext x
  exact (adjoint_transposeIsometry R hR (WithLp.toLp 2 x)).symm

variable {n : ℕ}

/-- The actual normalized coefficient matrix, including both complete blocks. -/
def coefficients (A : Mat n) (rho a : ℝ) : Matrix (Fin n) (Fin n ⊕ Fin n) ℝ :=
  Matrix.fromCols ((sigma n rho a / rho) • A) (rho⁻¹ • residualRoot A rho a)

theorem coefficients_rows (A : Mat n) {rho a : ℝ} (hrho : 0 < rho) (ha : 0 < a)
    (hA : ∀ i, ∑ j, |A i j| ≤ a) :
    coefficients A rho a * (coefficients A rho a).transpose = 1 := by
  have hQ := (residual_root_identity A hrho.le ha hA).2
  rw [coefficients, Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows]
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hQ]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, residualCovariance, Matrix.sub_apply,
    smul_eq_mul]
  field_simp
  ring

/-- Exact reference-only recombination, with the prescribed root. The raw
reference and current residual arrays remain available to the caller. -/
def recombine (A : Mat n) (rho a : ℝ)
    (gz : (Fin n → Point d) × (Fin n → Point d)) (i : Fin n) : Point d :=
  rho⁻¹ • ((∑ j, A i j • (sigma n rho a • gz.1 j)) +
    ∑ j, residualRoot A rho a i j • gz.2 j)

theorem recombine_measurable (A : Mat n) (rho a : ℝ) :
    Measurable (recombine (d := d) A rho a) := by
  unfold recombine
  fun_prop

/-- The full next comparison vector has its joint standard Gaussian law,
proved from the actual covariance identity and both fresh Gaussian blocks. -/
theorem recombine_preserving (A : Mat n) {rho a : ℝ} (hrho : 0 < rho) (ha : 0 < a)
    (hA : ∀ i, ∑ j, |A i j| ≤ a) :
    MeasurePreserving (recombine (d := d) A rho a)
      ((Measure.pi (fun _ : Fin n => stdGaussian (Point d))).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (Point d))))
      (Measure.pi (fun _ : Fin n => stdGaussian (Point d))) := by
  have hp := (matrix_preserving (d := d) (coefficients A rho a)
    (coefficients_rows A hrho ha hA)).comp
      (measurePreserving_sumPiEquivProdPi_symm
        (fun _ : Fin n ⊕ Fin n => stdGaussian (Point d)))
  convert hp using 1
  funext gz i
  simp only [Function.comp_apply, MeasurableEquiv.coe_sumPiEquivProdPi_symm,
    coefficients, Fintype.sum_sum_type, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr,
    Matrix.smul_apply, smul_eq_mul, recombine, smul_add, Finset.smul_sum, smul_smul]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    congr 1
    ring

/-- Tensor the recombination with the identity on arbitrary coarse data. No
independence of the comparison vector from the full original history is added. -/
theorem recombine_coarse_preserving {H : Type*} [MeasurableSpace H]
    (μ : Measure H) [SFinite μ] (A : Mat n) {rho a : ℝ} (hrho : 0 < rho) (ha : 0 < a)
    (hA : ∀ i, ∑ j, |A i j| ≤ a) :
    MeasurePreserving (Prod.map id (recombine (d := d) A rho a))
      (μ.prod ((Measure.pi (fun _ : Fin n => stdGaussian (Point d))).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (Point d)))))
      (μ.prod (Measure.pi (fun _ : Fin n => stdGaussian (Point d)))) :=
  (MeasurePreserving.id μ).prod (recombine_preserving A hrho ha hA)

/-- The chronological association: the residual is the just-consumed fresh
factor after the retained coarse/reference law has already been proved. -/
theorem recombine_coarse_assoc_preserving {H : Type*} [MeasurableSpace H]
    (μ : Measure H) [SFinite μ] (A : Mat n) {rho a : ℝ} (hrho : 0 < rho) (ha : 0 < a)
    (hA : ∀ i, ∑ j, |A i j| ≤ a) :
    MeasurePreserving
      (fun z : (H × (Fin n → Point d)) × (Fin n → Point d) =>
        (z.1.1,recombine A rho a (z.1.2,z.2)))
      ((μ.prod (Measure.pi (fun _ : Fin n => stdGaussian (Point d)))).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (Point d))))
      (μ.prod (Measure.pi (fun _ : Fin n => stdGaussian (Point d)))) :=
  (recombine_coarse_preserving μ A hrho ha hA).comp
    (measurePreserving_prodAssoc μ (Measure.pi (fun _ : Fin n => stdGaussian (Point d)))
      (Measure.pi (fun _ : Fin n => stdGaussian (Point d))))

/-- Apply the proved recombination to a projection of an arbitrary full
retained sample. The entire original sample can remain in its surrounding
coupling; this theorem only computes the required coarse/comparison marginal. -/
theorem projected_recombine_law {W H : Type*} [MeasurableSpace W] [MeasurableSpace H]
    (μ : Measure W) (ν : Measure H) [SFinite ν]
    (coarse : W → H) (hc : Measurable coarse)
    (reference residual : W → Fin n → Point d)
    (hg : Measurable reference) (hz : Measurable residual)
    (A : Mat n) {rho a : ℝ} (hrho : 0 < rho) (ha : 0 < a)
    (hA : ∀ i, ∑ j, |A i j| ≤ a)
    (hproject : μ.map (fun z => ((coarse z,reference z),residual z)) =
      (ν.prod (Measure.pi (fun _ : Fin n => stdGaussian (Point d)))).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (Point d)))) :
    μ.map (fun z => (coarse z,recombine A rho a (reference z,residual z))) =
      ν.prod (Measure.pi (fun _ : Fin n => stdGaussian (Point d))) := by
  have hp : MeasurePreserving (fun z => ((coarse z,reference z),residual z)) μ
      ((ν.prod (Measure.pi (fun _ : Fin n => stdGaussian (Point d)))).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (Point d)))) :=
    ⟨(hc.prodMk hg).prodMk hz,hproject⟩
  exact ((recombine_coarse_assoc_preserving ν A hrho ha hA).comp hp).map_eq

/-- The executable sampling matrix has the required public row bound; the
noise is the literal private noise and the width is its prescribed sigma. -/
theorem sampling_recombine_preserving (S : Numerics.AffineGraph.SamplingGeometry m)
    (e : Fin n ≃ S.Node) (r Ds : ℝ) (hm : 0 < m) (hr : 0 < r) (hDs : 0 < Ds) :
    MeasurePreserving
      (recombine (d := d) (SourceExecutableTables.samplingMatrix S e r)
        (SourceExecutableTables.samplingNoise S r Ds) (r^2))
      ((Measure.pi (fun _ : Fin n => stdGaussian (Point d))).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (Point d))))
      (Measure.pi (fun _ : Fin n => stdGaussian (Point d))) :=
  recombine_preserving _ (RecursiveExecutableDomain.sampling_noise_pos S r Ds hr hDs)
    (sq_pos_of_pos hr) (FixedTapeSampling.sampling_matrix_mass_le S e r hm hr.le)

end AcceleratedLogConcave.Oracle.ResidualGaussianRecombination
