/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.Option

/-!
# Prescribed-input Gaussian assembly

`active_eq_sqrt_sum` identifies the literal positive-square-root split for every fixed input.
`budget_residual_same_input` recovers the residual from that same input.
`literal_split_joint_law` and `manuscript_joint_law` average an explicitly independent standard
Gaussian input and fresh noise. No fixed-input standard-output law is asserted.
The finite index may be empty and the physical real Hilbert space may have dimension zero.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace AcceleratedLogConcave.Conditional.GaussianAssembly
variable {ι : Type*} [Fintype ι]

def mass (a : ι → ℝ) : ℝ := ∑ i, (a i)^2
def reserve (a : ι → ℝ) : ℝ := Real.sqrt (1 - mass a)

lemma mass_nonneg (a : ι → ℝ) : 0 ≤ mass a := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
lemma reserve_pos {a : ι → ℝ} (ha : mass a < 1) : 0 < reserve a :=
  Real.sqrt_pos.mpr (sub_pos.mpr ha)
lemma reserve_sq {a : ι → ℝ} (ha : mass a ≤ 1) : reserve a ^ 2 = 1 - mass a :=
  Real.sq_sqrt (sub_nonneg.mpr ha)
lemma reserve_add_one_ne_zero {a : ι → ℝ} (ha : mass a < 1) : 1 + reserve a ≠ 0 := by
  have := reserve_pos ha
  positivity

variable [DecidableEq ι]

/-- Explicit rank-one formula for the positive square root of I-aa^T. -/
def complement (a : ι → ℝ) : Matrix ι ι ℝ :=
  1 - (1 / (1 + reserve a)) • vecMulVec a a

lemma complement_apply (a : ι → ℝ) (i j : ι) :
    complement a i j = (if i = j then 1 else 0) - a i * a j / (1 + reserve a) := by
  simp [complement, Matrix.one_apply, Matrix.vecMulVec, div_eq_mul_inv]
  ring

lemma complement_mulVec (a x : ι → ℝ) :
    (complement a) *ᵥ x = fun i => x i - a i * (a ⬝ᵥ x) / (1 + reserve a) := by
  ext i
  simp [complement, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
    div_eq_mul_inv]
  ring

lemma complement_posSemidef {a : ι → ℝ} (ha : mass a < 1) : (complement a).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simp [Matrix.conjTranspose_apply, complement_apply, eq_comm, mul_comm]
  · intro x
    have hcs : (a ⬝ᵥ x)^2 ≤ mass a * (∑ i, (x i)^2) := by
      exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have hr := reserve_pos ha
    have hd : 0 < 1 + reserve a := by positivity
    have hx : 0 ≤ ∑ i, (x i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hm : mass a ≤ 1 + reserve a := by linarith
    have hb : (a ⬝ᵥ x)^2 / (1 + reserve a) ≤ ∑ i, (x i)^2 := by
      apply (div_le_iff₀ hd).mpr
      exact hcs.trans (by nlinarith)
    rw [complement_mulVec]
    have he : (∑ i, x i * (a i * (a ⬝ᵥ x) / (1 + reserve a))) =
        (a ⬝ᵥ x)^2 / (1 + reserve a) := by
      simp_rw [mul_div_assoc, ← mul_assoc]
      rw [← Finset.sum_mul]
      simp [dotProduct, mul_comm, pow_two, mul_div_assoc]
    simp only [star_trivial, dotProduct, mul_sub, Finset.sum_sub_distrib]
    change 0 ≤ (∑ i, x i * x i) - (∑ i, x i * (a i * (a ⬝ᵥ x) / (1 + reserve a)))
    rw [he]
    simpa only [← sq] using sub_nonneg.mpr hb

lemma complement_sq {a : ι → ℝ} (ha : mass a < 1) :
    complement a * complement a = 1 - vecMulVec a a := by
  have hd := reserve_add_one_ne_zero ha
  have hr := reserve_sq ha.le
  have hc : (1 / (1 + reserve a))^2 * mass a - 2 / (1 + reserve a) = -1 := by
    field_simp
    nlinarith
  ext i j
  simp only [complement, sub_mul, mul_sub, one_mul, mul_one, smul_mul,
    Matrix.mul_smul, smul_smul, vecMulVec_mul_vecMulVec]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, vecMulVec_apply, Pi.smul_apply]
  have haa : a ⬝ᵥ a = mass a := by simp [dotProduct, mass, pow_two]
  rw [haa]
  linear_combination (a i * a j) * hc

lemma complement_eq_sqrt {a : ι → ℝ} (ha : mass a < 1) :
    complement a = CFC.sqrt (1 - vecMulVec a a) :=
  (CFC.sqrt_unique (complement_sq ha) (complement_posSemidef ha).nonneg).symm

section Vector
omit [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def noiseSum (a : ι → ℝ) (z : ι → E) : E := ∑ i, a i • z i

def active (a : ι → ℝ) (p : E) (z : ι → E) (i : ι) : E :=
  z i + a i • (p - (1 / (1 + reserve a)) • noiseSum a z)

def residual (a : ι → ℝ) (p : E) (z : ι → E) : E :=
  reserve a • p - noiseSum a z

lemma active_weighted_sum (a : ι → ℝ) (p : E) (z : ι → E) :
    (∑ i, a i • active a p z i) = noiseSum a z +
      mass a • (p - (1 / (1 + reserve a)) • noiseSum a z) := by
  simp only [active, smul_add, smul_smul, Finset.sum_add_distrib, ← Finset.sum_smul,
    mass, pow_two, noiseSum]

lemma residual_reconstruction {a : ι → ℝ} (ha : mass a < 1) (p : E) (z : ι → E) :
    p = (∑ i, a i • active a p z i) + reserve a • residual a p z := by
  have hr := reserve_sq ha.le
  have hd := reserve_add_one_ne_zero ha
  rw [active_weighted_sum]
  simp only [residual, smul_sub, smul_smul]
  have hc : mass a * (1 / (1 + reserve a)) + reserve a = 1 := by
    field_simp
    nlinarith
  have hc' : mass a + reserve a * reserve a = 1 := by nlinarith
  match_scalars <;> nlinarith

lemma residual_eq_same_input {a : ι → ℝ} (ha : mass a < 1) (p : E) (z : ι → E) :
    residual a p z = (reserve a)⁻¹ • (p - ∑ i, a i • active a p z i) := by
  rw [eq_sub_iff_add_eq.mpr (residual_reconstruction ha p z).symm]
  rw [sub_sub_cancel, inv_smul_smul₀ (ne_of_gt (reserve_pos ha))]

lemma norm_sq_smul (c : ℝ) (x : E) : ‖c • x‖^2 = c^2 * ‖x‖^2 := by
  simp [norm_smul, mul_pow]

lemma sum_norm_active_sq (a : ι → ℝ) (p : E) (z : ι → E) :
    (∑ i, ‖active a p z i‖^2) = (∑ i, ‖z i‖^2) +
      2 * ⟪noiseSum a z, p - (1 / (1 + reserve a)) • noiseSum a z⟫ +
      mass a * ‖p - (1 / (1 + reserve a)) • noiseSum a z‖^2 := by
  simp only [active, norm_add_sq_real, real_inner_smul_right, norm_sq_smul,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    noiseSum, sum_inner, real_inner_smul_left, mass]

lemma assembly_norm_sq {a : ι → ℝ} (ha : mass a < 1) (p : E) (z : ι → E) :
    ‖residual a p z‖^2 + (∑ i, ‖active a p z i‖^2) = ‖p‖^2 + ∑ i, ‖z i‖^2 := by
  have hr := reserve_sq ha.le
  have hd := reserve_add_one_ne_zero ha
  rw [sum_norm_active_sq]
  simp only [residual, norm_sub_sq_real, norm_sq_smul, real_inner_smul_left,
    inner_sub_right, real_inner_smul_right]
  rw [real_inner_comm (noiseSum a z) p, real_inner_self_eq_norm_sq]
  rw [show mass a = 1 - reserve a ^ 2 by linarith]
  field_simp
  ring

/-- The literal output, with the residual at `none` and active coordinates at `some i`. -/
def assemble (a : ι → ℝ) (x : Option ι → E) : Option ι → E
  | none => residual a (x none) (fun i => x (some i))
  | some i => active a (x none) (fun j => x (some j)) i

lemma noiseSum_add (a : ι → ℝ) (z w : ι → E) :
    noiseSum a (z + w) = noiseSum a z + noiseSum a w := by
  simp [noiseSum, smul_add, Finset.sum_add_distrib]

lemma noiseSum_smul (a : ι → ℝ) (c : ℝ) (z : ι → E) :
    noiseSum a (c • z) = c • noiseSum a z := by
  simp [noiseSum, Finset.smul_sum, smul_smul, mul_comm]

def assemblyLinearMap (a : ι → ℝ) :
    PiLp 2 (fun _ : Option ι => E) →ₗ[ℝ] PiLp 2 (fun _ : Option ι => E) where
  toFun x := WithLp.toLp 2 (assemble a x)
  map_add' x y := by
    ext i
    cases i <;> simp [assemble, residual, active, noiseSum, smul_add,
      Finset.sum_add_distrib] <;> module
  map_smul' c x := by
    ext i
    cases i <;> simp [assemble, residual, active, noiseSum, Finset.smul_sum,
      smul_sub, smul_add, smul_smul, mul_comm, mul_left_comm, mul_assoc]

lemma assemblyLinearMap_norm {a : ι → ℝ} (ha : mass a < 1)
    (x : PiLp 2 (fun _ : Option ι => E)) : ‖assemblyLinearMap a x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simpa only [PiLp.norm_sq_eq_of_L2, Fintype.sum_option, assemblyLinearMap,
    LinearMap.coe_mk, AddHom.coe_mk, PiLp.toLp_apply, assemble] using
    assembly_norm_sq ha (x none) (fun i => x (some i))

def assemblyIsometry {a : ι → ℝ} (ha : mass a < 1) :
    PiLp 2 (fun _ : Option ι => E) →ₗᵢ[ℝ] PiLp 2 (fun _ : Option ι => E) :=
  { assemblyLinearMap a with norm_map' := assemblyLinearMap_norm ha }

/-- The active coordinates use exactly the positive matrix square root in the manuscript. -/
lemma active_eq_sqrt_sum [DecidableEq ι] {a : ι → ℝ} (ha : mass a < 1)
    (p : E) (z : ι → E) (i : ι) :
    active a p z i = a i • p + ∑ j, (CFC.sqrt (1 - vecMulVec a a)) i j • z j := by
  rw [← complement_eq_sqrt ha]
  simp only [complement_apply, sub_smul, Finset.sum_sub_distrib]
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [active, noiseSum, smul_sub, Finset.smul_sum, smul_smul]
  have hh : (∑ j, (a i * (1 / (1 + reserve a) * a j)) • z j) =
      ∑ j, (a i * a j / (1 + reserve a)) • z j := by
    congr 1
    ext j
    congr 1
    ring
  rw [hh]
  abel

variable [FiniteDimensional ℝ E]

def assemblyEquiv {a : ι → ℝ} (ha : mass a < 1) :
    PiLp 2 (fun _ : Option ι => E) ≃ₗᵢ[ℝ] PiLp 2 (fun _ : Option ι => E) :=
  LinearIsometryEquiv.ofSurjective (assemblyIsometry ha)
    (LinearMap.injective_iff_surjective.mp (show Function.Injective
      (assemblyIsometry (E := E) ha).toLinearMap from (assemblyIsometry (E := E) ha).injective))

variable [MeasurableSpace E] [BorelSpace E]

/-- Independent standard Gaussian blocks are the standard Gaussian of their Hilbert sum. -/
lemma pi_stdGaussian_toLp :
    (Measure.pi (fun _ : ι => stdGaussian E)).map (WithLp.toLp 2) =
      stdGaussian (PiLp 2 (fun _ : ι => E)) := by
  apply Measure.ext_of_charFun
  ext t
  simp_rw [charFun_pi, charFun_stdGaussian, ← Complex.exp_sum, ← Complex.ofReal_pow,
    PiLp.norm_sq_eq_of_L2]
  simp [Finset.sum_div, neg_div]

/-- Joint standard independence holds after averaging the independent standard input and noise. -/
lemma assemble_map_pi {a : ι → ℝ} (ha : mass a < 1) :
    (Measure.pi (fun _ : Option ι => stdGaussian E)).map (assemble a) =
      Measure.pi (fun _ : Option ι => stdGaussian E) := by
  apply (MeasurableEquiv.toLp 2 (Option ι → E)).map_measurableEquiv_injective
  rw [MeasurableEquiv.coe_toLp]
  have he := stdGaussian_map (assemblyEquiv (E := E) ha)
  rw [← pi_stdGaussian_toLp (ι := Option ι)] at he
  have hm : Measurable (assemble a : (Option ι → E) → Option ι → E) := by
    have hc : Continuous (assemble a : (Option ι → E) → Option ι → E) := by
      apply continuous_pi
      intro i
      cases i <;> dsimp [assemble, active, residual, noiseSum] <;> fun_prop
    exact hc.measurable
  have ht : Measurable (WithLp.toLp 2 : (Option ι → E) → PiLp 2 (fun _ : Option ι => E)) :=
    (MeasurableEquiv.toLp 2 (Option ι → E)).measurable
  rw [Measure.map_map ht hm]
  rw [Measure.map_map (assemblyEquiv (E := E) ha).continuous.measurable ht] at he
  exact he

/-- The fresh input/noise product law. The first component here is the active noise inventory. -/
lemma assemble_map_fresh_product {a : ι → ℝ} (ha : mass a < 1) :
    ((Measure.pi (fun _ : ι => stdGaussian E)).prod (stdGaussian E)).map
      (fun zp => assemble a ((MeasurableEquiv.piOptionEquivProd
        (fun _ : Option ι => E)).symm zp)) =
      Measure.pi (fun _ : Option ι => stdGaussian E) := by
  have hm : Measurable (assemble a : (Option ι → E) → Option ι → E) := by
    apply Measurable.of_eval
    intro i
    cases i <;> dsimp [assemble, active, residual, noiseSum] <;> fun_prop
  change Measure.map ((assemble a) ∘ (MeasurableEquiv.piOptionEquivProd
    (fun _ : Option ι => E)).symm) _ = _
  rw [← Measure.map_map hm ((MeasurableEquiv.piOptionEquivProd
    (fun _ : Option ι => E)).symm.measurable),
    Measure.pi_map_piOptionEquivProd (fun _ : Option ι => stdGaussian E), assemble_map_pi ha]

omit [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma pack_input_apply (z : ι → E) (p : E) (i : Option ι) :
    (MeasurableEquiv.piOptionEquivProd (fun _ : Option ι => E)).symm (z, p) i =
      i.elim p z := by
  cases i <;> rfl

/-- Literal split law, written as independent standard input followed by fresh standard noise. -/
lemma literal_split_joint_law {a : ι → ℝ} (ha : mass a < 1) :
    ((stdGaussian E).prod (Measure.pi (fun _ : ι => stdGaussian E))).map
      (fun pz i => i.elim (residual a pz.1 pz.2) (active a pz.1 pz.2)) =
      Measure.pi (fun _ : Option ι => stdGaussian E) := by
  have h := assemble_map_fresh_product (E := E) ha
  rw [← Measure.prod_swap (μ := stdGaussian E)
    (ν := Measure.pi (fun _ : ι => stdGaussian E))] at h
  have hm : Measurable (fun zp : (ι → E) × E => assemble a
      ((MeasurableEquiv.piOptionEquivProd (fun _ : Option ι => E)).symm zp)) := by
    apply Measurable.of_eval
    intro i
    cases i <;> dsimp [assemble, active, residual, noiseSum] <;> fun_prop
  rw [Measure.map_map hm measurable_swap] at h
  convert h using 1
  congr 1
  funext pz i
  cases i <;> rfl

end Vector

section Budget
omit [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma mass_div (c : ι → ℝ) (σ : ℝ) :
    mass (fun i => c i / σ) = mass c / σ^2 := by
  simp [mass, div_pow, Finset.sum_div]

lemma budget_admissible {c : ι → ℝ} {σ β : ℝ} (hσ : 0 < σ) (hβ : 0 < β)
    (hbudget : mass c + β^2 = σ^2) : mass (fun i => c i / σ) < 1 := by
  rw [mass_div]
  apply (div_lt_iff₀ (sq_pos_of_pos hσ)).mpr
  nlinarith [sq_pos_of_pos hβ]

lemma reserve_eq_budget {c : ι → ℝ} {σ β : ℝ} (hσ : 0 < σ) (hβ : 0 < β)
    (hbudget : mass c + β^2 = σ^2) : reserve (fun i => c i / σ) = β / σ := by
  have ha := budget_admissible hσ hβ hbudget
  apply (sq_eq_sq₀ (reserve_pos ha).le (div_pos hβ hσ).le).mp
  rw [reserve_sq ha.le, mass_div, div_pow]
  field_simp
  nlinarith

/-- The same-input residual reconstructs the physical variance budget exactly. -/
lemma budget_reconstruction {c : ι → ℝ} {σ β : ℝ} (hσ : 0 < σ) (hβ : 0 < β)
    (hbudget : mass c + β^2 = σ^2) (p : E) (z : ι → E) :
    σ • p = (∑ i, c i • active (fun j => c j / σ) p z i) +
      β • residual (fun j => c j / σ) p z := by
  have h := congrArg (fun v : E => σ • v)
    (residual_reconstruction (budget_admissible hσ hβ hbudget) p z)
  rw [reserve_eq_budget hσ hβ hbudget] at h
  have hc (t : ℝ) : σ * (t / σ) = t := by field_simp
  simpa only [smul_add, Finset.smul_sum, smul_smul, hc] using h

lemma budget_residual_same_input {c : ι → ℝ} {σ β : ℝ} (hσ : 0 < σ) (hβ : 0 < β)
    (hbudget : mass c + β^2 = σ^2) (p : E) (z : ι → E) :
    residual (fun j => c j / σ) p z = β⁻¹ •
      (σ • p - ∑ i, c i • active (fun j => c j / σ) p z i) := by
  rw [budget_reconstruction hσ hβ hbudget p z, add_sub_cancel_left,
    inv_smul_smul₀ (ne_of_gt hβ)]

/-- `none` is the base Gaussian coordinate; `some i` is child `i`. -/
def inventoryCoefficients (s : ℝ) (ω childScale : ι → ℝ) : Option ι → ℝ
  | none => s
  | some i => ω i * childScale i

lemma mass_inventoryCoefficients (s : ℝ) (ω childScale : ι → ℝ) :
    mass (inventoryCoefficients s ω childScale) = s^2 + ∑ i, (ω i * childScale i)^2 := by
  simp [mass, Fintype.sum_option, inventoryCoefficients]

lemma inventory_budget_admissible {s σ β : ℝ} {ω childScale : ι → ℝ}
    (hσ : 0 < σ) (hβ : 0 < β)
    (hbudget : s^2 + (∑ i, (ω i * childScale i)^2) + β^2 = σ^2) :
    mass (fun i => inventoryCoefficients s ω childScale i / σ) < 1 := by
  apply budget_admissible hσ hβ
  rwa [mass_inventoryCoefficients]

/-- No nonempty-inventory hypothesis is used: with no active coordinates the residual is input. -/
lemma residual_empty [IsEmpty ι] (a : ι → ℝ) (p : E) (z : ι → E) :
    residual a p z = p := by
  simp [residual, noiseSum, reserve, mass]

lemma inventory_reconstruction {s σ β : ℝ} {ω childScale : ι → ℝ}
    (hσ : 0 < σ) (hβ : 0 < β)
    (hbudget : s^2 + (∑ i, (ω i * childScale i)^2) + β^2 = σ^2)
    (p : E) (z : Option ι → E) :
    let a := fun i => inventoryCoefficients s ω childScale i / σ
    σ • p = s • active a p z none +
      (∑ i, (ω i * childScale i) • active a p z (some i)) + β • residual a p z := by
  have hb : mass (inventoryCoefficients s ω childScale) + β^2 = σ^2 := by
    rwa [mass_inventoryCoefficients]
  simpa only [Fintype.sum_option, inventoryCoefficients] using
    budget_reconstruction hσ hβ hb p z

lemma inventory_mass_empty [IsEmpty ι] (s : ℝ) (ω childScale : ι → ℝ) :
    mass (inventoryCoefficients s ω childScale) = s^2 := by
  simp [mass_inventoryCoefficients]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Source specialization, including empty child inventories and zero-dimensional physical space. -/
lemma manuscript_joint_law {σ β : ℝ} {ω childScale : ι → ℝ}
    (hσ : 0 < σ) (hβ : 0 < β)
    (hbudget : (σ / 2)^2 + (∑ i, (ω i * childScale i)^2) + β^2 = σ^2) :
    let a := fun i => inventoryCoefficients (σ / 2) ω childScale i / σ
    ((stdGaussian E).prod (Measure.pi (fun _ : Option ι => stdGaussian E))).map
      (fun pz i => i.elim (residual a pz.1 pz.2) (active a pz.1 pz.2)) =
      Measure.pi (fun _ : Option (Option ι) => stdGaussian E) :=
  literal_split_joint_law (inventory_budget_admissible hσ hβ hbudget)

end Budget

end AcceleratedLogConcave.Conditional.GaussianAssembly
