import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Genuine Hilbert coefficient tensors and nontrivial split norms

Every slot, including a distinguished output slot, belongs to the same finite
slot index. Coefficients carry the Hilbert–Schmidt (Euclidean) norm. A split
uses the operator norm of its actual rectangular matrix unfolding.

The finite-sum Kronecker proof is adapted from `openai/math`, revision
`1581d4cbdd69a0faf34b2089614fe2a814316a6a`,
`lean/OAI/Probability/LogConcave/JetEstimates/Bound.lean` (Apache-2.0).
-/

open Matrix WithLp
open scoped RealInnerProductSpace

namespace AcceleratedLogConcave.Tensor

/-- All slots are ordinary indices; a distinguished output slot, if present, is included. -/
abbrev Coeff (Slot : Type*) [Fintype Slot] (D : ℕ) :=
  EuclideanSpace ℝ (Slot → Fin D)

abbrev FinCoeff (n D : ℕ) := Coeff (Fin n) D

variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot] (D : ℕ)
abbrev LeftAssignment (S : Finset Slot) := S → Fin D
abbrev RightAssignment (S : Finset Slot) := {i : Slot // i ∉ S} → Fin D
abbrev LeftHilbert (S : Finset Slot) := EuclideanSpace ℝ (LeftAssignment D S)
abbrev RightHilbert (S : Finset Slot) := EuclideanSpace ℝ (RightAssignment D S)

/-- The usual admissible splits, excluding either empty group. -/
def NontrivialSplit (S : Finset Slot) : Prop := S.Nonempty ∧ Sᶜ.Nonempty

def assignmentEquiv (S : Finset Slot) :
    (Slot → Fin D) ≃ LeftAssignment D S × RightAssignment D S :=
  Equiv.piEquivPiSubtypeProd (fun i ↦ i ∈ S) (fun _ ↦ Fin D)

/-- Reindexing preserves the actual Hilbert--Schmidt coefficient norm. -/
noncomputable def splitReindex (S : Finset Slot) :
    Coeff Slot D ≃ₗᵢ[ℝ] EuclideanSpace ℝ (LeftAssignment D S × RightAssignment D S) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (assignmentEquiv D S)

/-- Actual rectangular matrix unfolding, indexed by assignments on the two slot groups. -/
noncomputable def unfoldEquiv (S : Finset Slot) :
    Coeff Slot D ≃ₗ[ℝ] Matrix (LeftAssignment D S) (RightAssignment D S) ℝ where
  toFun T r c := T ((assignmentEquiv D S).symm (r,c))
  invFun M := toLp 2 (fun a ↦ M ((assignmentEquiv D S a).1) ((assignmentEquiv D S a).2))
  left_inv T := by
    ext a
    change T ((assignmentEquiv D S).symm (assignmentEquiv D S a)) = T a
    rw [Equiv.symm_apply_apply]
  right_inv M := by
    ext r c
    change M ((assignmentEquiv D S ((assignmentEquiv D S).symm (r,c))).1)
      ((assignmentEquiv D S ((assignmentEquiv D S).symm (r,c))).2) = M r c
    rw [Equiv.apply_symm_apply]
  map_add' T U := rfl
  map_smul' r T := rfl

/-- Rectangular matrices act on Euclidean, not sup-norm, coefficient spaces. -/
noncomputable def matrixCLMEquiv {R C : Type*} [Fintype R] [Fintype C] [DecidableEq C] :
    Matrix R C ℝ ≃ₗ[ℝ] (EuclideanSpace ℝ C →L[ℝ] EuclideanSpace ℝ R) :=
  Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap

noncomputable def splitOperatorEquiv (S : Finset Slot) :
    Coeff Slot D ≃ₗ[ℝ] (RightHilbert D S →L[ℝ] LeftHilbert D S) :=
  (unfoldEquiv D S).trans matrixCLMEquiv

noncomputable def splitNorm (S : Finset Slot) (T : Coeff Slot D) : ℝ :=
  ‖splitOperatorEquiv D S T‖

lemma unfold_apply (S : Finset Slot) (T : Coeff Slot D)
    (r : LeftAssignment D S) (c : RightAssignment D S) :
    unfoldEquiv D S T r c = T (fun i ↦ if hi : i ∈ S then r ⟨i,hi⟩ else c ⟨i,hi⟩) := rfl

lemma splitOperator_apply (S : Finset Slot) (T : Coeff Slot D)
    (v : RightHilbert D S) (r : LeftAssignment D S) :
    splitOperatorEquiv D S T v r = ∑ c, unfoldEquiv D S T r c * v c := rfl

lemma split_pairing_bound (S : Finset Slot) (T : Coeff Slot D)
    (u : LeftHilbert D S) (v : RightHilbert D S) :
    |⟪u, splitOperatorEquiv D S T v⟫| ≤ splitNorm D S T * ‖u‖ * ‖v‖ := by
  calc
    _ ≤ ‖u‖ * ‖splitOperatorEquiv D S T v‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖u‖ * (‖splitOperatorEquiv D S T‖ * ‖v‖) := by
      gcongr
      exact (splitOperatorEquiv D S T).le_opNorm v
    _ = _ := by unfold splitNorm; ring

/-- Applying separate linear operators to the two coefficient groups. -/
noncomputable def separateAction (S : Finset Slot)
    (P : LeftHilbert D S →L[ℝ] LeftHilbert D S)
    (Q : RightHilbert D S →L[ℝ] RightHilbert D S) (T : Coeff Slot D) : Coeff Slot D :=
  (splitOperatorEquiv D S).symm (P ∘L (splitOperatorEquiv D S T) ∘L Q)

@[simp] lemma splitOperator_separateAction (S : Finset Slot)
    (P : LeftHilbert D S →L[ℝ] LeftHilbert D S)
    (Q : RightHilbert D S →L[ℝ] RightHilbert D S) (T : Coeff Slot D) :
    splitOperatorEquiv D S (separateAction D S P Q T) =
      P ∘L (splitOperatorEquiv D S T) ∘L Q :=
  (splitOperatorEquiv D S).apply_symm_apply _

lemma splitNorm_separateAction_le (S : Finset Slot)
    (P : LeftHilbert D S →L[ℝ] LeftHilbert D S)
    (Q : RightHilbert D S →L[ℝ] RightHilbert D S) (T : Coeff Slot D) :
    splitNorm D S (separateAction D S P Q T) ≤ ‖P‖ * splitNorm D S T * ‖Q‖ := by
  unfold splitNorm
  rw [splitOperator_separateAction]
  calc
    _ ≤ ‖P‖ * ‖splitOperatorEquiv D S T ∘L Q‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖P‖ * (‖splitOperatorEquiv D S T‖ * ‖Q‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ = _ := by ring

lemma splitNorm_separateAction_le_self (S : Finset Slot)
    (P : LeftHilbert D S →L[ℝ] LeftHilbert D S)
    (Q : RightHilbert D S →L[ℝ] RightHilbert D S)
    (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) (T : Coeff Slot D) :
    splitNorm D S (separateAction D S P Q T) ≤ splitNorm D S T := by
  calc
    _ ≤ ‖P‖ * splitNorm D S T * ‖Q‖ := splitNorm_separateAction_le D S P Q T
    _ ≤ 1 * splitNorm D S T * 1 := by gcongr <;> first | exact hP | exact hQ | simp [splitNorm]
    _ = _ := by simp

end AcceleratedLogConcave.Tensor

namespace AcceleratedLogConcave.Tensor

/-- Hilbert subspace of coefficient tensors invariant under all permutations of their slots. -/
def symmetricSubspace (Slot : Type*) [Fintype Slot] [DecidableEq Slot] (D : ℕ) : Submodule ℝ (Coeff Slot D) where
  carrier := {T | ∀ σ : Equiv.Perm Slot, ∀ a : Slot → Fin D, T (a ∘ σ) = T a}
  zero_mem' := by simp
  add_mem' := by
    intro T U hT hU σ a
    change T (a ∘ σ) + U (a ∘ σ) = T a + U a
    rw [hT σ a, hU σ a]
  smul_mem' := by
    intro c T hT σ a
    change c * T (a ∘ σ) = c * T a
    rw [hT σ a]

/-- Canonical Hilbert symmetrization: orthogonal projection onto symmetric coefficient tensors. -/
noncomputable def hilbertSymmetrizer (Slot : Type*) [Fintype Slot] [DecidableEq Slot] (D : ℕ) :
    Coeff Slot D →L[ℝ] Coeff Slot D := (symmetricSubspace Slot D).starProjection

lemma hilbertSymmetrizer_norm_le (Slot : Type*) [Fintype Slot] [DecidableEq Slot] (D : ℕ) :
    ‖hilbertSymmetrizer Slot D‖ ≤ 1 :=
  (symmetricSubspace Slot D).starProjection_norm_le

lemma hilbertSymmetrizer_symmetric (Slot : Type*) [Fintype Slot] [DecidableEq Slot] (D : ℕ)
    (T : Coeff Slot D) (σ : Equiv.Perm Slot) (a : Slot → Fin D) :
    hilbertSymmetrizer Slot D T (a ∘ σ) = hilbertSymmetrizer Slot D T a := by
  exact ((symmetricSubspace Slot D).orthogonalProjectionOnto T).property σ a

variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot] (D : ℕ)

noncomputable def separateSymmetrize (S : Finset Slot) (T : Coeff Slot D) : Coeff Slot D :=
  separateAction D S (hilbertSymmetrizer S D)
    (hilbertSymmetrizer {i : Slot // i ∉ S} D) T

lemma splitNorm_separateSymmetrize_le (S : Finset Slot) (T : Coeff Slot D) :
    splitNorm D S (separateSymmetrize D S T) ≤ splitNorm D S T :=
  splitNorm_separateAction_le_self D S _ _
    (hilbertSymmetrizer_norm_le _ _) (hilbertSymmetrizer_norm_le _ _) T

lemma hs_norm_sq (T : Coeff Slot D) : ‖T‖ ^ 2 = ∑ a : Slot → Fin D, (T a) ^ 2 :=
  EuclideanSpace.real_norm_sq_eq T

lemma split_reindex_hs_norm (S : Finset Slot) (T : Coeff Slot D) :
    ‖splitReindex D S T‖ = ‖T‖ := (splitReindex D S).norm_map T

end AcceleratedLogConcave.Tensor


namespace AcceleratedLogConcave.Tensor
section MatrixTensorProduct
variable {I J K L : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]

/-- Squared-energy formulation of an actual Euclidean matrix operator bound. -/
def EnergyBound (A : Matrix I J ℝ) (C : ℝ) : Prop :=
  ∀ v : J → ℝ, (∑ i, (∑ j, A i j * v j)^2) ≤ C * ∑ j, (v j)^2

/-- Finite-sum Kronecker argument, adapted from openai/math JetEstimates/Bound.lean,
TensorEnergy.Bound.kronecker, without importing that development. -/
lemma EnergyBound.kronecker {A : Matrix I J ℝ} {B : Matrix K L ℝ} {C D : ℝ}
    (hA : EnergyBound A C) (hB : EnergyBound B D) (hC : 0 ≤ C) :
    EnergyBound (Matrix.kronecker A B) (C * D) := by
  intro v
  change (∑ i : I × K, (∑ j : J × L, A i.1 j.1 * B i.2 j.2 * v j)^2) ≤
    (C * D) * ∑ j : J × L, (v j)^2
  simp only [Fintype.sum_prod_type]
  have he (i : I) (k : K) :
      (∑ j, ∑ l, (A i j * B k l) * v (j,l)) = ∑ j, A i j * (∑ l, B k l * v (j,l)) := by
    simp only [Finset.mul_sum, mul_assoc]
  simp_rw [he]
  rw [Finset.sum_comm]
  have hh := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset K)) ↦
    hA (fun j ↦ ∑ l, B k l * v (j,l)))
  rw [← Finset.mul_sum] at hh
  conv at hh => rhs; arg 2; rw [Finset.sum_comm]
  have hg := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset J)) ↦
      hB (fun l ↦ v (j,l)))) hC
  rw [← Finset.mul_sum] at hg
  exact hh.trans (hg.trans_eq (by ring))

variable [DecidableEq J] [DecidableEq L]

lemma matrixCLMEquiv_apply (A : Matrix I J ℝ) (v : EuclideanSpace ℝ J) (i : I) :
    matrixCLMEquiv A v i = ∑ j, A i j * v j := rfl

lemma energyBound_opNorm (A : Matrix I J ℝ) : EnergyBound A (‖matrixCLMEquiv A‖ ^ 2) := by
  intro v
  have h := (matrixCLMEquiv A).le_opNorm (toLp 2 v)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow] at h2
  simpa only [EuclideanSpace.real_norm_sq_eq, matrixCLMEquiv_apply] using h2

lemma opNorm_le_of_energyBound (A : Matrix I J ℝ) (C : ℝ) (hC : 0 ≤ C)
    (h : EnergyBound A (C ^ 2)) : ‖matrixCLMEquiv A‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  have he : ‖matrixCLMEquiv A v‖ ^ 2 ≤ C ^ 2 * ‖v‖ ^ 2 := by
    simpa only [EuclideanSpace.real_norm_sq_eq, matrixCLMEquiv_apply] using h v.ofLp
  have hp : 0 ≤ C * ‖v‖ := mul_nonneg hC (norm_nonneg _)
  nlinarith [norm_nonneg (matrixCLMEquiv A v)]

lemma matrixCLM_kronecker_norm_le (A : Matrix I J ℝ) (B : Matrix K L ℝ) :
    ‖matrixCLMEquiv (Matrix.kronecker A B)‖ ≤ ‖matrixCLMEquiv A‖ * ‖matrixCLMEquiv B‖ := by
  apply opNorm_le_of_energyBound _ _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [mul_pow]
  exact (energyBound_opNorm A).kronecker (energyBound_opNorm B) (sq_nonneg _)

end MatrixTensorProduct
end AcceleratedLogConcave.Tensor

namespace AcceleratedLogConcave.Tensor
section SlotAveraging
variable (Slot : Type*) [Fintype Slot] [DecidableEq Slot] (D : ℕ)

/-- The isometric action of a permutation of tensor slots on all coefficient assignments. -/
noncomputable def slotPermIsometry (σ : Equiv.Perm Slot) : Coeff Slot D ≃ₗᵢ[ℝ] Coeff Slot D :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.arrowCongr σ (Equiv.refl (Fin D)))

lemma slotPermIsometry_apply (σ : Equiv.Perm Slot) (T : Coeff Slot D) (a : Slot → Fin D) :
    slotPermIsometry Slot D σ T a = T (a ∘ σ) := rfl

/-- Explicit uniform average of all within-group slot permutations. -/
noncomputable def averagingSymmetrizer : Coeff Slot D →L[ℝ] Coeff Slot D :=
  (Fintype.card (Equiv.Perm Slot) : ℝ)⁻¹ •
    ∑ σ : Equiv.Perm Slot, (slotPermIsometry Slot D σ).toContinuousLinearEquiv.toContinuousLinearMap

lemma averagingSymmetrizer_norm_le : ‖averagingSymmetrizer Slot D‖ ≤ 1 := by
  have hc : 0 < (Fintype.card (Equiv.Perm Slot) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [averagingSymmetrizer, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (Fintype.card (Equiv.Perm Slot) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm Slot,
          ‖(slotPermIsometry Slot D σ).toContinuousLinearEquiv.toContinuousLinearMap‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (Fintype.card (Equiv.Perm Slot) : ℝ)⁻¹ * ∑ _ : Equiv.Perm Slot, (1 : ℝ) := by
      gcongr with σ
      exact (slotPermIsometry Slot D σ).toLinearIsometry.norm_toContinuousLinearMap_le
    _ = 1 := by simp [hc.ne']

lemma averagingSymmetrizer_apply (T : Coeff Slot D) (a : Slot → Fin D) :
    averagingSymmetrizer Slot D T a = (Fintype.card (Equiv.Perm Slot) : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm Slot, T (a ∘ σ) := by
  simp [averagingSymmetrizer, slotPermIsometry_apply]

end SlotAveraging

variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot] (D : ℕ)

noncomputable def separatelyAverage (S : Finset Slot) (T : Coeff Slot D) : Coeff Slot D :=
  separateAction D S (averagingSymmetrizer S D)
    (averagingSymmetrizer {i : Slot // i ∉ S} D) T

lemma splitNorm_separatelyAverage_le (S : Finset Slot) (T : Coeff Slot D) :
    splitNorm D S (separatelyAverage D S T) ≤ splitNorm D S T :=
  splitNorm_separateAction_le_self D S _ _
    (averagingSymmetrizer_norm_le _ _) (averagingSymmetrizer_norm_le _ _) T

section ProductBound
variable {Slot₂ : Type*} [Fintype Slot₂] [DecidableEq Slot₂]

/-- Tensor multiplication is the Kronecker product after grouping row and column assignments. -/
noncomputable def tensorProductUnfolding (S : Finset Slot) (R : Finset Slot₂)
    (T : Coeff Slot D) (U : Coeff Slot₂ D) :
    Matrix (LeftAssignment D S × LeftAssignment D R)
      (RightAssignment D S × RightAssignment D R) ℝ :=
  Matrix.kronecker (unfoldEquiv D S T) (unfoldEquiv D R U)

lemma tensorProductUnfolding_apply (S : Finset Slot) (R : Finset Slot₂)
    (T : Coeff Slot D) (U : Coeff Slot₂ D)
    (a : LeftAssignment D S × LeftAssignment D R)
    (b : RightAssignment D S × RightAssignment D R) :
    tensorProductUnfolding D S R T U a b =
      T ((assignmentEquiv D S).symm (a.1,b.1)) *
      U ((assignmentEquiv D R).symm (a.2,b.2)) := rfl

lemma tensorProductUnfolding_norm_le (S : Finset Slot) (R : Finset Slot₂)
    (T : Coeff Slot D) (U : Coeff Slot₂ D) :
    ‖matrixCLMEquiv (tensorProductUnfolding D S R T U)‖ ≤
      splitNorm D S T * splitNorm D R U :=
  matrixCLM_kronecker_norm_le (unfoldEquiv D S T) (unfoldEquiv D R U)

lemma tensorProduct_separate_contraction (S : Finset Slot) (R : Finset Slot₂)
    (T : Coeff Slot D) (U : Coeff Slot₂ D)
    (P : EuclideanSpace ℝ (LeftAssignment D S × LeftAssignment D R) →L[ℝ]
      EuclideanSpace ℝ (LeftAssignment D S × LeftAssignment D R))
    (Q : EuclideanSpace ℝ (RightAssignment D S × RightAssignment D R) →L[ℝ]
      EuclideanSpace ℝ (RightAssignment D S × RightAssignment D R))
    (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) :
    ‖P ∘L matrixCLMEquiv (tensorProductUnfolding D S R T U) ∘L Q‖ ≤
      splitNorm D S T * splitNorm D R U := by
  calc
    _ ≤ ‖P‖ * ‖matrixCLMEquiv (tensorProductUnfolding D S R T U) ∘L Q‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (‖matrixCLMEquiv (tensorProductUnfolding D S R T U)‖ * 1) := by
      gcongr
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left hQ (norm_nonneg _))
    _ = ‖matrixCLMEquiv (tensorProductUnfolding D S R T U)‖ := by ring
    _ ≤ _ := tensorProductUnfolding_norm_le D S R T U

end ProductBound
end AcceleratedLogConcave.Tensor


namespace AcceleratedLogConcave.Tensor
section BilinearEquivalence
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]

omit [DecidableEq J] in
lemma energyBound_of_bilinear {A : Matrix I J ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ (u : I → ℝ) (v : J → ℝ),
      (∑ i, ∑ j, u i * A i j * v j)^2 ≤ C * (∑ i, (u i)^2) * ∑ j, (v j)^2) :
    EnergyBound A C := by
  intro v
  let w : I → ℝ := fun i ↦ ∑ j, A i j * v j
  have he : (∑ i, ∑ j, w i * A i j * v j) = ∑ i, (w i)^2 := by
    simp only [mul_assoc, ← Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ ↦ by dsimp [w]; ring)
  have hh := h w v
  rw [he] at hh
  have hw : 0 ≤ ∑ i, (w i)^2 := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  by_cases hz : (∑ i, (w i)^2) = 0
  · change (∑ i, (w i)^2) ≤ _
    rw [hz]
    exact mul_nonneg hC (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))
  · have hp : 0 < ∑ i, (w i)^2 := lt_of_le_of_ne hw (Ne.symm hz)
    have hh' : (∑ i, (w i)^2) * (∑ i, (w i)^2) ≤
        (C * ∑ j, (v j)^2) * (∑ i, (w i)^2) := by nlinarith [hh]
    exact (mul_le_mul_iff_left₀ hp).mp (by simpa only [mul_comm] using hh')

omit [DecidableEq J] in
lemma EnergyBound.bilinear {A : Matrix I J ℝ} {C : ℝ} (h : EnergyBound A C)
    (u : I → ℝ) (v : J → ℝ) :
    (∑ i, ∑ j, u i * A i j * v j)^2 ≤ C * (∑ i, (u i)^2) * ∑ j, (v j)^2 := by
  simp only [mul_assoc, ← Finset.mul_sum]
  exact (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans
    ((mul_le_mul_of_nonneg_left (h v)
      (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))).trans_eq (by ring))

lemma matrixCLM_norm_le_of_bilinear_sq (A : Matrix I J ℝ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ (u : I → ℝ) (v : J → ℝ),
      (∑ i, ∑ j, u i * A i j * v j)^2 ≤ C^2 * (∑ i, (u i)^2) * ∑ j, (v j)^2) :
    ‖matrixCLMEquiv A‖ ≤ C :=
  opNorm_le_of_energyBound A C hC (energyBound_of_bilinear (sq_nonneg _) h)

lemma bilinear_sq_le_of_matrixCLM_norm_le (A : Matrix I J ℝ) (C : ℝ) (_hC : 0 ≤ C)
    (h : ‖matrixCLMEquiv A‖ ≤ C) (u : I → ℝ) (v : J → ℝ) :
    (∑ i, ∑ j, u i * A i j * v j)^2 ≤ C^2 * (∑ i, (u i)^2) * ∑ j, (v j)^2 := by
  have hsq : ‖matrixCLMEquiv A‖ ^ 2 ≤ C^2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  exact ((energyBound_opNorm A).bilinear u v).trans (by
    gcongr <;> exact Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))

lemma matrixCLM_norm_le_iff_bilinear_sq (A : Matrix I J ℝ) (C : ℝ) (hC : 0 ≤ C) :
    ‖matrixCLMEquiv A‖ ≤ C ↔ ∀ (u : I → ℝ) (v : J → ℝ),
      (∑ i, ∑ j, u i * A i j * v j)^2 ≤ C^2 * (∑ i, (u i)^2) * ∑ j, (v j)^2 :=
  ⟨fun h ↦ bilinear_sq_le_of_matrixCLM_norm_le A C hC h,
    matrixCLM_norm_le_of_bilinear_sq A C hC⟩

end BilinearEquivalence
end AcceleratedLogConcave.Tensor

namespace AcceleratedLogConcave.Tensor
section RegroupedSymmetrizers
variable (A B : Type*) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (D : ℕ)

/-- Concatenating two slot groups is an isometry on their Hilbert coefficient arrays. -/
noncomputable def regroupIsometry :
    Coeff (A ⊕ B) D ≃ₗᵢ[ℝ] EuclideanSpace ℝ ((A → Fin D) × (B → Fin D)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.sumArrowEquivProdArrow A B (Fin D))

/-- Average all permutations of the combined group, expressed in product-assignment coordinates. -/
noncomputable def regroupedSymmetrizer :
    EuclideanSpace ℝ ((A → Fin D) × (B → Fin D)) →L[ℝ]
      EuclideanSpace ℝ ((A → Fin D) × (B → Fin D)) :=
  (regroupIsometry A B D).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    averagingSymmetrizer (A ⊕ B) D ∘L
    (regroupIsometry A B D).symm.toContinuousLinearEquiv.toContinuousLinearMap

lemma regroupedSymmetrizer_norm_le : ‖regroupedSymmetrizer A B D‖ ≤ 1 := by
  let e := (regroupIsometry A B D).toContinuousLinearEquiv.toContinuousLinearMap
  let f := (regroupIsometry A B D).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have he : ‖e‖ ≤ 1 := (regroupIsometry A B D).toLinearIsometry.norm_toContinuousLinearMap_le
  have hf : ‖f‖ ≤ 1 := (regroupIsometry A B D).symm.toLinearIsometry.norm_toContinuousLinearMap_le
  change ‖e ∘L averagingSymmetrizer (A ⊕ B) D ∘L f‖ ≤ 1
  calc
    _ ≤ ‖e‖ * ‖averagingSymmetrizer (A ⊕ B) D ∘L f‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (1 * 1) := by
      gcongr
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul (averagingSymmetrizer_norm_le _ _) hf (norm_nonneg _) zero_le_one)
    _ = 1 := by norm_num

end RegroupedSymmetrizers

section TensorSymmetrization
variable {Slot Slot₂ : Type*} [Fintype Slot] [Fintype Slot₂]
  [DecidableEq Slot] [DecidableEq Slot₂] (D : ℕ)

/-- Tensor product followed by full, separate symmetrization of the combined left/right groups. -/
noncomputable def symmetrizedTensorProductOperator (S : Finset Slot) (R : Finset Slot₂)
    (T : Coeff Slot D) (U : Coeff Slot₂ D) :
    EuclideanSpace ℝ (RightAssignment D S × RightAssignment D R) →L[ℝ]
      EuclideanSpace ℝ (LeftAssignment D S × LeftAssignment D R) :=
  regroupedSymmetrizer S R D ∘L
    matrixCLMEquiv (tensorProductUnfolding D S R T U) ∘L
    regroupedSymmetrizer {i : Slot // i ∉ S} {i : Slot₂ // i ∉ R} D

lemma symmetrizedTensorProductOperator_norm_le (S : Finset Slot) (R : Finset Slot₂)
    (T : Coeff Slot D) (U : Coeff Slot₂ D) :
    ‖symmetrizedTensorProductOperator D S R T U‖ ≤ splitNorm D S T * splitNorm D R U :=
  tensorProduct_separate_contraction D S R T U _ _
    (regroupedSymmetrizer_norm_le _ _ _) (regroupedSymmetrizer_norm_le _ _ _)

end TensorSymmetrization

section SplitBasic
variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot] (D : ℕ)

@[simp] lemma splitNorm_zero (S : Finset Slot) : splitNorm D S 0 = 0 := by
  simp [splitNorm]

lemma splitNorm_nonneg (S : Finset Slot) (T : Coeff Slot D) : 0 ≤ splitNorm D S T :=
  norm_nonneg _

lemma splitNorm_add_le (S : Finset Slot) (T U : Coeff Slot D) :
    splitNorm D S (T + U) ≤ splitNorm D S T + splitNorm D S U := by
  simpa only [splitNorm, map_add] using norm_add_le (splitOperatorEquiv D S T) (splitOperatorEquiv D S U)

lemma splitNorm_smul (S : Finset Slot) (c : ℝ) (T : Coeff Slot D) :
    splitNorm D S (c • T) = |c| * splitNorm D S T := by
  simp [splitNorm, norm_smul, Real.norm_eq_abs]

lemma splitNorm_eq_zero_iff (S : Finset Slot) (T : Coeff Slot D) :
    splitNorm D S T = 0 ↔ T = 0 := by
  simp [splitNorm]

lemma splitNorm_le_iff_bilinear_sq (S : Finset Slot) (T : Coeff Slot D)
    (C : ℝ) (hC : 0 ≤ C) :
    splitNorm D S T ≤ C ↔ ∀ (u : LeftAssignment D S → ℝ) (v : RightAssignment D S → ℝ),
      (∑ r, ∑ c, u r * unfoldEquiv D S T r c * v c)^2 ≤
        C^2 * (∑ r, (u r)^2) * ∑ c, (v c)^2 :=
  matrixCLM_norm_le_iff_bilinear_sq (unfoldEquiv D S T) C hC

end SplitBasic
end AcceleratedLogConcave.Tensor


namespace AcceleratedLogConcave.Tensor
variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot] (D : ℕ)

lemma splitReindex_apply (S : Finset Slot) (T : Coeff Slot D)
    (r : LeftAssignment D S) (c : RightAssignment D S) :
    splitReindex D S T (r,c) = unfoldEquiv D S T r c := rfl

lemma unfold_hs_norm_sq (S : Finset Slot) (T : Coeff Slot D) :
    (∑ r, ∑ c, (unfoldEquiv D S T r c)^2) = ‖T‖^2 := by
  rw [← split_reindex_hs_norm D S T, EuclideanSpace.real_norm_sq_eq,
    Fintype.sum_prod_type]
  rfl

end AcceleratedLogConcave.Tensor
