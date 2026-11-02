import AcceleratedLogConcave.Tensor.ActualCoefficientBridge
import AcceleratedLogConcave.Tensor.OrderedContraction
import AcceleratedLogConcave.Tensor.FixedCutComparison

/-!

-/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
namespace AcceleratedLogConcave.Tensor.OutputLift
open ActualCoefficient
variable {D : ℕ}
variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Extract exactly one distinguished coordinate; all other slots remain free. -/
def portChart (p : A) : (A → Fin D) ≃ Fin D × ({i : A // i ≠ p} → Fin D) where
  toFun a := (a p, fun i => a i)
  invFun q i := if h : i = p then q.1 else q.2 ⟨i,h⟩
  left_inv a := by funext i; by_cases h : i = p <;> simp [h]
  right_inv q := by
    rcases q with ⟨w,a⟩
    apply Prod.ext
    · simp
    · funext i; simp [i.property]

omit [Fintype A] in
@[simp] theorem portChart_update (p : A) (a : A → Fin D) (w : Fin D) :
    portChart p (Function.update a p w) = (w,fun i : {i : A // i ≠ p} => a i) := by
  apply Prod.ext
  · simp [portChart]
  · funext i; simp [portChart,i.property]

omit [Fintype A] in
@[simp] theorem portChart_symm_pair (p : A) (a : A → Fin D) (w : Fin D) :
    (portChart p).symm (w,fun i : {i : A // i ≠ p} => a i) = Function.update a p w := by
  apply (portChart p).injective
  simp

/-- Literal identity tensor factorization, after the explicit port chart. -/
def liftMatrix (p : A) (M : Matrix (Fin D) (Fin D) ℝ) :
    Matrix (A → Fin D) (A → Fin D) ℝ := wireStep M (portChart p) (portChart p)

def lift (p : A) (M : Matrix (Fin D) (Fin D) ℝ) :
    Coeff A D →L[ℝ] Coeff A D := matrixCLMEquiv (liftMatrix p M)

theorem lift_norm_le (p : A) (M : Matrix (Fin D) (Fin D) ℝ) :
    ‖lift p M‖ ≤ ‖matrixCLMEquiv M‖ := by
  exact opNorm_le_of_energyBound _ _ (norm_nonneg _)
    ((energyBound_opNorm M).wireStep (sq_nonneg _) (portChart p) (portChart p))

/-- Basis-coordinate equality of the lifted map, valid for empty bypass groups
and for D=0. No coordinate is selected from an empty type. -/
theorem lift_apply (p : A) (M : Matrix (Fin D) (Fin D) ℝ)
    (v : Coeff A D) (a : A → Fin D) :
    lift p M v a = ∑ w : Fin D, M (a p) w * v (Function.update a p w) := by
  change (∑ q : A → Fin D, liftMatrix p M a q * v q) = _
  rw [← (portChart p).symm.sum_comp]
  simp only [Fintype.sum_prod_type, liftMatrix, wireStep,
    Equiv.apply_symm_apply]
  change (∑ w : Fin D, ∑ q : {i : A // i ≠ p} → Fin D,
    M (a p) w * (if (fun i : {i : A // i ≠ p} => a i) = q then 1 else 0) *
      v ((portChart p).symm (w,q))) = _
  simp [mul_ite, ite_mul]

/-- Transpose bound proved from the exact rectangular bilinear energy test. -/
theorem transpose_norm_le (M : Matrix (Fin D) (Fin D) ℝ) :
    ‖matrixCLMEquiv M.transpose‖ ≤ ‖matrixCLMEquiv M‖ := by
  apply matrixCLM_norm_le_of_bilinear_sq _ _ (norm_nonneg _)
  intro u v
  have h := (energyBound_opNorm M).bilinear v u
  have he : (∑ i, ∑ j, u i * M.transpose i j * v j) =
      ∑ j, ∑ i, v j * M j i * u i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    change u i * M j i * v j = _
    ring
  rw [he]
  convert h using 1; ring

/-- The matrix of the actual derivative, not an arbitrary coefficient proxy. -/
def derivativeMatrix (L : Space D →L[ℝ] Space D) : Matrix (Fin D) (Fin D) ℝ :=
  fun o i => inner ℝ (basis D o) (L (basis D i))

theorem derivativeMatrix_operator (L : Space D →L[ℝ] Space D) :
    matrixCLMEquiv (derivativeMatrix L) = L := by
  ext v o
  have h := congrArg (fun z => inner ℝ (basis D o) z) (linear_basis_expansion L v)
  simpa only [matrixCLMEquiv_apply, derivativeMatrix, inner_sum, inner_smul_right,
    EuclideanSpace.basisFun_inner, mul_comm] using h.symm

/-- Action on the distinguished output, leaving every other assignment intact. -/
def outputAction (p : A) (M : Matrix (Fin D) (Fin D) ℝ) (T : Coeff A D) : Coeff A D :=
  WithLp.toLp 2 (fun a => ∑ w, M (a p) w * T (Function.update a p w))

/-- Exact coefficient identity for composition on the vector-valued output. -/
theorem outputAction_vectorCoeff {I : Type*} [Fintype I] [DecidableEq I]
    (L : Space D →L[ℝ] Space D)
    (T : ContinuousMultilinearMap ℝ (fun _ : I => Space D) (Space D)) :
    outputAction (.inr () : I ⊕ Unit) (derivativeMatrix L) (vectorCoeff T) =
      vectorCoeff (L.compContinuousMultilinearMap T) := by
  ext a
  have h := congrArg (fun z => inner ℝ (basis D (a (.inr ()))) z)
    (linear_basis_expansion L (T (fun i => basis D (a (.inl i)))))
  simpa [outputAction, derivativeMatrix, vectorCoeff, mapCoeff,
    inner_sum, inner_smul_right, mul_comm] using h.symm

section Split
variable (S : Finset A) (p : A)

def rowLift (hp : p ∈ S) (M : Matrix (Fin D) (Fin D) ℝ) :
    LeftHilbert D S →L[ℝ] LeftHilbert D S := lift (⟨p,hp⟩ : S) M

/-- The column lift is the TRANSPOSE of the output derivative. -/
def columnLift (hp : p ∉ S) (M : Matrix (Fin D) (Fin D) ℝ) :
    RightHilbert D S →L[ℝ] RightHilbert D S :=
  lift (⟨p,hp⟩ : {i : A // i ∉ S}) M.transpose

omit [Fintype A] in
theorem rowLift_norm_le (hp : p ∈ S) (L : Space D →L[ℝ] Space D) :
    ‖rowLift S p hp (derivativeMatrix L)‖ ≤ ‖L‖ := by
  simpa only [rowLift, derivativeMatrix_operator] using lift_norm_le (⟨p,hp⟩ : S) (derivativeMatrix L)

theorem columnLift_norm_le (hp : p ∉ S) (L : Space D →L[ℝ] Space D) :
    ‖columnLift S p hp (derivativeMatrix L)‖ ≤ ‖L‖ := by
  exact (lift_norm_le (⟨p,hp⟩ : {i : A // i ∉ S}) _).trans
    ((transpose_norm_le _).trans_eq (congrArg norm (derivativeMatrix_operator L)))

omit [Fintype A] in
/-- The coefficient chart equality for a row output is pointwise, not merely a
cardinality or permutation-count statement. -/
theorem assemble_update_row (hp : p ∈ S) (r : LeftAssignment D S)
    (c : RightAssignment D S) (w : Fin D) :
    (assignmentEquiv D S).symm (Function.update r ⟨p,hp⟩ w,c) =
      Function.update ((assignmentEquiv D S).symm (r,c)) p w := by
  funext i
  by_cases hi : i = p
  · subst i; simp [assignmentEquiv, hp]
  · by_cases hS : i ∈ S
    · have hsub : (⟨i,hS⟩ : S) ≠ ⟨p,hp⟩ := by intro h; exact hi (congrArg Subtype.val h)
      simp [assignmentEquiv,hi,hS,hsub]
    · simp [assignmentEquiv,hi,hS]

omit [Fintype A] in
theorem assemble_update_column (hp : p ∉ S) (r : LeftAssignment D S)
    (c : RightAssignment D S) (w : Fin D) :
    (assignmentEquiv D S).symm (r,Function.update c ⟨p,hp⟩ w) =
      Function.update ((assignmentEquiv D S).symm (r,c)) p w := by
  funext i
  by_cases hi : i = p
  · subst i; simp [assignmentEquiv,hp]
  · by_cases hS : i ∈ S
    · simp [assignmentEquiv,hi,hS]
    · have hsub : (⟨i,hS⟩ : {i : A // i ∉ S}) ≠ ⟨p,hp⟩ := by
        intro h; exact hi (congrArg Subtype.val h)
      simp [assignmentEquiv,hi,hS,hsub]

theorem outputAction_row_operator (hp : p ∈ S)
    (M : Matrix (Fin D) (Fin D) ℝ) (T : Coeff A D) :
    splitOperatorEquiv D S (outputAction p M T) =
      (rowLift S p hp M).comp (splitOperatorEquiv D S T) := by
  ext v r
  rw [ContinuousLinearMap.comp_apply]
  change (∑ c, outputAction p M T ((assignmentEquiv D S).symm (r,c)) * v c) =
    lift (⟨p,hp⟩ : S) M (splitOperatorEquiv D S T v) r
  rw [lift_apply]
  simp only [outputAction, Finset.sum_mul, splitOperator_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro c _
  change M (((assignmentEquiv D S).symm (r,c)) p) w *
    T (Function.update ((assignmentEquiv D S).symm (r,c)) p w) * v c =
    M (r ⟨p,hp⟩) w * (T ((assignmentEquiv D S).symm
      (Function.update r ⟨p,hp⟩ w,c)) * v c)
  rw [assemble_update_row S p hp]
  simp [assignmentEquiv,hp,mul_assoc]

/-- Matrix entries of the transpose column lift. This is what forces the
right-hand action, without a symmetry assumption on Dv. -/
theorem columnLift_entry (hp : p ∉ S) (M : Matrix (Fin D) (Fin D) ℝ)
    (c q : RightAssignment D S) :
    liftMatrix (⟨p,hp⟩ : {i : A // i ∉ S}) M.transpose c q =
      liftMatrix (⟨p,hp⟩ : {i : A // i ∉ S}) M q c := by
  simp only [liftMatrix,wireStep,portChart,Matrix.transpose_apply]
  congr 1
  simp only [eq_comm]
  rfl

/-- Literal right composition, with the output coordinate on the columns. -/
theorem outputAction_column_operator (hp : p ∉ S)
    (M : Matrix (Fin D) (Fin D) ℝ) (T : Coeff A D) :
    splitOperatorEquiv D S (outputAction p M T) =
      (splitOperatorEquiv D S T).comp (columnLift S p hp M) := by
  ext v r
  change (∑ q, outputAction p M T ((assignmentEquiv D S).symm (r,q)) * v q) =
    ∑ c, T ((assignmentEquiv D S).symm (r,c)) *
      (∑ q, liftMatrix (⟨p,hp⟩ : {i : A // i ∉ S}) M.transpose c q * v q)
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  simp_rw [columnLift_entry S p hp]
  have he := lift_apply (⟨p,hp⟩ : {i : A // i ∉ S}) M
    (WithLp.toLp 2 (fun c => T ((assignmentEquiv D S).symm (r,c)))) q
  change (∑ c, liftMatrix _ M q c * T ((assignmentEquiv D S).symm (r,c))) = _ at he
  have hsum : (∑ c, T ((assignmentEquiv D S).symm (r,c)) *
      (liftMatrix (⟨p,hp⟩ : {i : A // i ∉ S}) M q c * v q)) =
      (∑ c, liftMatrix (⟨p,hp⟩ : {i : A // i ∉ S}) M q c *
        T ((assignmentEquiv D S).symm (r,c))) * v q := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [hsum,he]
  congr 1
  dsimp only [outputAction]
  apply Finset.sum_congr rfl
  intro w _
  rw [assemble_update_column S p hp]
  simp [assignmentEquiv,hp]

/-- Supplier 2, fixed-cut estimate: works for every split, hence in particular
all proper rectangular splits. No bound on another cut of T is used. -/
theorem outputAction_splitNorm_le (L : Space D →L[ℝ] Space D) (T : Coeff A D) :
    splitNorm D S (outputAction p (derivativeMatrix L) T) ≤ ‖L‖ * splitNorm D S T := by
  by_cases hp : p ∈ S
  · unfold splitNorm
    rw [outputAction_row_operator S p hp]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (rowLift_norm_le S p hp L) (norm_nonneg _))
  · unfold splitNorm
    rw [outputAction_column_operator S p hp]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_left (columnLift_norm_le S p hp L) (norm_nonneg _)).trans_eq
        (mul_comm _ _))
end Split
end AcceleratedLogConcave.Tensor.OutputLift
