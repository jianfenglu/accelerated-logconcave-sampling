import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Determinant

/-! Determinant evolution for the variational equation, without invertibility
hypotheses or division by the determinant. -/
noncomputable section
open scoped BigOperators
namespace AcceleratedLogConcave.Conditional.Centering
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def determinantMultilinear : ContinuousMultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ :=
  { Matrix.detRowAlternating.toMultilinearMap with
    cont := continuous_id.matrix_det }

/-- Jacobi's formula specialized to the left variational equation. -/
theorem hasDerivAt_det_of_left_matrix_ode {J : ℝ → Matrix ι ι ℝ}
    {A : Matrix ι ι ℝ} {t : ℝ} (hJ : HasDerivAt J (A * J t) t) :
    HasDerivAt (fun s => (J s).det) (A.trace * (J t).det) t := by
  have h := (determinantMultilinear.hasFDerivAt (J t)).comp_hasDerivAt t hJ
  convert h using 1
  · rfl
  · erw [ContinuousMultilinearMap.linearDeriv_apply]
    have hrow (i : ι) : (A * J t) i = ∑ k, (A i k) • J t k := by
      ext j
      simp [Matrix.mul_apply, Finset.sum_apply]
    have hterm (i : ι) : determinantMultilinear
        (Function.update (J t) i ((A * J t) i)) = A i i * (J t).det := by
      change (Matrix.updateRow (J t) i ((A * J t) i)).det = _
      rw [hrow, Matrix.det_updateRow_sum]
      rfl
    simp_rw [hterm]
    simp [Matrix.trace, Finset.sum_mul]

section Operator
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private def matrixCoordinates (b : Module.Basis ι ℝ E) :
    (E →L[ℝ] E) →L[ℝ] (ι → ι → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => LinearMap.toMatrix b b A.toLinearMap
      map_add' := by intros; simp; rfl
      map_smul' := by intros; simp; rfl }

/-- Basis-free determinant evolution for a continuous-linear variational curve. -/
theorem hasDerivAt_det_of_left_ode {J : ℝ → E →L[ℝ] E}
    {A : E →L[ℝ] E} {t : ℝ} (hJ : HasDerivAt J (A.comp (J t)) t) :
    HasDerivAt (fun s => (J s).det)
      (LinearMap.trace ℝ E A.toLinearMap * (J t).det) t := by
  classical
  let b := Module.finBasis ℝ E
  let C : (E →L[ℝ] E) →L[ℝ] (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) := matrixCoordinates b
  have hC : HasFDerivAt C C (J t) := C.hasFDerivAt
  have h := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (l := C) (f := J) t hC hJ
  have hm : HasDerivAt (fun s => LinearMap.toMatrix b b (J s).toLinearMap)
      (LinearMap.toMatrix b b A.toLinearMap * LinearMap.toMatrix b b (J t).toLinearMap) t := by
    change HasDerivAt (fun s => LinearMap.toMatrix b b (J s).toLinearMap)
      (LinearMap.toMatrix b b (A.comp (J t)).toLinearMap) t at h
    change HasDerivAt _ (LinearMap.toMatrix b b (A.toLinearMap.comp (J t).toLinearMap)) t at h
    erw [LinearMap.toMatrix_comp b b b] at h
    exact h
  have hd := hasDerivAt_det_of_left_matrix_ode hm
  simpa only [LinearMap.det_toMatrix, ← LinearMap.trace_eq_matrix_trace ℝ b] using hd
end Operator
end AcceleratedLogConcave.Conditional.Centering
