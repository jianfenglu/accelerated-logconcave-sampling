import AcceleratedLogConcave.Analysis.Poisson.ReferenceTransport
import Mathlib.LinearAlgebra.Trace

/-! Basis-independent divergence and the classical product rule used for the
actual phase-density continuity equation. -/
noncomputable section
open InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic
open Analysis.Poisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem fluxDivergence_eq_trace {v : E → E} {x : E} (hv : DifferentiableAt ℝ v x) :
    fluxDivergence v x = LinearMap.trace ℝ E (fderiv ℝ v x).toLinearMap := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (stdOrthonormalBasis ℝ E).toBasis]
  unfold fluxDivergence Matrix.trace
  apply Finset.sum_congr rfl
  intro i _
  change fderiv ℝ ((innerSL ℝ ((stdOrthonormalBasis ℝ E) i)) ∘ v) x
    ((stdOrthonormalBasis ℝ E) i) = _
  rw [((innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).hasFDerivAt.comp x hv.hasFDerivAt).fderiv]
  simp [LinearMap.toMatrix_apply, OrthonormalBasis.repr_apply_apply]

theorem fluxDivergence_eq_sum_basis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ E) {v : E → E} {x : E} (hv : DifferentiableAt ℝ v x) :
    fluxDivergence v x = ∑ i, inner ℝ (b i) (fderiv ℝ v x (b i)) := by
  rw [fluxDivergence_eq_trace hv, LinearMap.trace_eq_matrix_trace ℝ b.toBasis]
  simp [Matrix.trace, LinearMap.toMatrix_apply, OrthonormalBasis.repr_apply_apply]

/-- Product rule for the actual Euclidean flux divergence. -/
theorem fluxDivergence_smul {r : E → ℝ} {v : E → E} {x : E}
    (hr : DifferentiableAt ℝ r x) (hv : DifferentiableAt ℝ v x) :
    fluxDivergence (fun y => r y • v y) x =
      fderiv ℝ r x (v x) + r x * fluxDivergence v x := by
  let b := stdOrthonormalBasis ℝ E
  change fluxDivergence (r • v) x = _
  rw [fluxDivergence_eq_sum_basis b (hr.smul hv), fluxDivergence_eq_sum_basis b hv,
    (hr.hasFDerivAt.smul hv.hasFDerivAt).fderiv]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, inner_add_right, inner_smul_right]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, add_comm]
  congr 1
  have h := congrArg (fderiv ℝ r x) (b.sum_repr' (v x))
  simpa only [map_sum, map_smul, smul_eq_mul, mul_comm] using h

end AcceleratedLogConcave.Kinetic
