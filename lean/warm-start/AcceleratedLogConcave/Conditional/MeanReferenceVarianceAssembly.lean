import AcceleratedLogConcave.Conditional.MeanReferenceCenterCross
import AcceleratedLogConcave.Conditional.MeanReferenceChildCross

noncomputable section
open MeasureTheory ProbabilityTheory AcceleratedLogConcave
open Numerics Numerics.MeanFlowLp Conditional Conditional.MeanReferenceLayer
open scoped RealInnerProductSpace
set_option autoImplicit false
namespace AcceleratedLogConcave.Conditional.MeanReferenceVariance

lemma integral_sq_sum_orthogonal {A J : Type*} [MeasurableSpace A] [Fintype J]
    (μ : Measure A) (X : J → A → ℝ) (hX : ∀ i, MemLp (X i) 2 μ)
    (horth : ∀ i j, i ≠ j → (∫ a, X i a * X j a ∂μ) = 0) :
    (∫ a, (∑ i, X i a)^2 ∂μ) = ∑ i, ∫ a, (X i a)^2 ∂μ := by
  classical
  simp_rw [pow_two, Finset.sum_mul_sum]
  have hi (i : J) : Integrable (fun a => ∑ j, X i a * X j a) μ :=
    integrable_finsetSum Finset.univ (fun j _ => (hX i).integrable_mul (hX j))
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  have hij (j : J) : Integrable (fun a => X i a * X j a) μ := (hX i).integrable_mul (hX j)
  rw [integral_finsetSum Finset.univ (fun j _ => hij j)]
  exact Finset.sum_eq_single i (fun j _ hji => horth i j hji.symm) (by simp)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

def weightedIncrement (d : Data ι m) (c : Children d) (v : E)
    (i : Option (Fin m)) (z : Execution ι m) : ℝ :=
  i.elim ((d.sigma/2) * ⟪v, centerIncrement d c z⟫)
    (fun j => (GaussLegendre.weight m j*c.scale j) * ⟪v, childIncrement d c j z⟫)

lemma weightedIncrement_memLp (d : Data ι m) (c : Children d) (v : E)
    (i : Option (Fin m)) : MemLp (weightedIncrement d c v i) 2 (averagedJoint d c) := by
  cases i with
  | none => exact ((momentTarget d c).1.const_inner v).const_mul _
  | some i => exact (((momentTarget d c).2 i).const_inner v).const_mul _

lemma weightedIncrement_sum (d : Data ι m) (c : Children d) (v : E) (z : Execution ι m) :
    (∑ i, weightedIncrement d c v i z) =
      ⟪v, d.sigma • (recombine d c z.1 z.2-z.1.1)⟫ := by
  rw [displacement_target d c]
  simp [Fintype.sum_option, weightedIncrement, inner_add_right, inner_smul_right,
    inner_sum, centerIncrement, childIncrement]

/-- Both cross-moment families follow from the constructed retained law. -/
theorem orthogonalityTarget (d : Data ι m) (c : Children d) : OrthogonalityTarget d c :=
  ⟨child_child_cross d c, center_child_cross d c⟩

lemma assembly_of_orthogonality (d : Data ι m) (c : Children d)
    (ho : OrthogonalityTarget d c) : AssemblyTarget d c := by
  intro v
  have hw : ∀ i j, i ≠ j →
      (∫ z, weightedIncrement d c v i z * weightedIncrement d c v j z ∂averagedJoint d c) = 0 := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j =>
        simp only [weightedIncrement, Option.elim_none, Option.elim_some]
        simp_rw [mul_mul_mul_comm]
        rw [integral_const_mul, ho.2 v j, mul_zero]
    | some i =>
      cases j with
      | none =>
        simp only [weightedIncrement, Option.elim_none, Option.elim_some]
        simp_rw [mul_mul_mul_comm]
        rw [integral_const_mul]
        have hc := ho.2 v i
        rw [show (∫ z, ⟪v, childIncrement d c i z⟫ * ⟪v, centerIncrement d c z⟫ ∂averagedJoint d c) = 0
          from (by simpa only [mul_comm] using hc), mul_zero]
      | some j =>
        simp only [weightedIncrement, Option.elim_some]
        simp_rw [mul_mul_mul_comm]
        rw [integral_const_mul, ho.1 v i j (fun he => hij (congrArg some he)), mul_zero]
  have he := integral_sq_sum_orthogonal (averagedJoint d c) (weightedIncrement d c v)
    (weightedIncrement_memLp d c v) hw
  simp_rw [weightedIncrement_sum] at he
  rw [he, Fintype.sum_option]
  simp only [weightedIncrement, Option.elim_none, Option.elim_some, mul_pow]
  simp_rw [integral_const_mul]

/-- Exact directional second-moment decomposition; no recursive variance estimate is assumed. -/
theorem assemblyTarget (d : Data ι m) (c : Children d) : AssemblyTarget d c :=
  assembly_of_orthogonality d c (orthogonalityTarget d c)

end AcceleratedLogConcave.Conditional.MeanReferenceVariance
