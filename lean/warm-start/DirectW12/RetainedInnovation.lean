import AcceleratedLogConcave.Root.Innovation

/-!

-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace
namespace AcceleratedLogConcave.Root.RecursiveInnovation

/-- Genuine fixed-parent integrability, from the actual finite retained increment.
This is not inferred from an inequality involving Lean's total real integral. -/
theorem retained_innovation_integrable
    {ι : Type*} [fi : Fintype ι] {N : ℕ} (d : RetainedLaw.Data ι N) (v : EuclideanSpace ℝ ι) :
    Integrable (fun z => (inner ℝ v (RetainedLaw.output d z-z.1.1))^2)
      (RetainedLaw.averagedJoint d) := by
  let X : Fin N → RetainedLaw.Execution (ι := ι) (m := N) → ℝ :=
    fun i z => (-d.weight i) * inner ℝ v (RetainedLaw.childIncrement d i z)
  have hX : ∀ i, MemLp (X i) 2 (RetainedLaw.averagedJoint d) :=
    fun i => ((RetainedLaw.increment_memLp d i).const_inner (𝕜 := ℝ) v).const_mul _
  have hsum : MemLp (fun z => ∑ i, X i z) 2 (RetainedLaw.averagedJoint d) :=
    memLp_finsetSum Finset.univ (fun i _ => hX i)
  have he : (fun z => inner ℝ v (RetainedLaw.output d z-z.1.1)) =
      (fun z => ∑ i, X i z) := by
    funext z
    rw [RetainedLaw.innovation]
    simp only [inner_sum, inner_smul_right, X, RetainedLaw.childIncrement]
  have hs : Integrable (fun z => (∑ i, X i z)^2)
      (RetainedLaw.averagedJoint d) := hsum.integrable_sq
  exact hs.congr (ae_of_all _ (fun z =>
    congrArg (fun t : ℝ => t^2) (congrFun he z).symm))

end AcceleratedLogConcave.Root.RecursiveInnovation
