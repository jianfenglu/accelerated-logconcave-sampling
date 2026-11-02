import AcceleratedLogConcave.Conditional.MeanReferenceVarianceAssembly
import AcceleratedLogConcave.Conditional.RecursiveReferenceFamily

/-! Exact old/new child-moment transfer on the retained parent execution.
The original child input is retained through the split, rather than discarded
by an output-marginal identity. Integrability follows from the constructed laws. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Conditional.MeanReferenceVariance
open Numerics Numerics.MeanFlowLp MeanReferenceLayer
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

 theorem child_second_moment_transfer (d : Data ι m) (c : Children d) (v : E)
    (i : Fin m) :
    (∫ z, ⟪v, childIncrement d c i z⟫ ^ 2 ∂averagedJoint d c) =
      ∫ b, ∫ p, ∫ p', ⟪v, p' - p⟫ ^ 2 ∂c.kernel i (stateCenter d i b,p)
        ∂stdGaussian E ∂MeanReferenceLayer.baseLaw d := by
  let : IsMarkovKernel (c.kernel i) := c.markov i
  let nu := (MeanReferenceLayer.baseLaw d).prod
    (Measure.pi (fun _ : Fin m => stdGaussian E))
  let f : SplitState ι m × (Fin m → E) → ℝ := fun z => ⟪v,z.2 i-z.1.2 i⟫ ^ 2
  have hf : StronglyMeasurable f := by dsimp [f]; fun_prop
  have hp := splitExecution_preserving d c
  have hint : Integrable f (nu ⊗ₘ stateChildren d c) := by
    apply (hp.integrable_comp hf.aestronglyMeasurable).mp
    have hi := ((momentTarget d c).2 i).const_inner (𝕜 := ℝ) v
    have hmul := hi.integrable_mul hi
    change Integrable (fun z => ⟪v, childIncrement d c i z⟫ * ⟪v, childIncrement d c i z⟫) _ at hmul
    simpa only [f, Function.comp_def, splitState, childIncrement, pow_two] using hmul
  have hinter : Integrable (fun z : SplitState ι m =>
      ∫ q, f (z,q) ∂stateChildren d c z) nu := by
    have hh := hint.integral_compProd
    simpa only [Kernel.const_apply,Kernel.prodMkLeft_apply] using hh
  change (∫ z, f (splitState d c z.1,z.2) ∂averagedJoint d c) = _
  rw [← integral_map_of_stronglyMeasurable hp.measurable hf,hp.map_eq,
    Measure.integral_compProd hint,integral_prod _ hinter]
  apply integral_congr_ae
  filter_upwards with b
  have he (p : Fin m → E) :
      (∫ q, f ((b,p),q) ∂stateChildren d c (b,p)) =
      ∫ p', ⟪v,p'-p i⟫ ^ 2 ∂c.kernel i (stateCenter d i b,p i) := by
    dsimp only [f]
    rw [stateChildren_apply]
    let : ∀ k, IsProbabilityMeasure (c.kernel k (stateCenter d k b,p k)) :=
      fun k => by let := c.markov k; infer_instance
    have hh := measurePreserving_eval (fun k => c.kernel k (stateCenter d k b,p k)) i
    have hsm' : StronglyMeasurable (fun x : E => ⟪v,x-p i⟫ ^ 2) := by fun_prop
    simpa only [hh.map_eq] using
      (integral_map_of_stronglyMeasurable (μ := Measure.pi (fun k => c.kernel k (stateCenter d k b,p k))) hh.measurable hsm').symm
  simp_rw [he]
  have hsm : StronglyMeasurable (fun p : E =>
      ∫ p', ⟪v,p'-p⟫ ^ 2 ∂c.kernel i (stateCenter d i b,p)) := by
    have hh : StronglyMeasurable (fun z : E × E =>
        ∫ p', ⟪v,p'-z.2⟫ ^ 2 ∂c.kernel i z) :=
      (show StronglyMeasurable (fun z : (E × E) × E => ⟪v,z.2-z.1.2⟫ ^ 2) by
        fun_prop).integral_kernel_prod_right'
    exact hh.comp_measurable measurable_prodMk_left
  have hh := measurePreserving_eval (fun _ : Fin m => stdGaussian E) i
  rw [← integral_map_of_stronglyMeasurable hh.measurable hsm,hh.map_eq]

end AcceleratedLogConcave.Conditional.MeanReferenceVariance
