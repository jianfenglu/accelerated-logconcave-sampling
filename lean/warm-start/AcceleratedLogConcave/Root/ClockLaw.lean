import AcceleratedLogConcave.Root.ConditionalLaw
import AcceleratedLogConcave.Kinetic.GaussianEmbedding

/-! The constructed kernel has exactly the downstream joint clock/phase input shape.
Actual node centers are still supplied in the child family; no sampler identification or
W12 estimate is asserted here. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open AcceleratedLogConcave.Kinetic
set_option autoImplicit false
namespace AcceleratedLogConcave.Root.ClockLaw
variable {ι : Type*} [Fintype ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι
abbrev Clock := Icc (0 : ℝ) (1/2)
abbrev Data (ι : Type*) [Fintype ι] (m : ℕ) :=
  ConditionalLaw.Data (Clock × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) ι m

def kernel (d : Data ι m) : Kernel (Clock × GaussianPhase E) E :=
  (ConditionalLaw.rootKernel d).comap (fun z => ((z.1,z.2.1),z.2.2))
    ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd)
instance kernel_markov (d : Data ι m) : IsMarkovKernel (kernel d) := by
  unfold kernel
  infer_instance

def sectionKernel (d : Data ι m) (t : Clock) : Kernel (GaussianPhase E) E :=
  (kernel d).comap (fun z => (t,z)) measurable_prodMk_left

/-- Exact setwise formula consumed by `ConditionallyInvariant` at every clock. -/
theorem section_conditionallyInvariant (d : Data ι m) (t : Clock) :
    ∀ x s, MeasurableSet s →
      (∫⁻ h, sectionKernel d t (x,h) s ∂stdGaussian E) = stdGaussian E s := by
  intro x s hs
  exact ConditionalLaw.rootKernel_conditionallyInvariant d (t,x) s hs

end AcceleratedLogConcave.Root.ClockLaw
