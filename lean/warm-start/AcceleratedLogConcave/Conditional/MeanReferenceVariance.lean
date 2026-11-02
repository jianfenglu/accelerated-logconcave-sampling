import AcceleratedLogConcave.Conditional.MeanReferenceLayer

/-!
# Second moments of the actual mean-reference increments

The input and output coordinates are the coordinates of the same retained joint
execution. Moment hypotheses are derived from its constructed Gaussian laws.
-/
noncomputable section
open MeasureTheory ProbabilityTheory AcceleratedLogConcave
open Numerics Numerics.MeanFlowLp Conditional Conditional.MeanReferenceLayer
open scoped RealInnerProductSpace
set_option autoImplicit false
namespace AcceleratedLogConcave.Conditional.MeanReferenceVariance
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι
abbrev Execution (ι : Type*) (m : ℕ) := Host ι m × (Fin m → EuclideanSpace ℝ ι)
def centerIncrement (d : Data ι m) (c : Children d) (z : Execution ι m) : E :=
  (MeanReferenceLayer.phase d c 1 z.1).snd-active d c z.1 none
def childIncrement (d : Data ι m) (c : Children d) (i : Fin m) (z : Execution ι m) : E :=
  z.2 i-active d c z.1 (some i)
def MomentTarget (d : Data ι m) (c : Children d) : Prop :=
  MemLp (centerIncrement d c) 2 (averagedJoint d c) ∧
  ∀ i,MemLp (childIncrement d c i) 2 (averagedJoint d c)
def OrthogonalityTarget (d : Data ι m) (c : Children d) : Prop :=
  (∀ v : E,∀ i j : Fin m,i≠j →
    (∫ z,⟪v,childIncrement d c i z⟫ * ⟪v,childIncrement d c j z⟫ ∂averagedJoint d c)=0) ∧
  (∀ v : E,∀ i : Fin m,
    (∫ z,⟪v,centerIncrement d c z⟫ * ⟪v,childIncrement d c i z⟫ ∂averagedJoint d c)=0)
def AssemblyTarget (d : Data ι m) (c : Children d) : Prop :=
  ∀ v : E,(∫ z,⟪v,d.sigma • (recombine d c z.1 z.2-z.1.1)⟫^2 ∂averagedJoint d c)=
    (d.sigma/2)^2 * (∫ z,⟪v,centerIncrement d c z⟫^2 ∂averagedJoint d c)+
    ∑ i,(GaussLegendre.weight m i*c.scale i)^2 *
      (∫ z,⟪v,childIncrement d c i z⟫^2 ∂averagedJoint d c)

theorem host_preserving (d : Data ι m) (c : Children d) :
    MeasurePreserving Prod.fst (averagedJoint d c) ((stdGaussian E).prod (freshLaw d)) := by
  refine ⟨measurable_fst, ?_⟩
  rw [averagedJoint_eq]
  exact Measure.fst_compProd _ _

theorem active_preserving (d : Data ι m) (c : Children d) (i : Option (Fin m)) :
    MeasurePreserving (fun z : Execution ι m => active d c z.1 i)
      (averagedJoint d c) (stdGaussian E) := by
  have hs : MeasurePreserving
      (fun h : Host ι m => (h.2.1, fun j : Option (Option (Fin m)) =>
        j.elim (reserve d c h) (active d c h)))
      ((stdGaussian E).prod (freshLaw d))
      ((MeanBenchmarkCoupling.positionLaw d).prod
        (Measure.pi (fun _ : Option (Option (Fin m)) => stdGaussian E))) := by
    refine ⟨?_, split_target d c⟩
    apply Measurable.prodMk (measurable_fst.comp measurable_snd)
    apply Measurable.of_eval
    intro j
    cases j
    · exact (continuous_reserve d c).measurable
    · exact (continuous_active d c _).measurable
  exact (measurePreserving_eval (fun _ : Option (Option (Fin m)) => stdGaussian E) (some i)).comp
    (measurePreserving_snd.comp (hs.comp (host_preserving d c)))

def outputCoordinates (d : Data ι m) (c : Children d) (z : Execution ι m)
    (j : Option (Option (Fin m))) : E :=
  j.elim (reserve d c z.1) (fun i => i.elim ((MeanReferenceLayer.phase d c 1 z.1).snd) z.2)

theorem outputCoordinates_preserving (d : Data ι m) (c : Children d) :
    MeasurePreserving (outputCoordinates d c) (averagedJoint d c)
      (Measure.pi (fun _ : Option (Option (Fin m)) => stdGaussian E)) := by
  refine ⟨?_, outputJoint_target d c⟩
  apply Measurable.of_eval
  intro j
  cases j with
  | none => exact (continuous_reserve d c).measurable.comp measurable_fst
  | some i =>
    cases i with
    | none => exact ((WithLp.prod_continuous_ofLp 2 E E).snd.comp
        ((MeanReferenceLayer.continuous_phase d c 1).comp continuous_fst)).measurable
    | some i => exact (measurable_pi_apply i).comp measurable_snd

theorem momentTarget (d : Data ι m) (c : Children d) : MomentTarget d c := by
  have hin (i : Option (Fin m)) :
      MemLp (fun z : Execution ι m => active d c z.1 i) 2 (averagedJoint d c) :=
    IsGaussian.memLp_two_id.comp_measurePreserving (active_preserving d c i)
  have hout (j : Option (Option (Fin m))) :
      MemLp (fun z => outputCoordinates d c z j) 2 (averagedJoint d c) :=
    IsGaussian.memLp_two_id.comp_measurePreserving
      ((measurePreserving_eval (fun _ : Option (Option (Fin m)) => stdGaussian E) j).comp
        (outputCoordinates_preserving d c))
  exact ⟨(hout (some none)).sub (hin none), fun i => (hout (some (some i))).sub (hin (some i))⟩

end AcceleratedLogConcave.Conditional.MeanReferenceVariance
