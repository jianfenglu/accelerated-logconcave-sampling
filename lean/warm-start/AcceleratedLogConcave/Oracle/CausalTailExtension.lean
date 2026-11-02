import AcceleratedLogConcave.Oracle.TailOccurrenceCut
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import AcceleratedLogConcave.Probability.CausalRetainedExtension

/-! Causal augmentation of a literal syntax cut. The augmentation reads the
parameter and consumed prefix only. The whole unread tape remains a product
factor, and joining the original coordinates recovers the full source law. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.CausalTailExtension
open CanonicalTapeMeasurability CanonicalTapeLaw TailOccurrenceCut TailCut

variable {d c : ℕ} {Γ Δ : Ctx} {τ σ : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ σ}
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (L : PrimitiveLaws d) (cut : TailCut q p)
local instance : MeasurableSpace (Prefix d cut) := prefixSpace d cut
local instance : MeasurableSpace (Tape d p) := tapeSpace d p
local instance : MeasurableSpace (Tape d q) := tapeSpace d q
local instance : IsProbabilityMeasure (prefixLaw L cut) := prefixLaw_probability L cut
local instance : IsProbabilityMeasure (tapeLaw L q) := tapeLaw_probability L q

/-- The retained prefix may include any lower-depth reference data generated
causally from the consumed source coordinates. -/
def augmentedPrefix (κ : Kernel (A × Prefix d cut) B) : Kernel A (Prefix d cut × B) :=
  Kernel.const A (prefixLaw L cut) ⊗ₖ κ

instance augmentedPrefix_markov (κ : Kernel (A × Prefix d cut) B) [IsMarkovKernel κ] :
    IsMarkovKernel (augmentedPrefix L cut κ) := by
  unfold augmentedPrefix
  infer_instance

/-- No unread coordinate is an input of κ. This keeps every suffix instruction,
including all uniforms, units, siblings and continuation coordinates. -/
def extension (κ : Kernel (A × Prefix d cut) B) : Kernel A (Tape d p × B) :=
  ((augmentedPrefix L cut κ) ×ₖ Kernel.const A (tapeLaw L q)).map
    (fun z => (join cut (z.1.1,z.2),z.1.2))

instance extension_markov (κ : Kernel (A × Prefix d cut) B) [IsMarkovKernel κ] :
    IsMarkovKernel (extension L cut κ) := by
  unfold extension augmentedPrefix
  exact Kernel.IsMarkovKernel.map _
    (((measurable_join cut).comp (measurable_fst.fst.prodMk measurable_snd)).prodMk
      measurable_fst.snd)

/-- Conditional realization on the already supplied tape. Only its consumed
prefix is passed to the augmentation kernel; its full original tape is copied. -/
def onTape (κ : Kernel (A × Prefix d cut) B) : Kernel (A × Tape d p) (Tape d p × B) :=
  Kernel.deterministic Prod.snd measurable_snd ×ₖ
    κ.comap (fun z => (z.1,(split cut z.2).1))
      (measurable_fst.prodMk ((measurePreserving_split L cut).measurable.comp measurable_snd).fst)

instance onTape_markov (κ : Kernel (A × Prefix d cut) B) [IsMarkovKernel κ] :
    IsMarkovKernel (onTape L cut κ) := by
  unfold onTape
  infer_instance

/-- Retention holds at every supplied source tape, not just in distribution. -/
theorem onTape_original (κ : Kernel (A × Prefix d cut) B) [IsMarkovKernel κ] :
    (onTape L cut κ).fst = Kernel.deterministic Prod.snd measurable_snd := by
  unfold onTape
  exact Kernel.fst_prod _ _

/-- Two supplied tapes with the same consumed prefix induce the same reference
conditional, regardless of every coordinate in the unread continuation. -/
theorem onTape_reference_eq (κ : Kernel (A × Prefix d cut) B) [IsMarkovKernel κ]
    (a : A) (u v : Tape d p) (hprefix : (split cut u).1 = (split cut v).1) :
    (onTape L cut κ).snd (a,u) = (onTape L cut κ).snd (a,v) := by
  simp only [onTape, Kernel.snd_prod, Kernel.comap_apply, hprefix]

/-- Exact full-source projection, pointwise in the external parameter. -/
theorem extension_original (κ : Kernel (A × Prefix d cut) B) [IsMarkovKernel κ] :
    (extension L cut κ).fst = Kernel.const A (tapeLaw L p) := by
  have hj : Measurable (fun z : (Prefix d cut × B) × Tape d q =>
      (join cut (z.1.1,z.2),z.1.2)) :=
    (((measurable_join cut).comp (measurable_fst.fst.prodMk measurable_snd)).prodMk
      measurable_fst.snd)
  have hjoin : ((prefixLaw L cut).prod (tapeLaw L q)).map (join cut) = tapeLaw L p := by
    rw [← (measurePreserving_split L cut).map_eq,
      Measure.map_map (measurable_join cut) (measurePreserving_split L cut).measurable]
    simp only [Function.comp_def, join_split]
    exact Measure.map_id
  rw [Kernel.fst_eq]
  unfold extension
  rw [← Kernel.map_comp_right _ hj measurable_fst]
  have hf : (fun z : (Prefix d cut × B) × Tape d q =>
      (join cut (z.1.1,z.2),z.1.2).1) =
      (join cut) ∘ (Prod.map Prod.fst id) := rfl
  change ((augmentedPrefix L cut κ ×ₖ Kernel.const A (tapeLaw L q)).map
    (fun z => (join cut (z.1.1,z.2),z.1.2).1)) = _
  rw [hf, Kernel.map_comp_right _ (measurable_fst.prodMap measurable_id) (measurable_join cut),
    ← Kernel.map_prod_map _ _ measurable_fst measurable_id]
  rw [← Kernel.fst_eq]
  simp only [augmentedPrefix, Kernel.fst_compProd, Kernel.map_id, Kernel.prod_const]
  ext a
  rw [Kernel.map_apply _ (measurable_join cut), Kernel.const_apply, hjoin, Kernel.const_apply]

/-- Splitting the augmented execution restores a fresh WHOLE suffix, jointly
with the augmented past. This is a joint-law equality, not coordinate marginals. -/
theorem extension_split (κ : Kernel (A × Prefix d cut) B) [IsMarkovKernel κ] :
    (extension L cut κ).map (fun z => (((split cut z.1).1,z.2),(split cut z.1).2)) =
      augmentedPrefix L cut κ ×ₖ Kernel.const A (tapeLaw L q) := by
  have hj : Measurable (fun z : (Prefix d cut × B) × Tape d q =>
      (join cut (z.1.1,z.2),z.1.2)) :=
    (((measurable_join cut).comp (measurable_fst.fst.prodMk measurable_snd)).prodMk
      measurable_fst.snd)
  have hs := (measurePreserving_split L cut).measurable
  unfold extension
  have hsplit : Measurable (fun z : Tape d p × B =>
      (((split cut z.1).1,z.2),(split cut z.1).2)) := by
    exact (((hs.comp measurable_fst).fst.prodMk measurable_snd).prodMk
      (hs.comp measurable_fst).snd)
  rw [← Kernel.map_comp_right _ hj hsplit]
  convert Kernel.map_id (augmentedPrefix L cut κ ×ₖ Kernel.const A (tapeLaw L q)) using 1
  congr 1
  funext z
  simp only [Function.comp_def, split_join, id_eq]

section Disintegration
variable [StandardBorelSpace B] [Nonempty B]
    [MeasurableSpace.CountableOrCountablyGenerated A (Prefix d cut)]
    (joint : Kernel A (Prefix d cut × B)) [IsMarkovKernel joint]

/-- Construct a syntax-tail extension by parameterized disintegration of the
already-built consumed-prefix coupling. No disintegration is chosen separately
at each center. -/
def fromJoint : Kernel A (Tape d p × B) :=
  extension L cut (Probability.CausalRetainedExtension.childConditional joint)

instance fromJoint_markov : IsMarkovKernel (fromJoint L cut joint) := by
  unfold fromJoint
  infer_instance

theorem fromJoint_original :
    (fromJoint L cut joint).fst = Kernel.const A (tapeLaw L p) :=
  extension_original L cut _

/-- The consumed-prefix/reference joint is recovered exactly, with every unread
source coordinate still fresh as one product factor. -/
theorem fromJoint_split
    (hsource : joint.fst = Kernel.const A (prefixLaw L cut)) :
    (fromJoint L cut joint).map
      (fun z => (((split cut z.1).1,z.2),(split cut z.1).2)) =
      joint ×ₖ Kernel.const A (tapeLaw L q) := by
  rw [fromJoint, extension_split]
  unfold augmentedPrefix
  rw [Probability.CausalRetainedExtension.disintegrate_source joint _ hsource]

end Disintegration
end AcceleratedLogConcave.Oracle.CausalTailExtension
