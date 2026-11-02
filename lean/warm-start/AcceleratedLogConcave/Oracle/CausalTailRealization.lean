import AcceleratedLogConcave.Oracle.CausalTailExtension

/-! The conditional augmentation on the supplied source tape realizes the
same joint law as the syntax-cut extension. Every unread coordinate is retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.CausalTailRealization
open CanonicalTapeMeasurability CanonicalTapeLaw TailOccurrenceCut TailCut CausalTailExtension

variable {d c : ℕ} {Γ Δ : Ctx} {τ σ : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ σ}
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (L : PrimitiveLaws d) (cut : TailCut q p)
local instance : MeasurableSpace (Prefix d cut) := prefixSpace d cut
local instance : MeasurableSpace (Tape d p) := tapeSpace d p
local instance : MeasurableSpace (Tape d q) := tapeSpace d q
local instance : IsProbabilityMeasure (prefixLaw L cut) := prefixLaw_probability L cut
local instance : IsProbabilityMeasure (tapeLaw L p) := tapeLaw_probability L p
local instance : IsProbabilityMeasure (tapeLaw L q) := tapeLaw_probability L q

/-- Integrating the suffix-blind conditional on the actual supplied full tape
recovers the distribution-level extension, at every external parameter. -/
theorem onTape_realizes_extension (κ : Kernel (A × Prefix d cut) B) [IsMarkovKernel κ]
    (a : A) :
    Kernel.sectR (onTape L cut κ) a ∘ₘ tapeLaw L p = extension L cut κ a := by
  let R : Kernel (Prefix d cut) (Prefix d cut × B) := Kernel.id ×ₖ Kernel.sectR κ a
  let J : (Prefix d cut × B) × Tape d q → Tape d p × B :=
    fun z => (join cut (z.1.1,z.2),z.1.2)
  have hJ : Measurable J :=
    (((measurable_join cut).comp (measurable_fst.fst.prodMk measurable_snd)).prodMk
      measurable_fst.snd)
  have hkernel :
      (Kernel.sectR (onTape L cut κ) a).comap (join cut) (measurable_join cut) =
        (R ∥ₖ Kernel.id).map J := by
    ext z : 1
    rw [Kernel.comap_apply, Kernel.map_apply _ hJ]
    simp only [Kernel.sectR_apply, onTape, Kernel.prod_apply, Kernel.deterministic_apply,
      Kernel.comap_apply, split_join, R, Kernel.parallelComp_apply, Kernel.id_apply]
    rw [Measure.dirac_prod, Measure.prod_dirac, Measure.dirac_prod,
      Measure.map_map hJ measurable_prodMk_right,
      Measure.map_map (hJ.comp measurable_prodMk_right) measurable_prodMk_left]
    rfl
  have hjoin : ((prefixLaw L cut).prod (tapeLaw L q)).map (join cut) = tapeLaw L p := by
    rw [← (measurePreserving_split L cut).map_eq,
      Measure.map_map (measurable_join cut) (measurePreserving_split L cut).measurable]
    simp only [Function.comp_def, join_split]
    exact Measure.map_id
  rw [← hjoin, ← Measure.deterministic_comp_eq_map (measurable_join cut),
    Measure.comp_assoc, Kernel.comp_deterministic_eq_comap, hkernel,
    ← Measure.map_comp _ _ hJ, ← Measure.prod_comp_left]
  dsimp only [R]
  rw [← Measure.compProd_eq_comp_prod]
  rw [extension, Kernel.map_apply _ hJ, Kernel.prod_apply, Kernel.const_apply,
    augmentedPrefix, Kernel.compProd_apply_eq_compProd_sectR, Kernel.const_apply]

section Disintegration
variable [StandardBorelSpace B] [Nonempty B]
    [MeasurableSpace.CountableOrCountablyGenerated A (Prefix d cut)]
    (joint : Kernel A (Prefix d cut × B)) [IsMarkovKernel joint]

/-- The disintegrated lower-prefix coupling is realized on the same input tape. -/
theorem onTape_realizes_fromJoint (a : A) :
    Kernel.sectR (onTape L cut (Probability.CausalRetainedExtension.childConditional joint)) a
      ∘ₘ tapeLaw L p = fromJoint L cut joint a :=
  onTape_realizes_extension L cut _ a

/-- The actual-input realization recovers the consumed-prefix/reference joint
and the entire unread source tape as one independent product factor. -/
theorem onTape_fromJoint_split
    (hsource : joint.fst = Kernel.const A (prefixLaw L cut)) (a : A) :
    (Kernel.sectR (onTape L cut (Probability.CausalRetainedExtension.childConditional joint)) a
      ∘ₘ tapeLaw L p).map
        (fun z => (((split cut z.1).1,z.2),(split cut z.1).2)) =
      (joint a).prod (tapeLaw L q) := by
  rw [onTape_realizes_fromJoint]
  have hs := (measurePreserving_split L cut).measurable
  have hm : Measurable (fun z : Tape d p × B =>
      (((split cut z.1).1,z.2),(split cut z.1).2)) :=
    ((hs.comp measurable_fst).fst.prodMk measurable_snd).prodMk
      (hs.comp measurable_fst).snd
  have h := congrArg (fun K : Kernel A ((Prefix d cut × B) × Tape d q) => K a)
    (fromJoint_split L cut joint hsource)
  rw [Kernel.map_apply _ hm, Kernel.prod_apply, Kernel.const_apply] at h
  exact h

end Disintegration
end AcceleratedLogConcave.Oracle.CausalTailRealization
