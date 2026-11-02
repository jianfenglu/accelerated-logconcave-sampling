import AcceleratedLogConcave.Oracle.DesignatedChildBatchCoupling

/-! Exact retained-pair transport for the literal designated-child conditionals.
The old sample may contain arbitrary correlated history and complete tapes;
only the stated observation is projected for the marginal calculation. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.DesignatedChildBatchJointTransfer
open DesignatedChildBatchCoupling Conditional.MeanReferenceLayer
open CanonicalTapeLaw CanonicalTapeMeasurability
local instance canonicalTapeSpace (d : ℕ) (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
set_option backward.isDefEq.respectTransparency false
variable {d N C : ℕ} {Γ : Ctx}
  (L : PrimitiveLaws d) (hL : L.pointDraw = stdGaussian (Point d))
  (B : Data N C Γ) (J : Lower L B)
  {H : Type*} [MeasurableSpace H]
  (center : Fin N → H → Point d) (hcenter : ∀ i, Measurable (center i))

/-- Parameterized retained-pair law is constructed by averaging the actual
same-seed conditional, so its measurability is proved by kernel composition. -/
def averagedPairs : Kernel H (Fin N → Point d × Point d) :=
  pairedBatch L hL B J center hcenter ∘ₖ
    ((Kernel.id : Kernel H H) ×ₖ Kernel.const H (Measure.pi (rawLaw L B)))
instance averagedPairs_markov : IsMarkovKernel (averagedPairs L hL B J center hcenter) := by
  unfold averagedPairs
  infer_instance

theorem averagedPairs_apply (h : H) :
    averagedPairs L hL B J center hcenter h =
      Measure.pi (fun i => (J.joint i (center i h)).map (fun z => (z.1.1,z.2))) := by
  rw [averagedPairs, Kernel.comp_apply, Kernel.prod_apply, Kernel.id_apply,
    Kernel.const_apply, Measure.dirac_prod, bind_map_input _ _ _ measurable_prodMk_left]
  exact pairedBatch_law L hL B J center hcenter h

private theorem retained_average {P Q : Type*} [MeasurableSpace P] [MeasurableSpace Q]
    (μ : Measure H) [IsProbabilityMeasure μ] (ν : Measure P) [IsProbabilityMeasure ν]
    (k : Kernel (H × P) Q) [IsMarkovKernel k] :
    ((Kernel.deterministic Prod.fst measurable_fst) ×ₖ k) ∘ₘ (μ.prod ν) =
      μ ⊗ₘ (k ∘ₖ ((Kernel.id : Kernel H H) ×ₖ Kernel.const H ν)) := by
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.bind_apply (hs.prod ht) (Kernel.aemeasurable _),Measure.compProd_apply_prod hs ht]
  simp_rw [Kernel.prod_apply_prod,Kernel.deterministic_apply]
  have hD : Measurable (fun b : H => (Measure.dirac b) s) :=
    (Measure.measurable_coe hs).comp Measure.measurable_dirac
  have hM : Measurable (fun a : H × P => (Measure.dirac a.1) s*k a t) :=
    (hD.comp measurable_fst).mul (k.measurable_coe ht)
  rw [lintegral_prod _ hM.aemeasurable]
  have he : ∀ b, (∫⁻ p, (Measure.dirac b) s*k (b,p) t ∂ν) =
      (Measure.dirac b) s*(k ∘ₖ ((Kernel.id : Kernel H H) ×ₖ Kernel.const H ν)) b t := by
    intro b
    have hm : Measurable (fun p : P => k (b,p) t) :=
      (k.measurable_coe ht).comp measurable_prodMk_left
    rw [lintegral_const_mul _ hm]
    congr 1
    rw [Kernel.comp_apply' _ _ _ ht,Kernel.lintegral_id_prod (k.measurable_coe ht)]
    rfl
  simp_rw [he]
  simp only [Measure.dirac_apply' _ hs]
  rw [← lintegral_indicator hs]
  apply lintegral_congr
  intro b
  by_cases hb : b ∈ s <;> simp [hb]

/-- The coarse variable is kept, while the exact child retained-pair kernel
is averaged measurably over the original full raw occurrence inventory. -/
theorem coarse_pairs (ν : Measure H) [IsProbabilityMeasure ν] :
    ((ν.prod (Measure.pi (rawLaw L B))) ⊗ₘ referenceBatch L hL B J center hcenter).map
      (fun z => (z.1.1,fun i => ((z.1.2 i).2.1,z.2 i))) =
      ν ⊗ₘ averagedPairs L hL B J center hcenter := by
  rw [Measure.compProd_eq_comp_prod,Measure.map_comp _ _ (by fun_prop)]
  have hk : ((Kernel.id ×ₖ referenceBatch L hL B J center hcenter).map
      (fun z => (z.1.1,fun i => ((z.1.2 i).2.1,z.2 i)))) =
      (Kernel.deterministic Prod.fst measurable_fst) ×ₖ pairedBatch L hL B J center hcenter := by
    ext z s hs
    rw [Kernel.map_apply _ (by fun_prop),Kernel.prod_apply,Kernel.id_apply,
      Kernel.prod_apply,Kernel.deterministic_apply,pairedBatch,Kernel.map_apply _ (by fun_prop),
      retainedBatch,Kernel.prod_apply,Kernel.id_apply]
    rw [Measure.dirac_prod,Measure.dirac_prod,
      Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [hk]
  exact retained_average ν (Measure.pi (rawLaw L B)) (pairedBatch L hL B J center hcenter)

/-- The needed source observation may come from arbitrary correlated past
and full original tape. Only its coarse/raw projection factors; μ is retained
unchanged and the conclusion is the exact lower retained-pair kernel. -/
theorem observed_coarse_pairs {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (ν : Measure H) [IsProbabilityMeasure ν]
    (observe : A → H × (∀ i, Raw d B i)) (ho : Measurable observe)
    (hobserve : μ.map observe = ν.prod (Measure.pi (rawLaw L B))) :
    (μ ⊗ₘ (referenceBatch L hL B J center hcenter).comap observe ho).map
      (fun z => ((observe z.1).1,fun i => (((observe z.1).2 i).2.1,z.2 i))) =
      ν ⊗ₘ averagedPairs L hL B J center hcenter := by
  have hp := compProd_comap_push μ (referenceBatch L hL B J center hcenter) observe ho
  rw [hobserve] at hp
  have hm : Measurable (fun z : (H × (∀ i, Raw d B i)) × (Fin N → Point d) =>
      (z.1.1,fun i => ((z.1.2 i).2.1,z.2 i))) := by fun_prop
  have hh := congrArg (fun ρ : Measure ((H × (∀ i, Raw d B i)) × (Fin N → Point d)) =>
    ρ.map (fun z => (z.1.1,fun i => ((z.1.2 i).2.1,z.2 i)))) hp
  have hfull : Measurable (fun z : A × (Fin N → Point d) => (observe z.1,z.2)) := by fun_prop
  rw [Measure.map_map hm hfull] at hh
  exact hh.trans (coarse_pairs L hL B J center hcenter ν)

/-- Arbitrary complete old sample is retained as the first compProd coordinate.
This exact observation law is an AE disintegration adapter, never a pointwise
claim about a conditional lower joint. -/
theorem observed_joint {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ]
    (ν : Measure (H × (∀ i, Raw d B i)))
    (observe : A → H × (∀ i, Raw d B i)) (ho : Measurable observe)
    (hobserve : μ.map observe = ν) :
    (μ ⊗ₘ (referenceBatch L hL B J center hcenter).comap observe ho).map
      (fun z => (observe z.1,z.2)) =
      ν ⊗ₘ referenceBatch L hL B J center hcenter := by
  rw [compProd_comap_push, hobserve]

/-- Exact pair-vector law on an arbitrary retained original sample with the
canonical observation, at any fixed coarse datum. This retains all hidden
originalP correlations in μ itself. -/
theorem observed_fixed_pairs {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ]
    (observe : A → ∀ i, Raw d B i) (ho : Measurable observe)
    (hobserve : μ.map observe = Measure.pi (rawLaw L B)) (h : H) :
    (μ ⊗ₘ (referenceBatch L hL B J center hcenter).comap
      (fun a => (h,observe a)) (measurable_const.prodMk ho)).map
        (fun z i => ((observe z.1 i).2.1,z.2 i)) =
      Measure.pi (fun i => (J.joint i (center i h)).map (fun z => (z.1.1,z.2))) := by
  let k := (referenceBatch L hL B J center hcenter).comap
    (fun w => (h,w)) measurable_prodMk_left
  have hp := compProd_comap_push μ k observe ho
  rw [hobserve] at hp
  have hm : Measurable (fun z : (∀ i, Raw d B i) × (Fin N → Point d) =>
      fun i => ((z.1 i).2.1,z.2 i)) := by fun_prop
  have hh := congrArg (fun ρ : Measure ((∀ i, Raw d B i) × (Fin N → Point d)) =>
    ρ.map (fun z i => ((z.1 i).2.1,z.2 i))) hp
  have hfull : Measurable (fun z : A × (Fin N → Point d) => (observe z.1,z.2)) := by fun_prop
  rw [Measure.map_map hm hfull] at hh
  have hl := pairedBatch_law L hL B J center hcenter h
  rw [← hl]
  refine hh.trans ?_
  rw [Measure.compProd_eq_comp_prod, Measure.map_comp _ _ hm]
  congr 1
  ext w s hs
  change (((Kernel.id ×ₖ k).map (fun z i => ((z.1 i).2.1,z.2 i))) w) s =
    pairedBatch L hL B J center hcenter (h,w) s
  rw [Kernel.map_apply _ hm, Kernel.prod_apply, Kernel.id_apply]
  rw [pairedBatch,Kernel.map_apply _ (by fun_prop),retainedBatch,
    Kernel.prod_apply,Kernel.id_apply]
  rw [Measure.dirac_prod,Measure.dirac_prod,
    Measure.map_map (by fun_prop) (by fun_prop),Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

end AcceleratedLogConcave.Oracle.DesignatedChildBatchJointTransfer
