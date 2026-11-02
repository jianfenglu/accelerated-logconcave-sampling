import AcceleratedLogConcave.Oracle.PrivateCompletedReference
import AcceleratedLogConcave.Oracle.MeanInitialComparison
import AcceleratedLogConcave.Oracle.MeanChronologicalHost

/-! Actual incoming private reference augmentation for the mean program.
The conditional reads the original P and the consumed embedded private tape.
It ignores the entire assembly/flow/direct inventory and the unread body. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory MeasurableSpace
namespace AcceleratedLogConcave.Oracle.MeanIncomingPrivateCoupling
open Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open SourceMeanExecutable TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability
open AcceleratedLogConcave.Probability.CausalRetainedExtension
set_option autoImplicit true
private theorem instr_standardBorel (d : ℕ) (i : Instr c Γ τ) :
    @StandardBorelSpace (i.Tape d) (instrSpace d i) := by
  cases i with
  | gaussian => change StandardBorelSpace (Point d); infer_instance
  | uniform => change StandardBorelSpace UniformValue; infer_instance
  | pure _ => change StandardBorelSpace PUnit; infer_instance
  | center => change StandardBorelSpace PUnit; infer_instance
  | momentum => change StandardBorelSpace PUnit; infer_instance
  | grad _ => change StandardBorelSpace PUnit; infer_instance

/-- Countable generation follows from the actual finite syntax, with its
canonical instruction spaces; it is not a supplier hypothesis. -/
private theorem tape_standardBorel (d : ℕ) (p : Prog c Γ τ) :
    @StandardBorelSpace (Tape d p) (tapeSpace d p) := by
  induction p with
  | ret r => change StandardBorelSpace PUnit; infer_instance
  | step o i next ih =>
      let : MeasurableSpace (i.Tape d) := instrSpace d i
      let : MeasurableSpace (Tape d next) := tapeSpace d next
      let : StandardBorelSpace (i.Tape d) := instr_standardBorel d i
      let : StandardBorelSpace (Tape d next) := ih
      change StandardBorelSpace (i.Tape d × Tape d next)
      infer_instance
  | batch o children next ihc ihn =>
      let : ∀ j, MeasurableSpace (Tape d (children j)) := fun j => tapeSpace d (children j)
      let : MeasurableSpace (Tape d next) := tapeSpace d next
      let : ∀ j, StandardBorelSpace (Tape d (children j)) := ihc
      let : StandardBorelSpace (Tape d next) := ihn
      change StandardBorelSpace ((∀ j, Tape d (children j)) × Tape d next)
      infer_instance

local instance canonicalTapeSpace (d : ℕ) (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
local instance canonicalTapeStandardBorel (d : ℕ) (p : Prog c Γ τ) :
    StandardBorelSpace (Tape d p) := tape_standardBorel d p


set_option autoImplicit false
variable {m n a h d : ℕ} (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
    (main : Fin n → ExecutableData) (final : Fin m → ExecutableData) (sampling : ExecutableData)
    (N : ℕ)
local notation "host" => SourceMeanExecutable.program M nodes anchors seeds main final sampling N
local notation "cut" => MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N
local notation "slots" => prefixSlot (a := a) main final sampling ∘ PrefixPublicTable.privateSlot
local instance : MeasurableSpace (Prefix d cut) := prefixSpace d cut

/-- Extract only the actual private source tape, restoring its input-unit
slots; every source Gaussian and uniform coordinate remains the same. -/
def consumed (p : Prefix d cut) : Tape d sampling.program :=
  restoreTape slots sampling.program (fun r => nomatch r) (.there .here) .here
    (p.2.2.1 0)

theorem consumed_measurable : Measurable (consumed (d := d) M nodes anchors seeds main final sampling N) := by
  have hp : Measurable (fun p : Prefix d cut => p.2.2.1 0) :=
    (measurable_pi_apply 0).comp measurable_snd.snd.fst
  exact (ReplaySeedMeasurability.measurable_restoreTape slots sampling.program
    (fun r => nomatch r) (.there .here) .here).comp hp

variable (L : PrimitiveLaws d)
  (J : Kernel (Point d) ((Point d × Tape d sampling.program) × Point d)) [IsMarkovKernel J]

/-- Parameterized disintegration at the literal consumed seed, jointly in
external center. No Gaussian or accuracy assertion about a current call is used. -/
def conditional : Kernel ((Point d × Point d) × Prefix d cut) (Point d) :=
  (childConditional J).comap
    (fun z => (z.1.1,(z.1.2,consumed M nodes anchors seeds main final sampling N z.2)))
    (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk
      ((consumed_measurable M nodes anchors seeds main final sampling N).comp measurable_snd)))

instance conditional_markov : IsMarkovKernel
    (conditional M nodes anchors seeds main final sampling N J) := by
  unfold conditional
  infer_instance

/-- The exact original entire parent sample is retained. The extension sees
only consumed private coordinates, although the cut is at the body boundary. -/
def extension : Kernel ((Point d × Point d) × Tape d host)
    (((Point d × Point d) × Tape d host) × Point d) :=
  CausalTailHistory.onTape L cut (conditional M nodes anchors seeds main final sampling N J)

instance extension_markov : IsMarkovKernel
    (extension M nodes anchors seeds main final sampling N L J) := by
  unfold extension
  infer_instance

theorem extension_original :
    (extension M nodes anchors seeds main final sampling N L J).fst=Kernel.id :=
  CausalTailHistory.onTape_original L cut _


local instance : IsProbabilityMeasure L.pointDraw := L.point_probability
local instance : IsProbabilityMeasure (tapeLaw L host) := tapeLaw_probability L _
local instance : IsProbabilityMeasure (prefixLaw L cut) := prefixLaw_probability L _

/-- Literal original parent input and full canonical tape before augmentation. -/
def prior : Kernel (Point d) ((Point d × Point d) × Tape d host) :=
  ((Kernel.id : Kernel (Point d) (Point d)) ×ₖ Kernel.const (Point d) L.pointDraw) ×ₖ
    Kernel.const (Point d) (tapeLaw L host)

instance prior_markov : IsMarkovKernel (prior M nodes anchors seeds main final sampling N L) := by
  unfold prior
  infer_instance

def consumedLaw (x : Point d) : Measure ((Point d × Point d) × Prefix d cut) :=
  ((Measure.dirac x).prod L.pointDraw).prod (prefixLaw L cut)

instance consumedLaw_probability (x : Point d) : IsProbabilityMeasure
    (consumedLaw M nodes anchors seeds main final sampling N L x) := by
  unfold consumedLaw
  infer_instance

/-- The actual incoming cut is reached on a canonical complete tape. -/
theorem prior_split (x : Point d) :
    (prior M nodes anchors seeds main final sampling N L x).map (CausalTailHistory.unpack cut) =
      (consumedLaw M nodes anchors seeds main final sampling N L x).prod
        (tapeLaw L (body (a := a) (h := h) M nodes main final sampling N)) := by
  let ν := (Measure.dirac x).prod L.pointDraw
  let _ : IsProbabilityMeasure (tapeLaw L (body (a := a) (h := h) M nodes main final sampling N)) :=
    tapeLaw_probability L _
  have hp := (measurePreserving_prodAssoc ν (prefixLaw L cut)
    (tapeLaw L (body (a := a) (h := h) M nodes main final sampling N))).symm.comp
      ((MeasurePreserving.id ν).prod (measurePreserving_split L cut))
  rw [prior,Kernel.prod_apply,Kernel.prod_apply,Kernel.id_apply,Kernel.const_apply,Kernel.const_apply]
  convert hp.map_eq using 1 <;> rfl


/-- Actual private-output augmentation of the original incoming mean source. -/
def kernel : Kernel (Point d) (((Point d × Point d) × Tape d host) × Point d) :=
  extension M nodes anchors seeds main final sampling N L J ∘ₖ
    prior M nodes anchors seeds main final sampling N L

instance kernel_markov : IsMarkovKernel (kernel M nodes anchors seeds main final sampling N L J) := by
  unfold kernel
  infer_instance

theorem kernel_original :
    (kernel M nodes anchors seeds main final sampling N L J).fst =
      prior M nodes anchors seeds main final sampling N L := by
  rw [Kernel.fst_eq,kernel,Kernel.map_comp,← Kernel.fst_eq,extension_original,Kernel.id_comp]

/-- The original whole mean body remains a fresh product after the private
reference has been adjoined from consumed coordinates only. -/
theorem kernel_whole_body (x : Point d) :
    (kernel M nodes anchors seeds main final sampling N L J x).map
      (CausalTailHistory.unpackExtended cut) =
      ((consumedLaw M nodes anchors seeds main final sampling N L x) ⊗ₘ
        conditional M nodes anchors seeds main final sampling N J).prod
          (tapeLaw L (body (a := a) (h := h) M nodes main final sampling N)) := by
  rw [kernel,Kernel.comp_apply,extension]
  exact CausalTailHistory.whole_suffix_fresh_of_split L cut _ _
    (prior_split M nodes anchors seeds main final sampling N L x) _


local instance allTape_probability {c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    IsProbabilityMeasure (tapeLaw L p) := tapeLaw_probability L p
local instance allInstr_probability {c : ℕ} {Γ : Ctx} {τ : Ty} (i : Instr c Γ τ) :
    @IsProbabilityMeasure _ (instrSpace d i) (instrLaw L i) := instrLaw_probability L i

local instance allPrefix_space {c : ℕ} {Γ Δ : Ctx} {τ σ : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ σ} (t : TailCut q p) :
    MeasurableSpace (Prefix d t) := prefixSpace d t

local instance allPrefix_probability {c : ℕ} {Γ Δ : Ctx} {τ σ : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ σ} (t : TailCut q p) :
    @IsProbabilityMeasure _ (prefixSpace d t) (prefixLaw L t) := prefixLaw_probability L t

private theorem third_preserving {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (μa : Measure A) (μb : Measure B) (μc : Measure C) (μd : Measure D)
    [IsProbabilityMeasure μa] [IsProbabilityMeasure μb] [IsProbabilityMeasure μc] [IsProbabilityMeasure μd] :
    MeasurePreserving (fun z : A × B × C × D => z.2.2.1)
      (μa.prod (μb.prod (μc.prod μd))) μc :=
  (measurePreserving_fst (μ := μc) (ν := μd)).comp
    ((measurePreserving_snd (μ := μb) (ν := μc.prod μd)).comp
      (measurePreserving_snd (μ := μa) (ν := μb.prod (μc.prod μd))))

/-- The consumed embedded private occurrence restores its exact standalone
source tape law; the rest of the consumed prefix is only projected away. -/
theorem consumed_preserving : MeasurePreserving
    (consumed M nodes anchors seeds main final sampling N)
    (prefixLaw L cut) (tapeLaw L sampling.program) := by
  have hp : MeasurePreserving (fun p : Prefix d cut => p.2.2.1 0)
      (prefixLaw L cut)
      (tapeLaw L (sampling.program.embed slots (.there .here) .here)) := by
    have hs : MeasurePreserving (fun p : Prefix d cut => p.2.2.1)
        (prefixLaw L cut)
        (Measure.pi fun _ : Fin 1 => tapeLaw L (sampling.program.embed slots (.there .here) .here)) := by
      apply third_preserving
    exact (measurePreserving_eval
      (fun _ : Fin 1 => tapeLaw L (sampling.program.embed slots (.there .here) .here)) 0).comp hs
  exact (FreshChildCanonicalSeedLaw.restoreTape_preserving L slots sampling.program
    (fun r => nomatch r) (.there .here) .here).comp hp

/-- The literal consumed private input has the complete standalone source law. -/
theorem consumed_input_preserving (x : Point d) : MeasurePreserving
    (fun z : (Point d × Point d) × Prefix d cut =>
      (z.1.1,(z.1.2,consumed M nodes anchors seeds main final sampling N z.2)))
    (consumedLaw M nodes anchors seeds main final sampling N L x)
    ((Measure.dirac x).prod (FreshChildRetainedCoupling.sourceLaw L sampling.program)) := by
  exact ((MeasurePreserving.id (Measure.dirac x)).prod
    ((MeasurePreserving.id L.pointDraw).prod
      (consumed_preserving M nodes anchors seeds main final sampling N L))).comp
    (measurePreserving_prodAssoc (Measure.dirac x) L.pointDraw (prefixLaw L cut))

/-- Integrating the parameterized conditional recovers the exact lower private
coupling, including its original designated input and every source coordinate. -/
theorem consumed_joint_law
    (hsource : J.fst = Kernel.const (Point d)
      (FreshChildRetainedCoupling.sourceLaw L sampling.program)) (x : Point d) :
    ((consumedLaw M nodes anchors seeds main final sampling N L x) ⊗ₘ
      conditional M nodes anchors seeds main final sampling N J).map
      (fun z => ((z.1.1.1,(z.1.1.2,
        consumed M nodes anchors seeds main final sampling N z.1.2)),z.2)) =
      ((Measure.dirac x) ⊗ₘ J).map MeasurableEquiv.prodAssoc.symm := by
  have hp := Conditional.MeanReferenceLayer.compProd_comap_push
    (consumedLaw M nodes anchors seeds main final sampling N L x) (childConditional J)
    (fun z : (Point d × Point d) × Prefix d cut =>
      (z.1.1,(z.1.2,consumed M nodes anchors seeds main final sampling N z.2)))
    (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk
      ((consumed_measurable M nodes anchors seeds main final sampling N).comp measurable_snd)))
  change _ = _ at hp
  refine hp.trans ?_
  rw [(consumed_input_preserving M nodes anchors seeds main final sampling N L x).map_eq]
  rw [← Measure.compProd_const, ← Measure.compProd_assoc,
    disintegrate_source J _ hsource]

private theorem secondFourth_preserving {A B C D E : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D] [MeasurableSpace E]
    (μa : Measure A) (μb : Measure B) (μc : Measure C) (μd : Measure D) (μe : Measure E)
    [IsProbabilityMeasure μa] [IsProbabilityMeasure μb] [IsProbabilityMeasure μc]
    [IsProbabilityMeasure μd] [IsProbabilityMeasure μe] :
    MeasurePreserving (fun z : A × B × C × D × E => (z.2.1,z.2.2.2.1))
      (μa.prod (μb.prod (μc.prod (μd.prod μe)))) (μb.prod μd) :=
  ((MeasurePreserving.id μb).prod
    ((measurePreserving_fst (μ := μd) (ν := μe)).comp
      (measurePreserving_snd (μ := μc) (ν := μd.prod μe)))).comp
        (measurePreserving_snd (μ := μa) (ν := μb.prod (μc.prod (μd.prod μe))))

private theorem thirdFifthSeventh_preserving {A B C D E F H I : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    [MeasurableSpace E] [MeasurableSpace F] [MeasurableSpace H] [MeasurableSpace I]
    (μa : Measure A) (μb : Measure B) (μc : Measure C) (μd : Measure D)
    (μe : Measure E) (μf : Measure F) (μh : Measure H) (μi : Measure I)
    [IsProbabilityMeasure μa] [IsProbabilityMeasure μb] [IsProbabilityMeasure μc]
    [IsProbabilityMeasure μd] [IsProbabilityMeasure μe] [IsProbabilityMeasure μf]
    [IsProbabilityMeasure μh] [IsProbabilityMeasure μi] :
    MeasurePreserving (fun z : A × B × C × D × E × F × H × I =>
      (z.2.2.1,(z.2.2.2.2.1,z.2.2.2.2.2.2.1)))
      (μa.prod (μb.prod (μc.prod (μd.prod (μe.prod (μf.prod (μh.prod μi)))))))
      (μc.prod (μe.prod μh)) :=
  ((MeasurePreserving.id μc).prod (secondFourth_preserving μd μe μf μh μi)).comp
    ((measurePreserving_snd (μ := μb) (ν := μc.prod (μd.prod (μe.prod (μf.prod (μh.prod μi)))))).comp
      (measurePreserving_snd (μ := μa) (ν := μb.prod (μc.prod (μd.prod (μe.prod (μf.prod (μh.prod μi))))))))

private theorem dirac_compProd_map {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] (κ : Kernel A B) [IsSFiniteKernel κ] (a : A) :
    (Measure.dirac a) ⊗ₘ κ = (κ a).map (Prod.mk a) := by
  ext s hs
  rw [Measure.dirac_compProd_apply hs,Measure.map_apply measurable_prodMk_left hs]

private theorem compProd_independent_right {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    (κ : Kernel A C) [IsSFiniteKernel κ] :
    ((μ.prod ν) ⊗ₘ κ.comap Prod.fst measurable_fst).map
      (fun z => ((z.1.1,z.2),z.1.2)) = (μ ⊗ₘ κ).prod ν := by
  have hm : Measurable (fun z : (A × B) × C => ((z.1.1,z.2),z.1.2)) :=
    (measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd
  rw [Measure.compProd_eq_comp_prod,Measure.map_comp _ _ hm,
    Measure.compProd_eq_comp_prod,Measure.prod_comp_left]
  congr 1
  ext z : 1
  simp only [Kernel.map_apply _ hm,Kernel.parallelComp_apply,Kernel.prod_apply,Kernel.id_apply,
    Kernel.comap_apply,Measure.dirac_prod,Measure.prod_dirac]
  rw [Measure.map_map hm measurable_prodMk_left,Measure.map_map measurable_prodMk_right measurable_prodMk_left]
  rfl

/-- Complete consumed private source tape, literal assembly draws, and literal
flow draws have their JOINT product law by disjoint source-prefix factors. -/
theorem consumed_inventory_preserving : MeasurePreserving
    (fun p : Prefix d cut => (consumed M nodes anchors seeds main final sampling N p,
      (MeanChronologicalHost.raw M nodes anchors seeds main final sampling N p,
       fun j : Fin h => (show Point d from (p.2.2.2.2.2.2.1 j).1))))
    (prefixLaw L cut)
    ((tapeLaw L sampling.program).prod
      ((Measure.pi fun _ : Fin (m+1) => L.pointDraw).prod (Measure.pi fun _ : Fin h => L.pointDraw))) := by
  have hp : MeasurePreserving (fun p : Prefix d cut =>
      (p.2.2.1,(p.2.2.2.2.1,p.2.2.2.2.2.2.1)))
      (prefixLaw L cut)
      ((Measure.pi fun _ : Fin 1 => tapeLaw L (sampling.program.embed slots (.there .here) .here)).prod
        ((Measure.pi fun i : Fin (m+1) => tapeLaw L (residualDraw (c := size (a := a) main final sampling) (Γ := []) (assemblyOrigin i))).prod
          (Measure.pi fun j : Fin h => tapeLaw L (residualDraw (c := size (a := a) main final sampling) (Γ := []) (flowOrigin j))))) := by
    apply thirdFifthSeventh_preserving
  have hprivate : MeasurePreserving (fun z : Fin 1 → Tape d
      (sampling.program.embed (Δ := [.point,.point]) slots (.there .here) .here) =>
      restoreTape (Δ := [.point,.point]) slots sampling.program (fun r => nomatch r) (.there .here) .here (z 0))
      (Measure.pi fun _ : Fin 1 => tapeLaw L (sampling.program.embed (Δ := [.point,.point]) slots (.there .here) .here))
      (tapeLaw L sampling.program) := (FreshChildCanonicalSeedLaw.restoreTape_preserving (Δ := [.point,.point]) L slots sampling.program
    (fun r => nomatch r) (.there .here) .here).comp
    (measurePreserving_eval (fun _ : Fin 1 => tapeLaw L (sampling.program.embed (Δ := [.point,.point]) slots (.there .here) .here)) 0)
  have hraw := PrivateCausalAdvance.residualBatch_preserving (c := size (a := a) main final sampling) (Γ := []) L (assemblyOrigin (m := m))
  have hflow := PrivateCausalAdvance.residualBatch_preserving (c := size (a := a) main final sampling) (Γ := []) L (flowOrigin (h := h))
  exact (hprivate.prod (hraw.prod hflow)).comp hp

/-- The actual assembly and flow draws, retained as whole finite arrays. -/
def inventory (p : Prefix d cut) : (Fin (m+1) → Point d) × (Fin h → Point d) :=
  (MeanChronologicalHost.raw M nodes anchors seeds main final sampling N p,
    fun j => (p.2.2.2.2.2.2.1 j).1)

def inventoryLaw := (Measure.pi fun _ : Fin (m+1) => L.pointDraw).prod
  (Measure.pi fun _ : Fin h => L.pointDraw)
instance inventoryLaw_probability : IsProbabilityMeasure
    (inventoryLaw (m := m) (h := h) L) := by unfold inventoryLaw; infer_instance

include L in
theorem inventory_measurable : Measurable (inventory (d := d) M nodes anchors seeds main final sampling N) :=
  (consumed_inventory_preserving M nodes anchors seeds main final sampling N L).measurable.snd

def consumedInventory (z : (Point d × Point d) × Prefix d cut) :
    (Point d × (Point d × Tape d sampling.program)) × ((Fin (m+1) → Point d) × (Fin h → Point d)) :=
  ((z.1.1,(z.1.2,consumed M nodes anchors seeds main final sampling N z.2)),
    inventory M nodes anchors seeds main final sampling N z.2)

include L in
theorem consumedInventory_measurable : Measurable
    (consumedInventory (d := d) M nodes anchors seeds main final sampling N) :=
  (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk
    ((consumed_measurable M nodes anchors seeds main final sampling N).comp measurable_snd))).prodMk
      ((inventory_measurable M nodes anchors seeds main final sampling N L).comp measurable_snd)

theorem consumedInventory_preserving (x : Point d) : MeasurePreserving
    (consumedInventory M nodes anchors seeds main final sampling N)
    (consumedLaw M nodes anchors seeds main final sampling N L x)
    (((Measure.dirac x).prod (FreshChildRetainedCoupling.sourceLaw L sampling.program)).prod
      (inventoryLaw (m := m) (h := h) L)) := by
  have hp := (consumed_inventory_preserving M nodes anchors seeds main final sampling N L)
  have h := ((measurePreserving_prodAssoc (Measure.dirac x) L.pointDraw (tapeLaw L sampling.program)).prod
    (MeasurePreserving.id (inventoryLaw (m := m) (h := h) L))).comp
    ((measurePreserving_prodAssoc ((Measure.dirac x).prod L.pointDraw) (tapeLaw L sampling.program)
      (inventoryLaw (m := m) (h := h) L)).symm.comp
        ((MeasurePreserving.id ((Measure.dirac x).prod L.pointDraw)).prod hp))
  exact h

/-- Exact private retained joint WITH the untouched assembly/flow inventory.
Independence is derived from disjoint canonical source factors before the
conditional is applied; no marginal independence inference is used. -/
theorem consumed_joint_inventory_law
    (hsource : J.fst = Kernel.const (Point d)
      (FreshChildRetainedCoupling.sourceLaw L sampling.program)) (x : Point d) :
    ((consumedLaw M nodes anchors seeds main final sampling N L x) ⊗ₘ
      conditional M nodes anchors seeds main final sampling N J).map
      (fun z => (((z.1.1.1,(z.1.1.2,
        consumed M nodes anchors seeds main final sampling N z.1.2)),z.2),
          inventory M nodes anchors seeds main final sampling N z.1.2)) =
      (((Measure.dirac x) ⊗ₘ J).map MeasurableEquiv.prodAssoc.symm).prod
        (inventoryLaw (m := m) (h := h) L) := by
  let κ := childConditional J
  let obs := consumedInventory (d := d) M nodes anchors seeds main final sampling N
  have ho : Measurable obs := consumedInventory_measurable M nodes anchors seeds main final sampling N L
  have hp := Conditional.MeanReferenceLayer.compProd_comap_push
    (consumedLaw M nodes anchors seeds main final sampling N L x) (κ.comap Prod.fst measurable_fst) obs ho
  have he : (κ.comap Prod.fst measurable_fst).comap obs ho =
      conditional M nodes anchors seeds main final sampling N J := rfl
  rw [he,(consumedInventory_preserving M nodes anchors seeds main final sampling N L x).map_eq] at hp
  let rearrange := fun z :
      ((Point d × (Point d × Tape d sampling.program)) × ((Fin (m+1) → Point d) × (Fin h → Point d))) × Point d =>
      ((z.1.1,z.2),z.1.2)
  have hm : Measurable rearrange := (measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd
  have hobs : Measurable (fun z : (((Point d × Point d) × Prefix d cut) × Point d) => (obs z.1,z.2)) :=
    (ho.comp measurable_fst).prodMk measurable_snd
  have hjoin := congrArg (fun η => η.map rearrange) hp
  rw [Measure.map_map hm hobs] at hjoin
  dsimp only [rearrange] at hjoin
  rw [compProd_independent_right] at hjoin
  have hd : (((Measure.dirac x).prod (FreshChildRetainedCoupling.sourceLaw L sampling.program)) ⊗ₘ κ) =
      ((Measure.dirac x) ⊗ₘ J).map MeasurableEquiv.prodAssoc.symm := by
    rw [← Measure.compProd_const,← Measure.compProd_assoc,disintegrate_source J _ hsource]
  rw [hd] at hjoin
  exact hjoin

/-- Exact designated private input/reference pair and complete untouched
assembly/flow inventory at the consumed-prefix law. -/
theorem consumed_pair_inventory_law
    (hsource : J.fst = Kernel.const (Point d)
      (FreshChildRetainedCoupling.sourceLaw L sampling.program)) (x : Point d) :
    ((consumedLaw M nodes anchors seeds main final sampling N L x) ⊗ₘ
      conditional M nodes anchors seeds main final sampling N J).map
      (fun z => ((z.1.1.2,z.2),inventory M nodes anchors seeds main final sampling N z.1.2)) =
      ((J x).map (fun z => (z.1.1,z.2))).prod (inventoryLaw (m := m) (h := h) L) := by
  let drop := fun z : (Point d × (Point d × Tape d sampling.program)) × Point d => (z.1.2.1,z.2)
  have hd : Measurable drop := measurable_fst.snd.fst.prodMk measurable_snd
  have hi := inventory_measurable M nodes anchors seeds main final sampling N L
  have hs := consumed_measurable (d := d) M nodes anchors seeds main final sampling N
  have hobs : Measurable (fun z : (((Point d × Point d) × Prefix d cut) × Point d) =>
      (((z.1.1.1,(z.1.1.2,consumed M nodes anchors seeds main final sampling N z.1.2)),z.2),
        inventory M nodes anchors seeds main final sampling N z.1.2)) :=
    ((measurable_fst.fst.fst.prodMk (measurable_fst.fst.snd.prodMk
      (hs.comp measurable_fst.snd))).prodMk measurable_snd).prodMk (hi.comp measurable_fst.snd)
  have hp := congrArg (fun η => η.map (Prod.map drop id))
    (consumed_joint_inventory_law M nodes anchors seeds main final sampling N L J hsource x)
  rw [Measure.map_map (hd.prodMap measurable_id) hobs,
    ← Measure.map_prod_map _ _ hd measurable_id,Measure.map_id,
    Measure.map_map hd MeasurableEquiv.prodAssoc.symm.measurable,
    dirac_compProd_map,Measure.map_map _ measurable_prodMk_left] at hp
  · exact hp
  · exact hd.comp MeasurableEquiv.prodAssoc.symm.measurable

/-- Joint readout from the augmented FULL original source; P is the literal
original momentum, and the Gaussian arrays are the original prefix draws. -/
def pairedInventory (z : (((Point d × Point d) × Tape d host) × Point d)) :
    (Point d × Point d) × ((Fin (m+1) → Point d) × (Fin h → Point d)) :=
  ((z.1.1.2,z.2),inventory M nodes anchors seeds main final sampling N (split cut z.1.2).1)

include L in
theorem pairedInventory_measurable : Measurable
    (pairedInventory (d := d) M nodes anchors seeds main final sampling N) :=
  (measurable_fst.fst.snd.prodMk measurable_snd).prodMk
    ((inventory_measurable M nodes anchors seeds main final sampling N L).comp
      (((measurePreserving_split L cut).measurable.comp measurable_fst.snd).fst))

/-- Exact JOINT originalP/private-reference/assembly/flow law of the actual
causal incoming kernel. Its proof uses the full consumed-prefix product law. -/
theorem kernel_paired_inventory_law
    (hsource : J.fst = Kernel.const (Point d)
      (FreshChildRetainedCoupling.sourceLaw L sampling.program)) (x : Point d) :
    (kernel M nodes anchors seeds main final sampling N L J x).map
      (pairedInventory M nodes anchors seeds main final sampling N) =
        ((J x).map (fun z => (z.1.1,z.2))).prod (inventoryLaw (m := m) (h := h) L) := by
  let μ := (consumedLaw M nodes anchors seeds main final sampling N L x) ⊗ₘ
    conditional M nodes anchors seeds main final sampling N J
  have hp : MeasurePreserving
      (fun z : (((Point d × Point d) × Tape d host) × Point d) =>
        ((z.1.1,(split cut z.1.2).1),z.2))
      (kernel M nodes anchors seeds main final sampling N L J x) μ :=
    (measurePreserving_fst (μ := μ) (ν := tapeLaw L (body (a := a) (h := h) M nodes main final sampling N))).comp
      ⟨CausalTailHistory.measurable_unpackExtended L cut,
        kernel_whole_body M nodes anchors seeds main final sampling N L J x⟩
  let read := fun z : (((Point d × Point d) × Prefix d cut) × Point d) =>
    ((z.1.1.2,z.2),inventory M nodes anchors seeds main final sampling N z.1.2)
  have hm : Measurable read := (measurable_fst.fst.snd.prodMk measurable_snd).prodMk
    ((inventory_measurable M nodes anchors seeds main final sampling N L).comp measurable_fst.snd)
  have he := congrArg (fun η => η.map read) hp.map_eq
  rw [Measure.map_map hm hp.measurable] at he
  exact he.trans (consumed_pair_inventory_law M nodes anchors seeds main final sampling N L J hsource x)

end AcceleratedLogConcave.Oracle.MeanIncomingPrivateCoupling
