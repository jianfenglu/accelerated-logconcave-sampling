import AcceleratedLogConcave.Oracle.MeanIncomingAssemblyLaw

/-! Actual incoming mean law from the constructed private retained coupling.
All original source coordinates and the complete unread mean body are retained;
the full GE/phase/Pi law comes from their explicit joint law. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.MeanIncomingCompletedLaw
open Numerics Numerics.AffineGraph AffineLowering TapeLowering SourceMeanExecutable
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability
open MeanIncomingPrivateCoupling
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
local instance canonicalPrefixSpace {d c : ℕ} {Γ Δ : Ctx} {τ σ : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ σ} (path : TailCut q p) :
    MeasurableSpace (Prefix d path) := prefixSpace d path
variable {m n a h d : ℕ} (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
  (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
  (main : Fin n → ExecutableData) (final : Fin m → ExecutableData) (sampling : ExecutableData) (N : ℕ)
local notation "host" => SourceMeanExecutable.program M nodes anchors seeds main final sampling N
local notation "cut" => MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N
abbrev History (d : ℕ) := (Point d × Point d) × Point d

variable (L : PrimitiveLaws d)
  (J : Kernel (Point d) ((Point d × Tape d sampling.program) × Point d)) [IsMarkovKernel J]

/-- Regroup the newly adjoined actual private reference into incoming history. -/
def kernel := (MeanIncomingPrivateCoupling.kernel M nodes anchors seeds main final sampling N L J).map
  PrivateCausalAdvance.regroupOriginal

instance kernel_markov : IsMarkovKernel (kernel M nodes anchors seeds main final sampling N L J) := by
  unfold kernel
  exact Kernel.IsMarkovKernel.map _ PrivateCausalAdvance.regroupOriginal_measurable

def bodyPrefixLaw (base : Point d) :=
  ((consumedLaw M nodes anchors seeds main final sampling N L base) ⊗ₘ
    conditional M nodes anchors seeds main final sampling N J).map (PrivateCausalAdvance.regroupPrefix cut)

instance bodyPrefixLaw_probability (base : Point d) :
    IsProbabilityMeasure (bodyPrefixLaw M nodes anchors seeds main final sampling N L J base) := by
  unfold bodyPrefixLaw
  infer_instance

/-- Exact unchanged full-body product after the actual private augmentation. -/
theorem kernel_body_split (base : Point d) :
    (kernel M nodes anchors seeds main final sampling N L J base).map (CausalTailHistory.unpack cut) =
      (bodyPrefixLaw M nodes anchors seeds main final sampling N L J base).prod
        (tapeLaw L (body (a := a) (h := h) M nodes main final sampling N)) := by
  rw [kernel,Kernel.map_apply _ PrivateCausalAdvance.regroupOriginal_measurable]
  exact PrivateCausalAdvance.regroup_cut_law L cut _ _
    (kernel_whole_body M nodes anchors seeds main final sampling N L J base)

variable (hL : L.pointDraw=stdGaussian (Point d))
  {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0≤ell)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ F) z v v≤ell*‖v‖^2)
  (r σ : ℝ) (hr : 0<r) (hσ : 0<σ) (hsmall : r^2*ell≤1/2)

def center (a : History d) : Point d := a.1.1
def momentum (a : History d) : Point d := a.1.2
def position (a : History d) : Point d := backwardEnd M.R • a.2

include hL in
/-- Concrete incoming full assembly/phase law. The private pair assumption is
an exact LOWER retained law, to be specialized below by its published producer. -/
theorem incoming_augmented_law
    (hsource : J.fst=Kernel.const (Point d) (FreshChildRetainedCoupling.sourceLaw L sampling.program))
    (base : Point d)
    (hprivate : (J base).map (fun z => (z.1.1,z.2)) = (stdGaussian (Point d)).prod
      (Channels.forward (Conditional.baseLaw F base r) ⟨(M.R/backwardEnd M.R)^2,by positivity⟩)) :
    (bodyPrefixLaw M nodes anchors seeds main final sampling N L J base).map
      (MeanCompletedAugmentedLaws.incomingAugmented M nodes anchors seeds main final sampling N r hr
        (center (d := d)) (momentum (d := d)) (position M) hF hell hlo hup σ hσ hsmall base) =
      ((stdGaussian (Point d)).prod (MeanFlowLp.seedMeasure
        (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base))).prod
          (Measure.pi fun _ : Fin m => stdGaussian (Point d)) := by
  let read := fun z : (((Point d × Point d) × Prefix d cut) × Point d) =>
    ((z.1.1.2,z.2),inventory M nodes anchors seeds main final sampling N z.1.2)
  have hm : Measurable read := (measurable_fst.fst.snd.prodMk measurable_snd).prodMk
    ((inventory_measurable M nodes anchors seeds main final sampling N L).comp measurable_fst.snd)
  let assemble := MeanIncomingAssemblyLaw.assembledInventory M seeds hF hell hlo hup r σ hr hσ hsmall base
  have ha := MeanIncomingAssemblyLaw.assembledInventory_preserving M seeds hF hell hlo hup r σ hr hσ hsmall base
  have hi := MeanCompletedAugmentedLaws.incomingAugmented_measurable M nodes anchors seeds main final sampling N r hr
    (center (d := d)) (momentum (d := d)) (position M) measurable_fst.fst measurable_fst.snd
    (measurable_snd.const_smul (backwardEnd M.R)) hF hell hlo hup σ hσ hsmall base
  rw [bodyPrefixLaw,Measure.map_map hi (PrivateCausalAdvance.regroupPrefix_measurable cut)]
  have he : (MeanCompletedAugmentedLaws.incomingAugmented M nodes anchors seeds main final sampling N r hr
      (center (d := d)) (momentum (d := d)) (position M) hF hell hlo hup σ hσ hsmall base) ∘
      (PrivateCausalAdvance.regroupPrefix cut) = assemble ∘ read := rfl
  rw [he,← Measure.map_map ha.measurable hm,
    consumed_pair_inventory_law M nodes anchors seeds main final sampling N L J hsource base,hprivate]
  unfold inventoryLaw
  rw [hL]
  exact ha.map_eq

end AcceleratedLogConcave.Oracle.MeanIncomingCompletedLaw
