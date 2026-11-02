import AcceleratedLogConcave.Oracle.TailOccurrenceCut

/-! The full cut retains all siblings and the full continuation.
Projection derives the selected joint law; the seed's law is its EXACT induced
pushforward. No identification with an untransformed canonical child is made. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.TailOccurrenceCut
open MeasureTheory CanonicalTapeMeasurability CanonicalTapeLaw
open TailCut

variable {c d n : ℕ} {Γ Δ : Ctx} {τ σ : Ty}
    {p : Prog c Γ τ} (o : Origin) (children : Fin n → Prog c Δ .point)
    (next : Prog c (List.replicate n .point ++ Δ) σ)
    (t : TailCut (.batch o children next) p) (L : PrimitiveLaws d)

/-- Focus tape remains (ALL current siblings, COMPLETE continuation).
This is the full cut, not an independence assertion about some abstract tape. -/
theorem current_batch_cut :
    let : MeasurableSpace (Tape d p) := tapeSpace d p
    let : ∀ i, MeasurableSpace (Tape d (children i)) := fun i => tapeSpace d (children i)
    let : MeasurableSpace (Tape d next) := tapeSpace d next
    let : MeasurableSpace (Prefix d t) := prefixSpace d t
    let : MeasurableSpace (Tape d (.batch o children next)) := tapeSpace d (.batch o children next)
    MeasurePreserving (split (d := d) t) (tapeLaw L p)
      ((prefixLaw L t).prod ((Measure.pi fun i => tapeLaw L (children i)).prod (tapeLaw L next))) :=
  measurePreserving_split L t

/-- Independence is DERIVED by projecting the proved recursive-product cut.
The selected seed transform need only be measurable, not invertible. -/
theorem selected_seed_joint {W B : Type*} [MeasurableSpace W] [MeasurableSpace B]
    (i : Fin n) (f : Prefix d t → W) (seed : Tape d (children i) → B)
    (hf : @Measurable (Prefix d t) W (prefixSpace d t) _ f)
    (hs : @Measurable (Tape d (children i)) B (tapeSpace d (children i)) _ seed) :
    let : MeasurableSpace (Tape d p) := tapeSpace d p
    let : MeasurableSpace (Prefix d t) := prefixSpace d t
    let : MeasurableSpace (Tape d (children i)) := tapeSpace d (children i)
    (tapeLaw L p).map (fun ω => (f (split t ω).1, seed ((split t ω).2.1 i))) =
      ((prefixLaw L t).map f).prod ((tapeLaw L (children i)).map seed) := by
  let : MeasurableSpace (Tape d p) := tapeSpace d p
  let : ∀ j, MeasurableSpace (Tape d (children j)) := fun j => tapeSpace d (children j)
  let : MeasurableSpace (Tape d next) := tapeSpace d next
  let : MeasurableSpace (Prefix d t) := prefixSpace d t
  let : ∀ j, IsProbabilityMeasure (tapeLaw L (children j)) := fun j => tapeLaw_probability L _
  let : IsProbabilityMeasure (tapeLaw L next) := tapeLaw_probability L _
  let : IsProbabilityMeasure (prefixLaw L t) := prefixLaw_probability L t
  have hproj : MeasurePreserving
      (fun z : (∀ j, Tape d (children j)) × Tape d next => z.1 i)
      ((Measure.pi fun j => tapeLaw L (children j)).prod (tapeLaw L next))
      (tapeLaw L (children i)) :=
    (measurePreserving_eval (fun j => tapeLaw L (children j)) i).comp
      ⟨measurable_fst, Measure.fst_prod⟩
  have hf' : MeasurePreserving f (prefixLaw L t) ((prefixLaw L t).map f) := ⟨hf,rfl⟩
  have hs' : MeasurePreserving seed (tapeLaw L (children i))
      ((tapeLaw L (children i)).map seed) := ⟨hs,rfl⟩
  exact ((hf'.prod (hs'.comp hproj)).comp (current_batch_cut o children next t L)).map_eq

/-- Canonical split of the ACTUAL selected code retains all its Gaussian
occurrences and every residual leaf. No freshChild replay identification needed. -/
theorem selected_split_joint {W : Type*} [MeasurableSpace W]
    (i : Fin n) (f : Prefix d t → W)
    (hf : @Measurable (Prefix d t) W (prefixSpace d t) _ f) :
    let : MeasurableSpace (Tape d p) := tapeSpace d p
    let : MeasurableSpace (Prefix d t) := prefixSpace d t
    let : MeasurableSpace (TapeLowering.ResidualTape (children i)) := residualSpace (children i)
    (tapeLaw L p).map (fun ω =>
      (f (split t ω).1, TapeLowering.splitTape (children i) ((split t ω).2.1 i))) =
      ((prefixLaw L t).map f).prod
        ((Measure.pi fun _ : TapeLowering.GaussianSlot (children i) => L.pointDraw).prod
          (residualLaw L.uniformDraw (children i))) := by
  let : MeasurableSpace (Tape d p) := tapeSpace d p
  let : MeasurableSpace (Prefix d t) := prefixSpace d t
  let : MeasurableSpace (Tape d (children i)) := tapeSpace d (children i)
  let : MeasurableSpace (TapeLowering.ResidualTape (children i)) := residualSpace (children i)
  dsimp only
  erw [selected_seed_joint o children next t L i f (TapeLowering.splitTape (children i)) hf
    (measurable_splitTape d (children i))]
  rw [(CanonicalTapeFactorization.measurePreserving_splitTape L (children i)).map_eq]

end AcceleratedLogConcave.Oracle.TailOccurrenceCut
