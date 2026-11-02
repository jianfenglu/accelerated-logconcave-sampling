import AcceleratedLogConcave.Oracle.SelectedBatchJointLaw
import AcceleratedLogConcave.Oracle.ReplaySeedMeasurability

/-! Joint law with the ORIGINAL freshChild seed and source transform.
The right marginal is its exact induced law, not an asserted canonical law. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.TailOccurrenceCut
open MeasureTheory AffineLowering TapeLowering NoisyLayer
open CanonicalTapeMeasurability CanonicalTapeLaw ReplaySeedMeasurability TailCut

variable {n d C : ℕ} {Γ Δ : Ctx} {τ σ : Ty} {host : Prog C Γ τ}
    (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (en : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (slots : ∀ i, Fin ((tapeShape (p i)).gaussianBlocks * (tapeShape (p i)).gaussianBlocks + c i) → Fin C)
    (old : Fin n → Ref Δ .point) (o : Origin)
    (designated : Fin n → Origin)
    (auxiliary : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (next : Prog C (List.replicate n .point ++ Δ) σ)
local notation "children" => (fun i => freshChild (p i) (en i) (slots i) (old i) (designated i) (auxiliary i))

/-- Complete source seed V,Z,R. Full current sibling/continuation retention is
provided separately by current_batch_cut, before this marginal is taken. -/
theorem fresh_seed_joint {W : Type*} [MeasurableSpace W]
    (t : TailCut (.batch o children next) host) (L : PrimitiveLaws d) (i : Fin n)
    (f : Prefix d t → W) (hf : @Measurable _ W (prefixSpace d t) _ f) :
    let : MeasurableSpace (Tape d host) := tapeSpace d host
    let : MeasurableSpace (Prefix d t) := prefixSpace d t
    let : MeasurableSpace (Tape d (children i)) := tapeSpace d (children i)
    let : MeasurableSpace (ResidualTape (p i)) := residualSpace (p i)
    (tapeLaw L host).map (fun ω => (f (split t ω).1,
      freshChildTapeEquiv (p i) (en i) (slots i) (old i) (designated i) (auxiliary i)
        ((split t ω).2.1 i))) =
      ((prefixLaw L t).map f).prod
        ((tapeLaw L (children i)).map
          (freshChildTapeEquiv (p i) (en i) (slots i) (old i) (designated i) (auxiliary i))) := by
  let : MeasurableSpace (ResidualTape (p i)) := residualSpace (p i)
  exact selected_seed_joint o children next t L i f _ hf
    (measurable_freshChildSeed (p i) (en i) (slots i) (old i) (designated i) (auxiliary i))

/-- Exact childRoot-compatible transformed law, retaining designated momentum
and all source uniforms. T may be singular; no covariance completion is assumed. -/
theorem transformed_fresh_seed_joint {W : Type*} [MeasurableSpace W]
    (t : TailCut (.batch o children next) host) (L : PrimitiveLaws d) (i : Fin n)
    (T : Fin (tapeShape (p i)).gaussianBlocks → Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (f : Prefix d t → W) (hf : @Measurable _ W (prefixSpace d t) _ f) :
    let : MeasurableSpace (Tape d host) := tapeSpace d host
    let : MeasurableSpace (Prefix d t) := prefixSpace d t
    let : MeasurableSpace (Tape d (children i)) := tapeSpace d (children i)
    let : MeasurableSpace (Tape d (p i)) := tapeSpace d (p i)
    let seed := transformedSeed (p i) (en i) T ∘
      freshChildTapeEquiv (p i) (en i) (slots i) (old i) (designated i) (auxiliary i)
    (tapeLaw L host).map (fun ω => (f (split t ω).1, seed ((split t ω).2.1 i))) =
      ((prefixLaw L t).map f).prod ((tapeLaw L (children i)).map seed) := by
  let : MeasurableSpace (ResidualTape (p i)) := residualSpace (p i)
  let : MeasurableSpace (Tape d (p i)) := tapeSpace d (p i)
  let : MeasurableSpace (Tape d (children i)) := tapeSpace d (children i)
  exact selected_seed_joint o children next t L i f _ hf
    ((measurable_transformedSeed (p i) (en i) T).comp
      (measurable_freshChildSeed (p i) (en i) (slots i) (old i) (designated i) (auxiliary i)))

end AcceleratedLogConcave.Oracle.TailOccurrenceCut
