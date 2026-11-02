import AcceleratedLogConcave.Oracle.ReplaySeedMeasurability
import AcceleratedLogConcave.Oracle.SamplingCanonicalSplitFactorization

/-! Canonical ORIGINAL seed law derived from
recursive tapeLaw. No extra independence or Gaussian-distribution premise.
The primitive pointDraw need only have the normalization already in PrimitiveLaws. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.FreshChildCanonicalSeedLaw
open MeasureTheory AffineLowering TapeLowering NoisyLayer
open CanonicalTapeLaw CanonicalTapeMeasurability ReplaySeedMeasurability
variable {c c' d n : ℕ} {Γ Δ : Ctx} {τ : Ty}

private theorem insertUnit {A : Type*} [MeasurableSpace A] (μ : Measure A) [SFinite μ] :
    MeasurePreserving (fun x : A => (PUnit.unit, x)) μ
      ((Measure.dirac PUnit.unit).prod μ) :=
  ⟨measurable_const.prodMk measurable_id, (Measure.dirac_prod _).symm⟩

/-- Lowering removes only input-unit instructions. Every Gaussian and uniform
leaf and all child/tail products are unchanged. This is a derived law. -/
theorem restoreTape_preserving (L : PrimitiveLaws d) (κ : Fin c → Fin c')
    (p : Prog c Γ τ) : ∀ {Δ : Ctx} (f : RefMap Γ Δ) (x v : Ref Δ .point),
    @MeasurePreserving _ _ (tapeSpace d (p.lower κ f x v)) (tapeSpace d p)
      (restoreTape κ p f x v) (tapeLaw L (p.lower κ f x v)) (tapeLaw L p) := by
  let tapeMeasurable (c₀ : ℕ) (Γ₀ : Ctx) (τ₀ : Ty) (q : Prog c₀ Γ₀ τ₀) :
      MeasurableSpace (Tape d q) := tapeSpace d q
  let residualMeasurable (c₀ : ℕ) (Γ₀ : Ctx) (τ₀ : Ty) (q : Prog c₀ Γ₀ τ₀) :
      MeasurableSpace (ResidualTape q) := residualSpace q
  let instructionMeasurable (c₀ : ℕ) (Γ₀ : Ctx) (τ₀ : Ty) (a : Instr c₀ Γ₀ τ₀) :
      MeasurableSpace (Instr.Tape d a) := instrSpace d a
  let : IsProbabilityMeasure L.pointDraw := L.point_probability
  let : IsProbabilityMeasure L.uniformDraw := L.uniform_probability
  let instructionProbability (c₀ : ℕ) (Γ₀ : Ctx) (τ₀ : Ty) (a : Instr c₀ Γ₀ τ₀) :
      IsProbabilityMeasure (instrLaw L a) := instrLaw_probability L a
  let tapeProbability (c₀ : ℕ) (Γ₀ : Ctx) (τ₀ : Ty) (q : Prog c₀ Γ₀ τ₀) :
      IsProbabilityMeasure (tapeLaw L q) := tapeLaw_probability L q
  let residualProbability (c₀ : ℕ) (Γ₀ : Ctx) (τ₀ : Ty) (q : Prog c₀ Γ₀ τ₀) :
      IsProbabilityMeasure (residualLaw L.uniformDraw q) :=
    residualLaw_probability L.uniformDraw q
  induction p with
  | ret r => intro Δ f x v; exact MeasurePreserving.id _
  | step o a next ih =>
    intro Δ f x v
    cases a with
    | center => exact (insertUnit _).comp (ih _ _ _)
    | momentum => exact (insertUnit _).comp (ih _ _ _)
    | pure a => exact (MeasurePreserving.id _).prod (ih _ _ _)
    | grad a => exact (MeasurePreserving.id _).prod (ih _ _ _)
    | gaussian => exact (MeasurePreserving.id _).prod (ih _ _ _)
    | uniform => exact (MeasurePreserving.id _).prod (ih _ _ _)
  | batch o children next ihc iht =>
    intro Δ f x v
    let : ∀ j, MeasurableSpace (Tape d (children j)) := fun j => tapeSpace d _
    let : ∀ j, MeasurableSpace (Tape d ((children j).lower κ f x v)) := fun j => tapeSpace d _
    exact (measurePreserving_pi _ _ (fun j => ihc j f x v)).prod (iht _ _ _)

/-- Replay removes Gaussian/input instructions, but restores each original unit
slot. Uniforms are IDENTITIES, including every recursively nested child/tail. -/
theorem restoreReplay_preserving (L : PrimitiveLaws d) (κ : Fin c → Fin c')
    (p : Prog c Γ τ) : ∀ {Δ : Ctx} (f : RefMap Γ Δ)
      (slots : GaussianSlot p → Ref Δ .point) (x v : Ref Δ .point),
    @MeasurePreserving _ _ (tapeSpace d (replayGaussian κ p f slots x v))
      (residualSpace p) (restoreReplayTape κ p f slots x v)
      (tapeLaw L (replayGaussian κ p f slots x v)) (residualLaw L.uniformDraw p) := by
  let tapeMeasurable (c₀ : ℕ) (Γ₀ : Ctx) (τ₀ : Ty) (q : Prog c₀ Γ₀ τ₀) :
      MeasurableSpace (Tape d q) := tapeSpace d q
  let residualMeasurable (c₀ : ℕ) (Γ₀ : Ctx) (τ₀ : Ty) (q : Prog c₀ Γ₀ τ₀) :
      MeasurableSpace (ResidualTape q) := residualSpace q
  let instructionMeasurable (c₀ : ℕ) (Γ₀ : Ctx) (τ₀ : Ty) (a : Instr c₀ Γ₀ τ₀) :
      MeasurableSpace (Instr.Tape d a) := instrSpace d a
  let : IsProbabilityMeasure L.pointDraw := L.point_probability
  let : IsProbabilityMeasure L.uniformDraw := L.uniform_probability
  let instructionProbability (c₀ : ℕ) (Γ₀ : Ctx) (τ₀ : Ty) (a : Instr c₀ Γ₀ τ₀) :
      IsProbabilityMeasure (instrLaw L a) := instrLaw_probability L a
  let tapeProbability (c₀ : ℕ) (Γ₀ : Ctx) (τ₀ : Ty) (q : Prog c₀ Γ₀ τ₀) :
      IsProbabilityMeasure (tapeLaw L q) := tapeLaw_probability L q
  let residualProbability (c₀ : ℕ) (Γ₀ : Ctx) (τ₀ : Ty) (q : Prog c₀ Γ₀ τ₀) :
      IsProbabilityMeasure (residualLaw L.uniformDraw q) :=
    residualLaw_probability L.uniformDraw q
  induction p with
  | ret r => intro Δ f slots x v; exact MeasurePreserving.id _
  | step o a next ih =>
    intro Δ f slots x v
    cases a with
    | center => exact (insertUnit _).comp (ih _ _ _ _)
    | momentum => exact (insertUnit _).comp (ih _ _ _ _)
    | gaussian => exact (insertUnit _).comp (ih _ _ _ _)
    | pure a => exact (MeasurePreserving.id _).prod (ih _ _ _ _)
    | grad a => exact (MeasurePreserving.id _).prod (ih _ _ _ _)
    | uniform => exact (MeasurePreserving.id L.uniformDraw).prod (ih _ _ _ _)
  | batch o children next ihc iht =>
    intro Δ f slots x v
    let : ∀ j, MeasurableSpace (ResidualTape (children j)) := fun j => residualSpace _
    let : ∀ j, MeasurableSpace
      (Tape d (replayGaussian κ (children j) f (fun s => slots (.inl ⟨j,s⟩)) x v)) :=
        fun j => tapeSpace d _
    exact (measurePreserving_pi _ _
      (fun j => ihc j f (fun s => slots (.inl ⟨j,s⟩)) x v)).prod (iht _ _ _ _)

/-- A normalized discarded factor. This never discards any original uniform:
only compiler administrative coordinates are dropped in its uses below. -/
private theorem dropLeft {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [SFinite ν] :
    MeasurePreserving Prod.snd (μ.prod ν) ν := ⟨measurable_snd, Measure.snd_prod⟩

private theorem dropRight {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure ν] :
    MeasurePreserving Prod.fst (μ.prod ν) μ := ⟨measurable_fst, Measure.fst_prod⟩

/-- Enumerated raw auxiliary array × complete ORIGINAL residual law. The
replay result, not a newly supplied residual tape, supplies the second factor. -/
theorem compiledSeed_preserving (L : PrimitiveLaws d) (p : Program c τ)
    (e : GaussianSlot p ≃ Fin n) (origin : Fin n → Origin) :
    let : MeasurableSpace (Tape d (compileWith p e origin)) := tapeSpace d _
    let : MeasurableSpace (ResidualTape p) := residualSpace p
    MeasurePreserving (compiledTapeEquivWith (d := d) p e origin)
      (tapeLaw L (compileWith p e origin))
      ((Measure.pi fun _ : Fin n => L.pointDraw).prod (residualLaw L.uniformDraw p)) := by
  dsimp only
  let tapeMeasurable (c₀ : ℕ) (Γ₀ : Ctx) (τ₀ : Ty) (q : Prog c₀ Γ₀ τ₀) :
      MeasurableSpace (Tape d q) := tapeSpace d q
  let residualMeasurable (c₀ : ℕ) (Γ₀ : Ctx) (τ₀ : Ty) (q : Prog c₀ Γ₀ τ₀) :
      MeasurableSpace (ResidualTape q) := residualSpace q
  let instructionMeasurable (c₀ : ℕ) (Γ₀ : Ctx) (τ₀ : Ty) (a : Instr c₀ Γ₀ τ₀) :
      MeasurableSpace (Instr.Tape d a) := instrSpace d a
  let : IsProbabilityMeasure L.pointDraw := L.point_probability
  let : IsProbabilityMeasure L.uniformDraw := L.uniform_probability
  let instructionProbability (c₀ : ℕ) (Γ₀ : Ctx) (τ₀ : Ty) (a : Instr c₀ Γ₀ τ₀) :
      IsProbabilityMeasure (instrLaw L a) := instrLaw_probability L a
  let tapeProbability (c₀ : ℕ) (Γ₀ : Ctx) (τ₀ : Ty) (q : Prog c₀ Γ₀ τ₀) :
      IsProbabilityMeasure (tapeLaw L q) := tapeLaw_probability L q
  let residualProbability (c₀ : ℕ) (Γ₀ : Ctx) (τ₀ : Ty) (q : Prog c₀ Γ₀ τ₀) :
      IsProbabilityMeasure (residualLaw L.uniformDraw q) :=
    residualLaw_probability L.uniformDraw q
  let : MeasurableSpace (Tape d (replayBody p e)) := tapeSpace d _
  let : MeasurableSpace (ResidualTape p) := residualSpace p
  let : ∀ j : Fin n, MeasurableSpace (Tape d (rawDraw (c := n*n+c) (origin j))) := fun j => tapeSpace d _
  let : ∀ j : Fin n, MeasurableSpace (Tape d (transformRow c n j)) := fun j => tapeSpace d _
  let : ∀ j : Fin n, IsProbabilityMeasure (tapeLaw L (transformRow c n j)) :=
    fun j => tapeLaw_probability L _
  let : ∀ _ : Fin n, SigmaFinite L.pointDraw := fun _ => inferInstance
  have hraw : MeasurePreserving
      (fun z : ∀ j : Fin n, Tape d (rawDraw (c := n*n+c) (origin j)) => fun j => (z j).1)
      (Measure.pi fun j => tapeLaw L (rawDraw (c := n*n+c) (origin j)))
      (Measure.pi fun _ : Fin n => L.pointDraw) :=
    measurePreserving_pi _ (fun _ : Fin n => L.pointDraw) (fun _ => dropRight _ _)
  have hr := restoreReplay_preserving L (Fin.natAdd (n*n)) p (fun a => nomatch a)
    (fun s => batchRef (e s)) (compiledCenter n) (compiledMomentum n)
  have hrows := dropLeft (Measure.pi fun j : Fin n => tapeLaw L (transformRow c n j))
    (tapeLaw L (replayBody p e))
  have hzero := dropLeft (Measure.dirac PUnit.unit)
    ((Measure.pi fun j : Fin n => tapeLaw L (transformRow c n j)).prod
      (tapeLaw L (replayBody p e)))
  have hbody := hraw.prod (hr.comp (hrows.comp hzero))
  -- The two outer input-unit factors are literal compileWith constructors.
  let tail := Prog.step [] Instr.momentum
    (Prog.batch [] (fun j => rawDraw (c := n*n+c) (origin j))
      (Prog.step [] (Instr.pure Pure.zero) (Prog.batch [] (transformRow c n) (replayBody p e))))
  let : IsProbabilityMeasure (tapeLaw L tail) := tapeLaw_probability L tail
  exact hbody.comp ((dropLeft _ _).comp (dropLeft _ (tapeLaw L tail)))

/-- Canonical source-seed measure, with no claim that pointDraw is Gaussian. -/
def sourceSeedLaw (L : PrimitiveLaws d) (p : Program c .point)
    (n : ℕ) : @Measure (Point d × ((Fin n → Point d) × ResidualTape p))
      ((inferInstance : MeasurableSpace (Point d)).prod
        ((inferInstance : MeasurableSpace (Fin n → Point d)).prod (residualSpace p))) :=
  let : MeasurableSpace (ResidualTape p) := residualSpace p
  L.pointDraw.prod ((Measure.pi fun _ : Fin n => L.pointDraw).prod
    (residualLaw L.uniformDraw p))

/-- Exact induced freshChild marginal equals the canonical ORIGINAL seed law.
This is a theorem conclusion, not a replacement definition of the induced law. -/
theorem freshChildSeed_preserving (L : PrimitiveLaws d) (p : Program c .point)
    (e : GaussianSlot p ≃ Fin n) (κ : Fin (n*n+c) → Fin c')
    (old : Ref Δ .point) (designated : Origin) (auxiliary : Fin n → Origin) :
    let : MeasurableSpace (Tape d (freshChild p e κ old designated auxiliary)) := tapeSpace d _
    let : MeasurableSpace (ResidualTape p) := residualSpace p
    MeasurePreserving (freshChildTapeEquiv (d := d) p e κ old designated auxiliary)
      (tapeLaw L (freshChild p e κ old designated auxiliary)) (sourceSeedLaw L p n) := by
  dsimp only
  let tapeMeasurable (c₀ : ℕ) (Γ₀ : Ctx) (τ₀ : Ty) (q : Prog c₀ Γ₀ τ₀) :
      MeasurableSpace (Tape d q) := tapeSpace d q
  let residualMeasurable (c₀ : ℕ) (Γ₀ : Ctx) (τ₀ : Ty) (q : Prog c₀ Γ₀ τ₀) :
      MeasurableSpace (ResidualTape q) := residualSpace q
  let instructionMeasurable (c₀ : ℕ) (Γ₀ : Ctx) (τ₀ : Ty) (a : Instr c₀ Γ₀ τ₀) :
      MeasurableSpace (Instr.Tape d a) := instrSpace d a
  let : IsProbabilityMeasure L.pointDraw := L.point_probability
  let : IsProbabilityMeasure L.uniformDraw := L.uniform_probability
  let instructionProbability (c₀ : ℕ) (Γ₀ : Ctx) (τ₀ : Ty) (a : Instr c₀ Γ₀ τ₀) :
      IsProbabilityMeasure (instrLaw L a) := instrLaw_probability L a
  let tapeProbability (c₀ : ℕ) (Γ₀ : Ctx) (τ₀ : Ty) (q : Prog c₀ Γ₀ τ₀) :
      IsProbabilityMeasure (tapeLaw L q) := tapeLaw_probability L q
  let residualProbability (c₀ : ℕ) (Γ₀ : Ctx) (τ₀ : Ty) (q : Prog c₀ Γ₀ τ₀) :
      IsProbabilityMeasure (residualLaw L.uniformDraw q) :=
    residualLaw_probability L.uniformDraw q
  let : MeasurableSpace (Tape d (compileWith p e auxiliary)) := tapeSpace d _
  let : MeasurableSpace (ResidualTape p) := residualSpace p
  exact (MeasurePreserving.id L.pointDraw).prod
    ((compiledSeed_preserving L p e auxiliary).comp
      (restoreTape_preserving L κ (compileWith p e auxiliary)
        (fun a => nomatch a) (.there old) .here))

/-- Fixed deterministic childRoot is an allowed T, even singular. It transforms
only Z and keeps the SAME V and full original residual in transformedSourceTape.
The RHS is a pushforward of the now-identified canonical seed, not a Gaussian
covariance claim or an accuracy conclusion. -/
theorem transformed_freshChild_law (L : PrimitiveLaws d) (p : Program c .point)
    (e : GaussianSlot p ≃ Fin n) (κ : Fin (n*n+c) → Fin c')
    (old : Ref Δ .point) (designated : Origin) (auxiliary : Fin n → Origin)
    (T : Fin n → Fin n → ℝ) :
    let : MeasurableSpace (Tape d (freshChild p e κ old designated auxiliary)) := tapeSpace d _
    let : MeasurableSpace (ResidualTape p) := residualSpace p
    let : MeasurableSpace (Tape d p) := tapeSpace d p
    (tapeLaw L (freshChild p e κ old designated auxiliary)).map
      (transformedSeed (d := d) p e T ∘ freshChildTapeEquiv p e κ old designated auxiliary) =
    (sourceSeedLaw L p n).map (transformedSeed (d := d) p e T) := by
  dsimp only
  let : MeasurableSpace (ResidualTape p) := residualSpace p
  let : MeasurableSpace (Tape d p) := tapeSpace d p
  let : MeasurableSpace (Tape d (freshChild p e κ old designated auxiliary)) := tapeSpace d _
  rw [← Measure.map_map (measurable_transformedSeed p e T)
    (measurable_freshChildSeed p e κ old designated auxiliary)]
  rw [(freshChildSeed_preserving L p e κ old designated auxiliary).map_eq]

/-- Exact fixed childRoot specialization; no PSD/covariance normalization used. -/
theorem childRoot_freshChild_law (L : PrimitiveLaws d) (p : Program c .point)
    (e : GaussianSlot p ≃ Fin n) (κ : Fin (n*n+c) → Fin c')
    (old : Ref Δ .point) (designated : Origin) (auxiliary : Fin n → Origin)
    (rho radius : ℝ) (shift : Fin n → ℝ) :
    let : MeasurableSpace (Tape d (freshChild p e κ old designated auxiliary)) := tapeSpace d _
    let : MeasurableSpace (ResidualTape p) := residualSpace p
    let : MeasurableSpace (Tape d p) := tapeSpace d p
    (tapeLaw L (freshChild p e κ old designated auxiliary)).map
      (transformedSeed (d := d) p e (CovarianceSetup.childRoot rho radius shift) ∘
        freshChildTapeEquiv p e κ old designated auxiliary) =
    (sourceSeedLaw L p n).map
      (transformedSeed (d := d) p e (CovarianceSetup.childRoot rho radius shift)) :=
  transformed_freshChild_law L p e κ old designated auxiliary
    (CovarianceSetup.childRoot rho radius shift)

end AcceleratedLogConcave.Oracle.FreshChildCanonicalSeedLaw
