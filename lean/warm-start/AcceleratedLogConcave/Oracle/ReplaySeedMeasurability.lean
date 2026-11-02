import AcceleratedLogConcave.Oracle.SamplingCanonicalTapeMeasurability
import AcceleratedLogConcave.Oracle.NoisyLayer

/-! Structural measurability of original replay seed extraction.
No law identification or independence is assumed/proved by this file. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.ReplaySeedMeasurability
open AffineLowering TapeLowering NoisyLayer OperationalMeasurability CanonicalTapeMeasurability
variable {α : Type*} [MeasurableSpace α] {c c' d : ℕ} {Γ Δ : Ctx} {τ : Ty}

theorem restoreTape_path (κ : Fin c → Fin c') (p : Prog c Γ τ) :
    ∀ {Δ : Ctx} (f : RefMap Γ Δ) (center momentum : Ref Δ .point)
      (ω : α → Tape d (p.lower κ f center momentum)),
      TapePathMeasurable (p.lower κ f center momentum) ω →
      TapePathMeasurable p (fun a => restoreTape κ p f center momentum (ω a)) := by
  induction p with
  | ret r => intro Δ f center momentum ω h; trivial
  | step o a next ih =>
    intro Δ f center momentum ω h
    cases a with
    | center => exact ⟨trivial, ih _ _ _ ω h⟩
    | momentum => exact ⟨trivial, ih _ _ _ ω h⟩
    | pure a => exact ⟨trivial, ih _ _ _ (fun z => (ω z).2) h.2⟩
    | grad r => exact ⟨trivial, ih _ _ _ (fun z => (ω z).2) h.2⟩
    | gaussian => exact ⟨h.1, ih _ _ _ (fun z => (ω z).2) h.2⟩
    | uniform => exact ⟨h.1, ih _ _ _ (fun z => (ω z).2) h.2⟩
  | batch o children next ihChildren ihNext =>
    intro Δ f center momentum ω h
    exact ⟨fun i => ihChildren i _ _ _ (fun z => (ω z).1 i) (h.1 i),
      ihNext _ _ _ (fun z => (ω z).2) h.2⟩

theorem restoreReplay_path (κ : Fin c → Fin c') (p : Prog c Γ τ) :
    ∀ {Δ : Ctx} (f : RefMap Γ Δ) (slots : GaussianSlot p → Ref Δ .point)
      (center momentum : Ref Δ .point)
      (ω : α → Tape d (replayGaussian κ p f slots center momentum)),
      TapePathMeasurable (replayGaussian κ p f slots center momentum) ω →
      ResidualPathMeasurable p
        (fun a => restoreReplayTape κ p f slots center momentum (ω a)) := by
  induction p with
  | ret r => intro Δ f slots center momentum ω h; trivial
  | step o a next ih =>
    intro Δ f slots center momentum ω h
    cases a with
    | center => exact ⟨trivial, ih _ _ _ _ ω h⟩
    | momentum => exact ⟨trivial, ih _ _ _ _ ω h⟩
    | gaussian => exact ⟨trivial, ih _ _ _ _ ω h⟩
    | pure a => exact ⟨trivial, ih _ _ _ _ (fun z => (ω z).2) h.2⟩
    | grad r => exact ⟨trivial, ih _ _ _ _ (fun z => (ω z).2) h.2⟩
    | uniform => exact ⟨h.1, ih _ _ _ _ (fun z => (ω z).2) h.2⟩
  | batch o children next ihChildren ihNext =>
    intro Δ f slots center momentum ω h
    exact ⟨fun i => ihChildren i _ _ _ _ (fun z => (ω z).1 i) (h.1 i),
      ihNext _ _ _ _ (fun z => (ω z).2) h.2⟩

/-- Measurability into the ORIGINAL source residual carrier, with all uniform
coordinates varying. Uses actual replay, not an independent residual copy. -/
theorem measurable_restoreReplay (κ : Fin c → Fin c') (p : Prog c Γ τ)
    (f : RefMap Γ Δ) (slots : GaussianSlot p → Ref Δ .point)
    (center momentum : Ref Δ .point) :
    @Measurable (Tape d (replayGaussian κ p f slots center momentum)) (ResidualTape p)
      (tapeSpace d _) (residualSpace p) (restoreReplayTape κ p f slots center momentum) := by
  let : MeasurableSpace (Tape d (replayGaussian κ p f slots center momentum)) := tapeSpace d _
  exact (measurable_iff_residualPath p _).mpr
    (restoreReplay_path κ p f slots center momentum id
      ((measurable_iff_tapePath _ _).mp measurable_id))



theorem measurable_restoreTape (κ : Fin c → Fin c') (p : Prog c Γ τ)
    (f : RefMap Γ Δ) (center momentum : Ref Δ .point) :
    @Measurable (Tape d (p.lower κ f center momentum)) (Tape d p)
      (tapeSpace d _) (tapeSpace d p) (restoreTape κ p f center momentum) := by
  let : MeasurableSpace (Tape d (p.lower κ f center momentum)) := tapeSpace d _
  exact (measurable_iff_tapePath p _).mpr
    (restoreTape_path κ p f center momentum id
      ((measurable_iff_tapePath _ _).mp measurable_id))

theorem measurable_compiledSeed {n : ℕ} (p : Program c τ)
    (e : GaussianSlot p ≃ Fin n) (origin : Fin n → Origin) :
    let : MeasurableSpace (Tape d (compileWith p e origin)) := tapeSpace d _
    let : MeasurableSpace (ResidualTape p) := residualSpace p
    Measurable (compiledTapeEquivWith (d := d) p e origin) := by
  let : MeasurableSpace (Tape d (compileWith p e origin)) := tapeSpace d _
  let : MeasurableSpace (ResidualTape p) := residualSpace p
  have h := (measurable_iff_tapePath (d := d) (compileWith p e origin) id).mp measurable_id
  have hz : ∀ j, Measurable (fun ω : Tape d (compileWith p e origin) => (show Point d from (ω.2.2.1 j).1)) :=
    fun j => (h.2.2.1 j).1
  have hr := restoreReplay_path (Fin.natAdd (n*n)) p (fun a => nomatch a)
    (fun s => batchRef (e s)) (compiledCenter n) (compiledMomentum n)
    (fun ω : Tape d (compileWith p e origin) => ω.2.2.2.2.2) h.2.2.2.2.2
  exact (measurable_pi_iff.mpr hz).prodMk ((measurable_iff_residualPath p _).mpr hr)

/-- Literal V,Z,R extraction; no freshening and no minimality claim. -/
theorem measurable_freshChildSeed {n : ℕ} (p : Program c .point)
    (e : GaussianSlot p ≃ Fin n) (κ : Fin (n*n+c) → Fin c')
    (old : Ref Δ .point) (designated : Origin) (auxiliary : Fin n → Origin) :
    let : MeasurableSpace (Tape d (freshChild p e κ old designated auxiliary)) := tapeSpace d _
    let : MeasurableSpace (ResidualTape p) := residualSpace p
    Measurable (freshChildTapeEquiv (d := d) p e κ old designated auxiliary) := by
  let : MeasurableSpace (Tape d (freshChild p e κ old designated auxiliary)) := tapeSpace d _
  let : MeasurableSpace (ResidualTape p) := residualSpace p
  let : MeasurableSpace (Tape d (compileWith p e auxiliary)) := tapeSpace d _
  let : MeasurableSpace (Tape d ((compileWith p e auxiliary).lower κ
      (fun a => nomatch a) (.there old) .here)) := tapeSpace d _
  exact measurable_fst.prodMk ((measurable_compiledSeed p e auxiliary).comp
    ((measurable_restoreTape κ (compileWith p e auxiliary)
      (fun a => nomatch a) (.there old) .here).comp measurable_snd))

/-- The source transform keeps designated momentum and the COMPLETE original
residual. Singular T is allowed; covariance identification is separate. -/
def transformedSeed {n : ℕ} (p : Program c .point) (e : GaussianSlot p ≃ Fin n)
    (T : Fin n → Fin n → ℝ)
    (z : Point d × ((Fin n → Point d) × ResidualTape p)) : Point d × Tape d p :=
  (z.1, transformedSourceTape p e T z.2.1 z.2.2)

theorem measurable_transformedSeed {n : ℕ} (p : Program c .point)
    (e : GaussianSlot p ≃ Fin n) (T : Fin n → Fin n → ℝ) :
    let : MeasurableSpace (ResidualTape p) := residualSpace p
    let : MeasurableSpace (Tape d p) := tapeSpace d p
    Measurable (transformedSeed (d := d) p e T) := by
  let : MeasurableSpace (ResidualTape p) := residualSpace p
  let : MeasurableSpace (Tape d p) := tapeSpace d p
  have hz : Measurable (fun z : Point d × ((Fin n → Point d) × ResidualTape p) =>
      fun s : GaussianSlot p => transformedGaussian T z.2.1 (e s)) := by
    apply measurable_pi_iff.mpr
    intro s
    unfold transformedGaussian
    exact Finset.measurable_sum _ (fun j _ => by fun_prop)
  exact measurable_fst.prodMk ((measurable_joinTape d p).comp
    (hz.prodMk measurable_snd.snd))

end AcceleratedLogConcave.Oracle.ReplaySeedMeasurability
