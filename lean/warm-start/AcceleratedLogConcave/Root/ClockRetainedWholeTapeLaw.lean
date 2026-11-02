import AcceleratedLogConcave.Root.ClockRetainedTapeLaw

/-! Probability coordinates for the hand-packed retained-final tape. The
assembly and center-initialization arrays are actual fresh syntax draws. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Root.ClockRetainedWholeTapeLaw
open MeasureTheory ProbabilityTheory
open Oracle Oracle.CanonicalTapeMeasurability Oracle.CanonicalTapeLaw
open ClockRetainedFinalSplice
open ClockNoisyLayer

variable (P : SourceSchedule) (hR : P.R ≤ 1 / 2) (hc : 0 < P.csch)
  (hsmall : P.csch < 1 / 160) (clock : ClockLaw.Clock)
  {d : ℕ} (ell : ℕ)

theorem measurable_assembly_toFun :
    let : MeasurableSpace (Tape d (assembled P hR hc hsmall clock ell)) :=
      tapeSpace d (assembled P hR hc hsmall clock ell)
    let : MeasurableSpace (Tape d (initialized P hR hc hsmall clock ell)) :=
      tapeSpace d (initialized P hR hc hsmall clock ell)
    Measurable (assemblyTapeEquiv P hR hc hsmall clock d ell) := by
  let : MeasurableSpace (Tape d (assembled P hR hc hsmall clock ell)) :=
    tapeSpace d (assembled P hR hc hsmall clock ell)
  let : MeasurableSpace (Tape d (initialized P hR hc hsmall clock ell)) :=
    tapeSpace d (initialized P hR hc hsmall clock ell)
  let : ∀ i, MeasurableSpace (Tape d
      (Oracle.NoisyLayer.residualDraw
        (c := size P hR hc hsmall clock) (Γ := ClockPublicSetup.readyCtx P)
        (assemblyOrigin P ell i))) :=
    fun i => tapeSpace d _
  let : MeasurableSpace (Instr.Tape d
      (Instr.gaussian : Instr (size P hR hc hsmall clock)
        (ClockPublicSetup.readyCtx P) .point)) := instrSpace d .gaussian
  let : ∀ i, MeasurableSpace (Tape d
      (Oracle.MeanGaussianSetup.row (assemblySlot P hR hc hsmall clock)
        (ClockPublicSetup.saved P ClockPublicSetup.hRef) i)) :=
    fun i => tapeSpace d _
  have hdraw (i : Index P) : Measurable
      (fun tape : Tape d (assembled P hR hc hsmall clock ell) => (tape.1 i).1) :=
    ((measurable_pi_apply i).comp measurable_fst).fst
  have hdraws : Measurable
      (fun tape : Tape d (assembled P hR hc hsmall clock ell) =>
        fun i : Index P => (tape.1 i).1) := measurable_pi_iff.mpr hdraw
  exact hdraws.prodMk (measurable_snd.comp measurable_snd)

theorem measurable_assembly_invFun :
    let : MeasurableSpace (Tape d (initialized P hR hc hsmall clock ell)) :=
      tapeSpace d (initialized P hR hc hsmall clock ell)
    let : MeasurableSpace (Tape d (assembled P hR hc hsmall clock ell)) :=
      tapeSpace d (assembled P hR hc hsmall clock ell)
    Measurable (assemblyTapeEquiv P hR hc hsmall clock d ell).symm := by
  let : MeasurableSpace (Tape d (initialized P hR hc hsmall clock ell)) :=
    tapeSpace d (initialized P hR hc hsmall clock ell)
  let : MeasurableSpace (Tape d (assembled P hR hc hsmall clock ell)) :=
    tapeSpace d (assembled P hR hc hsmall clock ell)
  let : ∀ i, MeasurableSpace (Tape d
      (Oracle.NoisyLayer.residualDraw
        (c := size P hR hc hsmall clock) (Γ := ClockPublicSetup.readyCtx P)
        (assemblyOrigin P ell i))) :=
    fun i => tapeSpace d _
  let : ∀ i, MeasurableSpace (Tape d
      (Oracle.MeanGaussianSetup.row (assemblySlot P hR hc hsmall clock)
        (ClockPublicSetup.saved P ClockPublicSetup.hRef) i)) :=
    fun i => tapeSpace d _
  exact (measurable_pi_iff.mpr fun i =>
    ((measurable_pi_apply i).comp measurable_fst).prodMk measurable_const).prodMk
      (measurable_const.prodMk measurable_snd)

def assemblyMeasurableEquiv :
    let : MeasurableSpace (Tape d (assembled P hR hc hsmall clock ell)) :=
      tapeSpace d (assembled P hR hc hsmall clock ell)
    let : MeasurableSpace (Tape d (initialized P hR hc hsmall clock ell)) :=
      tapeSpace d (initialized P hR hc hsmall clock ell)
    Tape d (assembled P hR hc hsmall clock ell) ≃ᵐ
      ((Index P → Point d) × Tape d (initialized P hR hc hsmall clock ell)) := by
  let : MeasurableSpace (Tape d (assembled P hR hc hsmall clock ell)) :=
    tapeSpace d (assembled P hR hc hsmall clock ell)
  let : MeasurableSpace (Tape d (initialized P hR hc hsmall clock ell)) :=
    tapeSpace d (initialized P hR hc hsmall clock ell)
  exact { assemblyTapeEquiv P hR hc hsmall clock d ell with
    measurable_toFun := measurable_assembly_toFun P hR hc hsmall clock ell
    measurable_invFun := measurable_assembly_invFun P hR hc hsmall clock ell }

/-- The raw assembly array is independent of its complete continuation. -/
theorem map_assembly (L : PrimitiveLaws d) :
    let : MeasurableSpace (Tape d (assembled P hR hc hsmall clock ell)) :=
      tapeSpace d (assembled P hR hc hsmall clock ell)
    let : MeasurableSpace (Tape d (initialized P hR hc hsmall clock ell)) :=
      tapeSpace d (initialized P hR hc hsmall clock ell)
    (tapeLaw L (assembled P hR hc hsmall clock ell)).map
      (assemblyMeasurableEquiv P hR hc hsmall clock ell) =
        (Measure.pi fun _ : Index P => L.pointDraw).prod
          (tapeLaw L (initialized P hR hc hsmall clock ell)) := by
  let : MeasurableSpace (Tape d (assembled P hR hc hsmall clock ell)) :=
    tapeSpace d (assembled P hR hc hsmall clock ell)
  let : MeasurableSpace (Tape d (initialized P hR hc hsmall clock ell)) :=
    tapeSpace d (initialized P hR hc hsmall clock ell)
  let : ∀ i, MeasurableSpace (Tape d
      (Oracle.NoisyLayer.residualDraw
        (c := size P hR hc hsmall clock) (Γ := ClockPublicSetup.readyCtx P)
        (assemblyOrigin P ell i))) := fun i => tapeSpace d _
  let : ∀ i, MeasurableSpace (Tape d
      (Oracle.MeanGaussianSetup.row (assemblySlot P hR hc hsmall clock)
        (ClockPublicSetup.saved P ClockPublicSetup.hRef) i)) := fun i => tapeSpace d _
  let : IsProbabilityMeasure L.pointDraw := L.point_probability
  let : ∀ i, IsProbabilityMeasure (tapeLaw L
      (Oracle.NoisyLayer.residualDraw (c := size P hR hc hsmall clock)
        (Γ := ClockPublicSetup.readyCtx P) (assemblyOrigin P ell i))) :=
    fun i => tapeLaw_probability L _
  let : IsProbabilityMeasure
      (tapeLaw L (initialized P hR hc hsmall clock ell)) := tapeLaw_probability L _
  let : ∀ i, IsProbabilityMeasure (tapeLaw L
      (Oracle.MeanGaussianSetup.row (assemblySlot P hR hc hsmall clock)
        (ClockPublicSetup.saved P ClockPublicSetup.hRef) i)) :=
    fun i => tapeLaw_probability L _
  let : MeasurableSpace (Instr.Tape d
      (Instr.gaussian : Instr (size P hR hc hsmall clock)
        (ClockPublicSetup.readyCtx P) .point)) := instrSpace d .gaussian
  have hd (i : Index P) : MeasurePreserving
      (fun ω : Tape d (Oracle.NoisyLayer.residualDraw
        (c := size P hR hc hsmall clock) (Γ := ClockPublicSetup.readyCtx P)
        (assemblyOrigin P ell i)) => ω.1)
      (tapeLaw L (Oracle.NoisyLayer.residualDraw (c := size P hR hc hsmall clock)
        (Γ := ClockPublicSetup.readyCtx P) (assemblyOrigin P ell i))) L.pointDraw := by
    change MeasurePreserving Prod.fst
      (L.pointDraw.prod (Measure.dirac (α := PUnit) PUnit.unit)) L.pointDraw
    exact measurePreserving_fst
  have hdraw := measurePreserving_pi
    (fun i : Index P => tapeLaw L (Oracle.NoisyLayer.residualDraw
      (c := size P hR hc hsmall clock) (Γ := ClockPublicSetup.readyCtx P)
      (assemblyOrigin P ell i)))
    (fun _ : Index P => L.pointDraw) hd
  have htail := measurePreserving_snd
    (μ := Measure.pi (fun i : Index P => tapeLaw L
      (Oracle.MeanGaussianSetup.row (assemblySlot P hR hc hsmall clock)
        (ClockPublicSetup.saved P ClockPublicSetup.hRef) i)))
    (ν := tapeLaw L (initialized P hR hc hsmall clock ell))
  exact (hdraw.prod htail).map_eq

private def initialStructuralTapeEquiv :
    Tape d (initialized P hR hc hsmall clock ell) ≃
      ((Index P → Point d) × Tape d (loop P hR hc hsmall clock ell)) :=
  Oracle.NoisyLayer.initialTapeEquiv
    (oldSlot P hR hc hsmall clock
      (ClockRepeatedLayers.rhoSlot P hR hc hsmall clock))
    (fun i => assemblySaved P (ClockPublicSetup.directRef P i)) []
    (ClockInitialLayer.initialOrigin P ell) (loop P hR hc hsmall clock ell)

theorem measurable_initial_toFun :
    let : MeasurableSpace (Tape d (initialized P hR hc hsmall clock ell)) :=
      tapeSpace d (initialized P hR hc hsmall clock ell)
    let : MeasurableSpace (Tape d (loop P hR hc hsmall clock ell)) :=
      tapeSpace d (loop P hR hc hsmall clock ell)
    Measurable (initialStructuralTapeEquiv P hR hc hsmall clock ell (d := d)) := by
  let : MeasurableSpace (Tape d (initialized P hR hc hsmall clock ell)) :=
    tapeSpace d (initialized P hR hc hsmall clock ell)
  let : MeasurableSpace (Tape d (loop P hR hc hsmall clock ell)) :=
    tapeSpace d (loop P hR hc hsmall clock ell)
  let : ∀ i, MeasurableSpace (Tape d
      (Oracle.NoisyLayer.residualDraw (c := size P hR hc hsmall clock)
        (Γ := assembledCtx P) (ClockInitialLayer.initialOrigin P ell i))) :=
    fun i => tapeSpace d _
  let : MeasurableSpace (Instr.Tape d
      (Instr.gaussian : Instr (size P hR hc hsmall clock) (assembledCtx P) .point)) :=
    instrSpace d .gaussian
  let : ∀ i, MeasurableSpace (Tape d (Oracle.NoisyLayer.initialRow
      (oldSlot P hR hc hsmall clock
        (ClockRepeatedLayers.rhoSlot P hR hc hsmall clock))
      (fun j => assemblySaved P (ClockPublicSetup.directRef P j)) i)) :=
    fun i => tapeSpace d _
  have hdraw (i : Index P) : Measurable
      (fun tape : Tape d (initialized P hR hc hsmall clock ell) => (tape.1 i).1) :=
    ((measurable_pi_apply i).comp measurable_fst).fst
  have hdraws : Measurable
      (fun tape : Tape d (initialized P hR hc hsmall clock ell) =>
        fun i : Index P => (tape.1 i).1) := measurable_pi_iff.mpr hdraw
  exact hdraws.prodMk (measurable_snd.comp measurable_snd)

theorem measurable_initial_invFun :
    let : MeasurableSpace (Tape d (loop P hR hc hsmall clock ell)) :=
      tapeSpace d (loop P hR hc hsmall clock ell)
    let : MeasurableSpace (Tape d (initialized P hR hc hsmall clock ell)) :=
      tapeSpace d (initialized P hR hc hsmall clock ell)
    Measurable (initialStructuralTapeEquiv P hR hc hsmall clock ell (d := d)).symm := by
  let : MeasurableSpace (Tape d (loop P hR hc hsmall clock ell)) :=
    tapeSpace d (loop P hR hc hsmall clock ell)
  let : MeasurableSpace (Tape d (initialized P hR hc hsmall clock ell)) :=
    tapeSpace d (initialized P hR hc hsmall clock ell)
  let : ∀ i, MeasurableSpace (Tape d
      (Oracle.NoisyLayer.residualDraw (c := size P hR hc hsmall clock)
        (Γ := assembledCtx P) (ClockInitialLayer.initialOrigin P ell i))) :=
    fun i => tapeSpace d _
  let : ∀ i, MeasurableSpace (Tape d (Oracle.NoisyLayer.initialRow
      (oldSlot P hR hc hsmall clock
        (ClockRepeatedLayers.rhoSlot P hR hc hsmall clock))
      (fun j => assemblySaved P (ClockPublicSetup.directRef P j)) i)) :=
    fun i => tapeSpace d _
  exact (measurable_pi_iff.mpr fun i =>
    ((measurable_pi_apply i).comp measurable_fst).prodMk measurable_const).prodMk
      (measurable_const.prodMk measurable_snd)

def initialMeasurableEquiv :
    let : MeasurableSpace (Tape d (initialized P hR hc hsmall clock ell)) :=
      tapeSpace d (initialized P hR hc hsmall clock ell)
    let : MeasurableSpace (Tape d (loop P hR hc hsmall clock ell)) :=
      tapeSpace d (loop P hR hc hsmall clock ell)
    Tape d (initialized P hR hc hsmall clock ell) ≃ᵐ
      ((Index P → Point d) × Tape d (loop P hR hc hsmall clock ell)) := by
  let : MeasurableSpace (Tape d (initialized P hR hc hsmall clock ell)) :=
    tapeSpace d (initialized P hR hc hsmall clock ell)
  let : MeasurableSpace (Tape d (loop P hR hc hsmall clock ell)) :=
    tapeSpace d (loop P hR hc hsmall clock ell)
  exact { initialStructuralTapeEquiv P hR hc hsmall clock ell (d := d) with
    measurable_toFun := measurable_initial_toFun P hR hc hsmall clock ell
    measurable_invFun := measurable_initial_invFun P hR hc hsmall clock ell }

/-- Separate initial-center draws, with the entire repeated-layer tape kept. -/
theorem map_initial (L : PrimitiveLaws d) :
    let : MeasurableSpace (Tape d (initialized P hR hc hsmall clock ell)) :=
      tapeSpace d (initialized P hR hc hsmall clock ell)
    let : MeasurableSpace (Tape d (loop P hR hc hsmall clock ell)) :=
      tapeSpace d (loop P hR hc hsmall clock ell)
    (tapeLaw L (initialized P hR hc hsmall clock ell)).map
      (initialMeasurableEquiv P hR hc hsmall clock ell) =
        (Measure.pi fun _ : Index P => L.pointDraw).prod
          (tapeLaw L (loop P hR hc hsmall clock ell)) := by
  let : MeasurableSpace (Tape d (initialized P hR hc hsmall clock ell)) :=
    tapeSpace d (initialized P hR hc hsmall clock ell)
  let : MeasurableSpace (Tape d (loop P hR hc hsmall clock ell)) :=
    tapeSpace d (loop P hR hc hsmall clock ell)
  let : ∀ i, MeasurableSpace (Tape d
      (Oracle.NoisyLayer.residualDraw (c := size P hR hc hsmall clock)
        (Γ := assembledCtx P) (ClockInitialLayer.initialOrigin P ell i))) :=
    fun i => tapeSpace d _
  let : ∀ i, MeasurableSpace (Tape d (Oracle.NoisyLayer.initialRow
      (oldSlot P hR hc hsmall clock
        (ClockRepeatedLayers.rhoSlot P hR hc hsmall clock))
      (fun j => assemblySaved P (ClockPublicSetup.directRef P j)) i)) :=
    fun i => tapeSpace d _
  let : MeasurableSpace (Instr.Tape d
      (Instr.gaussian : Instr (size P hR hc hsmall clock) (assembledCtx P) .point)) :=
    instrSpace d .gaussian
  let : IsProbabilityMeasure L.pointDraw := L.point_probability
  let : ∀ i, IsProbabilityMeasure (tapeLaw L
      (Oracle.NoisyLayer.residualDraw (c := size P hR hc hsmall clock)
        (Γ := assembledCtx P) (ClockInitialLayer.initialOrigin P ell i))) :=
    fun i => tapeLaw_probability L _
  let : ∀ i, IsProbabilityMeasure (tapeLaw L (Oracle.NoisyLayer.initialRow
      (oldSlot P hR hc hsmall clock
        (ClockRepeatedLayers.rhoSlot P hR hc hsmall clock))
      (fun j => assemblySaved P (ClockPublicSetup.directRef P j)) i)) :=
    fun i => tapeLaw_probability L _
  let : IsProbabilityMeasure (tapeLaw L (loop P hR hc hsmall clock ell)) :=
    tapeLaw_probability L _
  have hd (i : Index P) : MeasurePreserving
      (fun ω : Tape d (Oracle.NoisyLayer.residualDraw
        (c := size P hR hc hsmall clock) (Γ := assembledCtx P)
        (ClockInitialLayer.initialOrigin P ell i)) => ω.1)
      (tapeLaw L (Oracle.NoisyLayer.residualDraw (c := size P hR hc hsmall clock)
        (Γ := assembledCtx P) (ClockInitialLayer.initialOrigin P ell i))) L.pointDraw := by
    change MeasurePreserving Prod.fst
      (L.pointDraw.prod (Measure.dirac (α := PUnit) PUnit.unit)) L.pointDraw
    exact measurePreserving_fst
  have hdraw := measurePreserving_pi
    (fun i : Index P => tapeLaw L (Oracle.NoisyLayer.residualDraw
      (c := size P hR hc hsmall clock) (Γ := assembledCtx P)
      (ClockInitialLayer.initialOrigin P ell i)))
    (fun _ : Index P => L.pointDraw) hd
  have htail := measurePreserving_snd
    (μ := Measure.pi (fun i : Index P => tapeLaw L (Oracle.NoisyLayer.initialRow
      (oldSlot P hR hc hsmall clock
        (ClockRepeatedLayers.rhoSlot P hR hc hsmall clock))
      (fun j => assemblySaved P (ClockPublicSetup.directRef P j)) i)))
    (ν := tapeLaw L (loop P hR hc hsmall clock ell))
  exact (hdraw.prod htail).map_eq

/-- The mixed main/final payload receives precisely the measurable structure
transported from its actual, complete loop tape. This keeps every original
uniform and each final child residual while the outer Gaussian arrays are
factored independently. -/
@[instance_reducible] def mainFinalSpace : MeasurableSpace
    (MainFinalTapeData P hR hc hsmall clock d (P.K+4)) :=
  MeasurableSpace.comap
    (completeLoopTapeEquiv P hR hc hsmall clock d ell).symm
    (tapeSpace d (loop P hR hc hsmall clock ell))

def mainFinalMeasurableEquiv :
    let : MeasurableSpace (Tape d (loop P hR hc hsmall clock ell)) :=
      tapeSpace d (loop P hR hc hsmall clock ell)
    let : MeasurableSpace (MainFinalTapeData P hR hc hsmall clock d (P.K+4)) :=
      mainFinalSpace P hR hc hsmall clock ell
    Tape d (loop P hR hc hsmall clock ell) ≃ᵐ
      MainFinalTapeData P hR hc hsmall clock d (P.K+4) := by
  let : MeasurableSpace (Tape d (loop P hR hc hsmall clock ell)) :=
    tapeSpace d (loop P hR hc hsmall clock ell)
  let : MeasurableSpace (MainFinalTapeData P hR hc hsmall clock d (P.K+4)) :=
    mainFinalSpace P hR hc hsmall clock ell
  let e := completeLoopTapeEquiv P hR hc hsmall clock d ell
  have hinv : Measurable e.symm := comap_measurable e.symm
  have hforward : Measurable e := by
    intro s hs
    change @MeasurableSet _ (MeasurableSpace.comap e.symm
      (tapeSpace d (loop P hR hc hsmall clock ell))) s at hs
    rcases hs with ⟨t, ht, rfl⟩
    change @MeasurableSet _ (tapeSpace d (loop P hR hc hsmall clock ell))
      (e ⁻¹' (e.symm ⁻¹' t))
    have hset : e ⁻¹' (e.symm ⁻¹' t) = t := by
      ext x
      simp only [Set.mem_preimage, Equiv.symm_apply_apply]
    rw [hset]
    exact ht
  exact { e with measurable_toFun := hforward, measurable_invFun := hinv }

def mainFinalLaw : @Measure
    (MainFinalTapeData P hR hc hsmall clock d (P.K+4))
    (mainFinalSpace P hR hc hsmall clock ell) := by
  let : MeasurableSpace (Tape d (loop P hR hc hsmall clock ell)) :=
    tapeSpace d (loop P hR hc hsmall clock ell)
  let : MeasurableSpace (MainFinalTapeData P hR hc hsmall clock d (P.K+4)) :=
    mainFinalSpace P hR hc hsmall clock ell
  exact (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
    (loop P hR hc hsmall clock ell)).map
      (mainFinalMeasurableEquiv P hR hc hsmall clock ell)

/-- The exact `WholeTapeData` of the deterministic retained-final splice is
upgraded to a measurable equivalence. Its main/final payload is not erased. -/
def wholeTapeMeasurableEquiv :
    let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
      tapeSpace d (code P hR hc hsmall clock ell)
    let : MeasurableSpace (MainFinalTapeData P hR hc hsmall clock d (P.K+4)) :=
      mainFinalSpace P hR hc hsmall clock ell
    Tape d (code P hR hc hsmall clock ell) ≃ᵐ
      WholeTapeData P hR hc hsmall clock d := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
    tapeSpace d (code P hR hc hsmall clock ell)
  let : MeasurableSpace (Tape d (assembled P hR hc hsmall clock ell)) :=
    tapeSpace d (assembled P hR hc hsmall clock ell)
  let : MeasurableSpace (Tape d (initialized P hR hc hsmall clock ell)) :=
    tapeSpace d (initialized P hR hc hsmall clock ell)
  let : MeasurableSpace (Tape d (loop P hR hc hsmall clock ell)) :=
    tapeSpace d (loop P hR hc hsmall clock ell)
  let : MeasurableSpace (MainFinalTapeData P hR hc hsmall clock d (P.K+4)) :=
    mainFinalSpace P hR hc hsmall clock ell
  let e₀ := ClockRetainedTapeLaw.publicPrefixMeasurableEquiv
    P hR hc hsmall clock ell (d := d)
  let e₁ := (MeasurableEquiv.refl (Point d)).prodCongr
    (assemblyMeasurableEquiv P hR hc hsmall clock ell (d := d))
  let e₂ := (MeasurableEquiv.refl (Point d)).prodCongr
    ((MeasurableEquiv.refl (Index P → Point d)).prodCongr
      (initialMeasurableEquiv P hR hc hsmall clock ell (d := d)))
  let e₃ := (MeasurableEquiv.refl (Point d)).prodCongr
    ((MeasurableEquiv.refl (Index P → Point d)).prodCongr
      ((MeasurableEquiv.refl (Index P → Point d)).prodCongr
        (mainFinalMeasurableEquiv P hR hc hsmall clock ell (d := d))))
  exact e₀.trans (e₁.trans (e₂.trans e₃))

theorem wholeTapeMeasurableEquiv_toEquiv :
    let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
      tapeSpace d (code P hR hc hsmall clock ell)
    let : MeasurableSpace (MainFinalTapeData P hR hc hsmall clock d (P.K+4)) :=
      mainFinalSpace P hR hc hsmall clock ell
    (wholeTapeMeasurableEquiv P hR hc hsmall clock ell).toEquiv =
      wholeTapeEquiv P hR hc hsmall clock d ell := by
  rfl

/-- Explicit product on the actual hand-packed coordinates. The main/final
factor still contains all child residuals and uniforms, with its law inherited
from the full loop tape through the proved deterministic equivalence. -/
def wholeDataLaw : @Measure (WholeTapeData P hR hc hsmall clock d)
    (by
      let : MeasurableSpace (MainFinalTapeData P hR hc hsmall clock d (P.K+4)) :=
        mainFinalSpace P hR hc hsmall clock ell
      exact inferInstance) := by
  let : MeasurableSpace (MainFinalTapeData P hR hc hsmall clock d (P.K+4)) :=
    mainFinalSpace P hR hc hsmall clock ell
  exact (stdGaussian (Point d)).prod
    ((Measure.pi fun _ : Index P => stdGaussian (Point d)).prod
      ((Measure.pi fun _ : Index P => stdGaussian (Point d)).prod
        (mainFinalLaw P hR hc hsmall clock ell (d := d))))

theorem map_wholeTape :
    let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
      tapeSpace d (code P hR hc hsmall clock ell)
    let : MeasurableSpace (MainFinalTapeData P hR hc hsmall clock d (P.K+4)) :=
      mainFinalSpace P hR hc hsmall clock ell
    (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
      (code P hR hc hsmall clock ell)).map
        (wholeTapeMeasurableEquiv P hR hc hsmall clock ell) =
      wholeDataLaw P hR hc hsmall clock ell := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
    tapeSpace d (code P hR hc hsmall clock ell)
  let : MeasurableSpace (Tape d (assembled P hR hc hsmall clock ell)) :=
    tapeSpace d (assembled P hR hc hsmall clock ell)
  let : MeasurableSpace (Tape d (initialized P hR hc hsmall clock ell)) :=
    tapeSpace d (initialized P hR hc hsmall clock ell)
  let : MeasurableSpace (Tape d (loop P hR hc hsmall clock ell)) :=
    tapeSpace d (loop P hR hc hsmall clock ell)
  let : MeasurableSpace (MainFinalTapeData P hR hc hsmall clock d (P.K+4)) :=
    mainFinalSpace P hR hc hsmall clock ell
  let L := ClockPublicSetupTapeLaw.standardLaws d
  let μ := stdGaussian (Point d)
  let μZ := Measure.pi (fun _ : Index P => μ)
  let μloop := tapeLaw L (loop P hR hc hsmall clock ell)
  let μmain := mainFinalLaw P hR hc hsmall clock ell (d := d)
  let : IsProbabilityMeasure (tapeLaw L (assembled P hR hc hsmall clock ell)) :=
    tapeLaw_probability L _
  let : IsProbabilityMeasure (tapeLaw L (initialized P hR hc hsmall clock ell)) :=
    tapeLaw_probability L _
  let : IsProbabilityMeasure μloop := tapeLaw_probability L _
  let : IsProbabilityMeasure μ := L.point_probability
  let : IsProbabilityMeasure μZ := by infer_instance
  let : IsProbabilityMeasure μmain := by
    unfold μmain mainFinalLaw
    infer_instance
  let e₀ := ClockRetainedTapeLaw.publicPrefixMeasurableEquiv
    P hR hc hsmall clock ell (d := d)
  let e₁ := (MeasurableEquiv.refl (Point d)).prodCongr
    (assemblyMeasurableEquiv P hR hc hsmall clock ell (d := d))
  let e₂ := (MeasurableEquiv.refl (Point d)).prodCongr
    ((MeasurableEquiv.refl (Index P → Point d)).prodCongr
      (initialMeasurableEquiv P hR hc hsmall clock ell (d := d)))
  let e₃ := (MeasurableEquiv.refl (Point d)).prodCongr
    ((MeasurableEquiv.refl (Index P → Point d)).prodCongr
      ((MeasurableEquiv.refl (Index P → Point d)).prodCongr
        (mainFinalMeasurableEquiv P hR hc hsmall clock ell (d := d))))
  have hp : MeasurePreserving e₀
      (tapeLaw L (code P hR hc hsmall clock ell))
      (μ.prod (tapeLaw L (assembled P hR hc hsmall clock ell))) := by
    refine ⟨e₀.measurable, ?_⟩
    simpa only [L, μ, ClockPublicSetupTapeLaw.standardLaws] using
      (ClockRetainedTapeLaw.map_publicPrefix P hR hc hsmall clock ell L)
  have ha : MeasurePreserving
      (assemblyMeasurableEquiv P hR hc hsmall clock ell)
      (tapeLaw L (assembled P hR hc hsmall clock ell))
      (μZ.prod (tapeLaw L (initialized P hR hc hsmall clock ell))) := by
    refine ⟨(assemblyMeasurableEquiv P hR hc hsmall clock ell).measurable, ?_⟩
    simpa only [μZ, μ, L, ClockPublicSetupTapeLaw.standardLaws] using
      (map_assembly P hR hc hsmall clock ell L)
  have hi : MeasurePreserving
      (initialMeasurableEquiv P hR hc hsmall clock ell)
      (tapeLaw L (initialized P hR hc hsmall clock ell))
      (μZ.prod μloop) := by
    refine ⟨(initialMeasurableEquiv P hR hc hsmall clock ell).measurable, ?_⟩
    simpa only [μZ, μ, μloop, L, ClockPublicSetupTapeLaw.standardLaws] using
      (map_initial P hR hc hsmall clock ell L)
  have hl : MeasurePreserving
      (mainFinalMeasurableEquiv P hR hc hsmall clock ell)
      μloop μmain := by
    refine ⟨(mainFinalMeasurableEquiv P hR hc hsmall clock ell).measurable, ?_⟩
    rfl
  have h₁ := ((MeasurePreserving.id μ).prod ha).comp hp
  have h₂ := ((MeasurePreserving.id μ).prod
    ((MeasurePreserving.id μZ).prod hi)).comp h₁
  have h₃ := ((MeasurePreserving.id μ).prod
    ((MeasurePreserving.id μZ).prod
      ((MeasurePreserving.id μZ).prod hl))).comp h₂
  change Measure.map (e₀.trans (e₁.trans (e₂.trans e₃)))
    (tapeLaw L (code P hR hc hsmall clock ell)) =
      μ.prod (μZ.prod (μZ.prod μmain))
  exact h₃.map_eq

/-- The entering momentum stays as the original independent coordinate in
the law of the exact hand-packed tape. -/
theorem originalInputAndWholeTapeLaw :
    let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
      tapeSpace d (code P hR hc hsmall clock ell)
    let : MeasurableSpace (MainFinalTapeData P hR hc hsmall clock d (P.K+4)) :=
      mainFinalSpace P hR hc hsmall clock ell
    ((stdGaussian (Point d)).prod
      (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
        (code P hR hc hsmall clock ell))).map
      (Prod.map (id : Point d → Point d)
        (wholeTapeMeasurableEquiv P hR hc hsmall clock ell)) =
    (stdGaussian (Point d)).prod
      (wholeDataLaw P hR hc hsmall clock ell) := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
    tapeSpace d (code P hR hc hsmall clock ell)
  let : MeasurableSpace (MainFinalTapeData P hR hc hsmall clock d (P.K+4)) :=
    mainFinalSpace P hR hc hsmall clock ell
  let : IsProbabilityMeasure
      (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
        (code P hR hc hsmall clock ell)) :=
    tapeLaw_probability (ClockPublicSetupTapeLaw.standardLaws d) _
  have h : MeasurePreserving
      (wholeTapeMeasurableEquiv P hR hc hsmall clock ell)
      (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
        (code P hR hc hsmall clock ell))
      (wholeDataLaw P hR hc hsmall clock ell) :=
    ⟨(wholeTapeMeasurableEquiv P hR hc hsmall clock ell).measurable,
      map_wholeTape P hR hc hsmall clock ell⟩
  exact ((MeasurePreserving.id (stdGaussian (Point d))).prod h).map_eq

end AcceleratedLogConcave.Root.ClockRetainedWholeTapeLaw
