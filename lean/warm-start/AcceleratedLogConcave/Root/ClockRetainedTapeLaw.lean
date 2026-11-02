import AcceleratedLogConcave.Root.ClockRetainedFinalSplice
import AcceleratedLogConcave.Root.ClockPublicSetupTapeLaw
import AcceleratedLogConcave.Oracle.SamplingCanonicalSplitFactorization

/-! Measurable and law-level transport of the actual normalized retained-root
program tape. The first seam is the public E0 draw and complete continuation.
No child/reference kernel identification is used. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Root.ClockRetainedTapeLaw
open MeasureTheory ProbabilityTheory
open Oracle Oracle.CanonicalTapeMeasurability Oracle.CanonicalTapeLaw
open Oracle.CanonicalTapeFactorization Oracle.TapeLowering
open ClockRetainedFinalSplice

variable (P : SourceSchedule) (hR : P.R ≤ 1 / 2) (hc : 0 < P.csch)
  (hsmall : P.csch < 1 / 160) (clock : ClockLaw.Clock)
  {d : ℕ} (ell : ℕ)

theorem measurable_publicPrefix_toFun :
    let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
      tapeSpace d (code P hR hc hsmall clock ell)
    let : MeasurableSpace (Tape d (assembled P hR hc hsmall clock ell)) :=
      tapeSpace d (assembled P hR hc hsmall clock ell)
    Measurable (publicPrefixTapeEquiv P hR hc hsmall clock d ell) := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
    tapeSpace d (code P hR hc hsmall clock ell)
  let : MeasurableSpace (Tape d (assembled P hR hc hsmall clock ell)) :=
    tapeSpace d (assembled P hR hc hsmall clock ell)
  let : ∀ j, MeasurableSpace (Tape d (splitRow P hR hc hsmall clock j)) :=
    fun j => tapeSpace d (splitRow P hR hc hsmall clock j)
  let : ∀ i, MeasurableSpace (Tape d (publicDirectRow P hR hc hsmall clock i)) :=
    fun i => tapeSpace d (publicDirectRow P hR hc hsmall clock i)
  exact (measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk
    (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp measurable_snd))))

theorem measurable_publicPrefix_invFun :
    let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
      tapeSpace d (code P hR hc hsmall clock ell)
    let : MeasurableSpace (Tape d (assembled P hR hc hsmall clock ell)) :=
      tapeSpace d (assembled P hR hc hsmall clock ell)
    Measurable (publicPrefixTapeEquiv P hR hc hsmall clock d ell).symm := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
    tapeSpace d (code P hR hc hsmall clock ell)
  let : MeasurableSpace (Tape d (assembled P hR hc hsmall clock ell)) :=
    tapeSpace d (assembled P hR hc hsmall clock ell)
  let : ∀ j, MeasurableSpace (Tape d (splitRow P hR hc hsmall clock j)) :=
    fun j => tapeSpace d (splitRow P hR hc hsmall clock j)
  let : ∀ i, MeasurableSpace (Tape d (publicDirectRow P hR hc hsmall clock i)) :=
    fun i => tapeSpace d (publicDirectRow P hR hc hsmall clock i)
  exact measurable_const.prodMk (measurable_const.prodMk
    (measurable_fst.prodMk (measurable_const.prodMk
      (measurable_const.prodMk measurable_snd))))

def publicPrefixMeasurableEquiv :
    let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
      tapeSpace d (code P hR hc hsmall clock ell)
    let : MeasurableSpace (Tape d (assembled P hR hc hsmall clock ell)) :=
      tapeSpace d (assembled P hR hc hsmall clock ell)
    Tape d (code P hR hc hsmall clock ell) ≃ᵐ
      Point d × Tape d (assembled P hR hc hsmall clock ell) := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
    tapeSpace d (code P hR hc hsmall clock ell)
  let : MeasurableSpace (Tape d (assembled P hR hc hsmall clock ell)) :=
    tapeSpace d (assembled P hR hc hsmall clock ell)
  exact { publicPrefixTapeEquiv P hR hc hsmall clock d ell with
    measurable_toFun := measurable_publicPrefix_toFun P hR hc hsmall clock ell
    measurable_invFun := measurable_publicPrefix_invFun P hR hc hsmall clock ell }

theorem map_publicPrefix (L : PrimitiveLaws d) :
    let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
      tapeSpace d (code P hR hc hsmall clock ell)
    let : MeasurableSpace (Tape d (assembled P hR hc hsmall clock ell)) :=
      tapeSpace d (assembled P hR hc hsmall clock ell)
    (tapeLaw L (code P hR hc hsmall clock ell)).map
      (publicPrefixMeasurableEquiv P hR hc hsmall clock ell) =
        L.pointDraw.prod (tapeLaw L (assembled P hR hc hsmall clock ell)) := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
    tapeSpace d (code P hR hc hsmall clock ell)
  let : MeasurableSpace (Tape d (assembled P hR hc hsmall clock ell)) :=
    tapeSpace d (assembled P hR hc hsmall clock ell)
  let : ∀ j, MeasurableSpace (Tape d (splitRow P hR hc hsmall clock j)) :=
    fun j => tapeSpace d (splitRow P hR hc hsmall clock j)
  let : ∀ i, MeasurableSpace (Tape d (publicDirectRow P hR hc hsmall clock i)) :=
    fun i => tapeSpace d (publicDirectRow P hR hc hsmall clock i)
  let : ∀ j, IsProbabilityMeasure (tapeLaw L (splitRow P hR hc hsmall clock j)) :=
    fun j => tapeLaw_probability L _
  let : ∀ i, IsProbabilityMeasure (tapeLaw L (publicDirectRow P hR hc hsmall clock i)) :=
    fun i => tapeLaw_probability L _
  let : IsProbabilityMeasure (tapeLaw L (assembled P hR hc hsmall clock ell)) :=
    tapeLaw_probability L _
  let : IsProbabilityMeasure L.pointDraw := L.point_probability
  let μs := Measure.pi (fun j => tapeLaw L (splitRow P hR hc hsmall clock j))
  let μb := Measure.pi (fun i => tapeLaw L (publicDirectRow P hR hc hsmall clock i))
  let μn := tapeLaw L (assembled P hR hc hsmall clock ell)
  let μ0 := Measure.dirac (α := PUnit) PUnit.unit
  have ht := (measurePreserving_snd (μ := μb) (ν := μn)).comp
    (measurePreserving_snd (μ := μs) (ν := μb.prod μn))
  have hg := (MeasurePreserving.id L.pointDraw).prod ht
  exact (hg.comp ((measurePreserving_snd (μ := μ0)
    (ν := L.pointDraw.prod (μs.prod (μb.prod μn)))).comp
    (measurePreserving_snd (μ := μ0)
      (ν := μ0.prod (L.pointDraw.prod (μs.prod (μb.prod μn))))))).map_eq

/-- The complete actual code tape, including every final child occurrence,
has its proved canonical measurable split. The residual carrier is retained. -/
def fullSplitMeasurableEquiv :
    let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
      tapeSpace d (code P hR hc hsmall clock ell)
    let : MeasurableSpace (ResidualTape (code P hR hc hsmall clock ell)) :=
      residualSpace (code P hR hc hsmall clock ell)
    Tape d (code P hR hc hsmall clock ell) ≃ᵐ
      ((GaussianSlot (code P hR hc hsmall clock ell) → Point d) ×
        ResidualTape (code P hR hc hsmall clock ell)) :=
  splitGaussianMeasurableEquiv d (code P hR hc hsmall clock ell)

/-- A literal Gaussian product over *all* syntax occurrences, times the full
residual product law. This is derived from syntax, not a law hypothesis. -/
theorem fullSplitLaw :
    let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
      tapeSpace d (code P hR hc hsmall clock ell)
    let : MeasurableSpace (ResidualTape (code P hR hc hsmall clock ell)) :=
      residualSpace (code P hR hc hsmall clock ell)
    (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
      (code P hR hc hsmall clock ell)).map
        (fullSplitMeasurableEquiv P hR hc hsmall clock ell) =
      (Measure.pi fun _ : GaussianSlot (code P hR hc hsmall clock ell) =>
        stdGaussian (Point d)).prod
        (residualLaw volume (code P hR hc hsmall clock ell)) := by
  exact splitLaw_eq_product (ClockPublicSetupTapeLaw.standardLaws d)
    (code P hR hc hsmall clock ell)

/-- The entering original momentum is retained as its own coordinate in the
joint law; the full code tape is then split without dropping any residual. -/
theorem originalInputAndFullTapeLaw :
    let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
      tapeSpace d (code P hR hc hsmall clock ell)
    let : MeasurableSpace (ResidualTape (code P hR hc hsmall clock ell)) :=
      residualSpace (code P hR hc hsmall clock ell)
    ((stdGaussian (Point d)).prod
      (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
        (code P hR hc hsmall clock ell))).map
      (fun a => (a.1, splitTape (code P hR hc hsmall clock ell) a.2)) =
    (stdGaussian (Point d)).prod
      ((Measure.pi fun _ : GaussianSlot (code P hR hc hsmall clock ell) =>
        stdGaussian (Point d)).prod
        (residualLaw volume (code P hR hc hsmall clock ell))) := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
    tapeSpace d (code P hR hc hsmall clock ell)
  let : MeasurableSpace (ResidualTape (code P hR hc hsmall clock ell)) :=
    residualSpace (code P hR hc hsmall clock ell)
  let : IsProbabilityMeasure
      (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
        (code P hR hc hsmall clock ell)) :=
    tapeLaw_probability (ClockPublicSetupTapeLaw.standardLaws d) _
  have h := (MeasurePreserving.id (stdGaussian (Point d))).prod
    (measurePreserving_splitTape (ClockPublicSetupTapeLaw.standardLaws d)
      (code P hR hc hsmall clock ell))
  have hf : Prod.map (id : Point d → Point d)
        (splitTape (d := d) (code P hR hc hsmall clock ell)) =
      (fun a : Point d × Tape d (code P hR hc hsmall clock ell) =>
        (a.1, splitTape (d := d) (code P hR hc hsmall clock ell) a.2)) := by
    funext a
    cases a
    rfl
  simpa only [hf, ClockPublicSetupTapeLaw.standardLaws] using h.map_eq

/-- The actual interpreter's point-output law under that same full product.
The input momentum remains the original supplied coordinate. -/
theorem fullOutputProductLaw (G : Point d → Point d) (hG : Measurable G)
    (xF momentum : Point d) :
    let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
      tapeSpace d (code P hR hc hsmall clock ell)
    let : MeasurableSpace (ResidualTape (code P hR hc hsmall clock ell)) :=
      residualSpace (code P hR hc hsmall clock ell)
    ((Measure.pi fun _ : GaussianSlot (code P hR hc hsmall clock ell) =>
      stdGaussian (Point d)).prod
        (residualLaw volume (code P hR hc hsmall clock ell))).map (β := Point d)
      (fun a => (run (code P hR hc hsmall clock ell) G
        ⟨table P hR hc hsmall clock, xF, momentum⟩ Env.empty
        (joinTape (code P hR hc hsmall clock ell) a.1 a.2)).value) =
    (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
      (code P hR hc hsmall clock ell)).map (β := Point d)
      (fun ω => (run (code P hR hc hsmall clock ell) G
        ⟨table P hR hc hsmall clock, xF, momentum⟩ Env.empty ω).value) := by
  exact program_point_product_law (ClockPublicSetupTapeLaw.standardLaws d)
    (code P hR hc hsmall clock ell) G hG
    (table P hR hc hsmall clock) xF momentum

end AcceleratedLogConcave.Root.ClockRetainedTapeLaw
