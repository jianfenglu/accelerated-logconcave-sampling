import AcceleratedLogConcave.Root.ClockJointClockExecutionKernel
import AcceleratedLogConcave.Root.ClockExposedGaussianKernel

/-! The source clock and the first public Gaussian are both visible inputs to
the literal retained root. The fresh tape retains every other coordinate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AcceleratedLogConcave.Root.ClockJointClockExposedKernel
open MeasureTheory ProbabilityTheory Oracle Oracle.TapeLowering
open Oracle.CanonicalTapeMeasurability Oracle.CanonicalTapeLaw
open ClockRetainedFinalSplice ClockRetainedTapeTransport ClockRetainedTapeLaw
open ClockRetainedShape

variable (P : SourceSchedule) (hR : P.R ≤ 1/2) (hc : 0 < P.csch)
    (hsmall : P.csch < 1/160) {d : ℕ} (ell : ℕ)

def assembledShape (clock : ClockLaw.Clock) (ell : ℕ) :
    Σ c : ℕ, Prog c (ClockPublicSetup.readyCtx P) .point :=
  ⟨size P hR hc hsmall clock, assembled P hR hc hsmall clock ell⟩

theorem assembledShape_clock (clock : ClockLaw.Clock) :
    assembledShape P hR hc hsmall clock ell =
      assembledShape P hR hc hsmall anchorClock ell := by
  apply Sigma.ext (whole_size_clock P hR hc hsmall clock anchorClock)
  exact assembled_heq P hR hc hsmall ell clock anchorClock

private def tapeEquivOfShapeEq (d : ℕ)
    {s t : Σ c : ℕ, Prog c (ClockPublicSetup.readyCtx P) .point}
    (h : s = t) :
    let : MeasurableSpace (Tape d s.2) := tapeSpace d s.2
    let : MeasurableSpace (Tape d t.2) := tapeSpace d t.2
    Tape d s.2 ≃ᵐ Tape d t.2 := by
  cases h
  letI : MeasurableSpace (Tape d s.2) := tapeSpace d s.2
  exact MeasurableEquiv.refl _

private theorem tapeEquivOfShapeEq_heq (d : ℕ)
    {s t : Σ c : ℕ, Prog c (ClockPublicSetup.readyCtx P) .point}
    (h : s = t) (ω : Tape d s.2) :
    tapeEquivOfShapeEq P d h ω ≍ ω := by
  cases h
  rfl

private def codeTapeEquivOfShapeEq (d : ℕ)
    {s t : Σ c : ℕ, Program c .point} (h : s = t) :
    let : MeasurableSpace (Tape d s.2) := tapeSpace d s.2
    let : MeasurableSpace (Tape d t.2) := tapeSpace d t.2
    Tape d s.2 ≃ᵐ Tape d t.2 := by
  cases h
  letI : MeasurableSpace (Tape d s.2) := tapeSpace d s.2
  exact MeasurableEquiv.refl _

private theorem codeTapeEquivOfShapeEq_heq (d : ℕ)
    {s t : Σ c : ℕ, Program c .point} (h : s = t) (ω : Tape d s.2) :
    codeTapeEquivOfShapeEq d h ω ≍ ω := by
  cases h
  rfl

private theorem codeTapeEquivOfShapeEq_eq_cast (d : ℕ)
    {s t : Σ c : ℕ, Program c .point} (h : s = t) (ω : Tape d s.2) :
    codeTapeEquivOfShapeEq d h ω =
      cast (congrArg (fun v : Σ c : ℕ, Program c .point => Tape d v.2) h) ω := by
  cases h
  rfl

private theorem tapeEquivOfShapeEq_eq_cast (d : ℕ)
    {s t : Σ c : ℕ, Prog c (ClockPublicSetup.readyCtx P) .point}
    (h : s = t) (ω : Tape d s.2) :
    tapeEquivOfShapeEq P d h ω =
      cast (congrArg
        (fun v : Σ c : ℕ, Prog c (ClockPublicSetup.readyCtx P) .point => Tape d v.2) h) ω := by
  cases h
  rfl

private theorem cast_prefix_coordinates {X Y A A' B B' C C' : Type}
    (hA : A = A') (hB : B = B') (hC : C = C')
    (h : (X × Y × Point d × A × B × C) =
      (X × Y × Point d × A' × B' × C'))
    (u : X × Y × Point d × A × B × C) :
    (cast h u).2.2.1 = u.2.2.1 ∧
    (cast h u).2.2.2.2.2 = cast hC u.2.2.2.2.2 := by
  cases hA
  cases hB
  cases hC
  have hh : h = rfl := Subsingleton.elim _ _
  rw [hh]
  exact ⟨rfl, rfl⟩

private theorem map_tapeLaw_ofShapeEq (d : ℕ) (L : PrimitiveLaws d)
    {s t : Σ c : ℕ, Prog c (ClockPublicSetup.readyCtx P) .point}
    (h : s = t) :
    let : MeasurableSpace (Tape d s.2) := tapeSpace d s.2
    let : MeasurableSpace (Tape d t.2) := tapeSpace d t.2
    (tapeLaw L s.2).map (tapeEquivOfShapeEq P d h) = tapeLaw L t.2 := by
  cases h
  let : MeasurableSpace (Tape d s.2) := tapeSpace d s.2
  change Measure.map id _ = _
  simp

def assembledTapeEquiv (clock : ClockLaw.Clock) :
    let : MeasurableSpace (Tape d (assembled P hR hc hsmall anchorClock ell)) :=
      tapeSpace d (assembled P hR hc hsmall anchorClock ell)
    let : MeasurableSpace (Tape d (assembled P hR hc hsmall clock ell)) :=
      tapeSpace d (assembled P hR hc hsmall clock ell)
    Tape d (assembled P hR hc hsmall anchorClock ell) ≃ᵐ
      Tape d (assembled P hR hc hsmall clock ell) :=
  tapeEquivOfShapeEq P d (assembledShape_clock P hR hc hsmall ell clock).symm

theorem map_assembledTapeLaw (clock : ClockLaw.Clock) :
    let : MeasurableSpace (Tape d (assembled P hR hc hsmall anchorClock ell)) :=
      tapeSpace d (assembled P hR hc hsmall anchorClock ell)
    let : MeasurableSpace (Tape d (assembled P hR hc hsmall clock ell)) :=
      tapeSpace d (assembled P hR hc hsmall clock ell)
    (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
      (assembled P hR hc hsmall anchorClock ell)).map
      (assembledTapeEquiv P hR hc hsmall ell clock) =
      tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
        (assembled P hR hc hsmall clock ell) :=
  map_tapeLaw_ofShapeEq P d (ClockPublicSetupTapeLaw.standardLaws d)
    (assembledShape_clock P hR hc hsmall ell clock).symm

def output (G : Point d → Point d)
    (a : (ClockLaw.Clock × ((Point d × Point d) × Point d)) ×
      Tape d (assembled P hR hc hsmall anchorClock ell)) : Point d :=
  let : MeasurableSpace (Tape d (assembled P hR hc hsmall anchorClock ell)) :=
    tapeSpace d (assembled P hR hc hsmall anchorClock ell)
  let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
    tapeSpace d (code P hR hc hsmall anchorClock ell)
  ClockJointClockExecutionKernel.output P hR hc hsmall ell G
    ((a.1.1,a.1.2.1),
      (publicPrefixMeasurableEquiv P hR hc hsmall anchorClock ell).symm
        (a.1.2.2,a.2))

theorem output_measurable (G : Point d → Point d) (hG : Measurable G) :
    let : MeasurableSpace (Tape d (assembled P hR hc hsmall anchorClock ell)) :=
      tapeSpace d (assembled P hR hc hsmall anchorClock ell)
    Measurable (output P hR hc hsmall ell G) := by
  let : MeasurableSpace (Tape d (assembled P hR hc hsmall anchorClock ell)) :=
    tapeSpace d (assembled P hR hc hsmall anchorClock ell)
  let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
    tapeSpace d (code P hR hc hsmall anchorClock ell)
  let e := publicPrefixMeasurableEquiv P hR hc hsmall anchorClock ell (d := d)
  have hf : Measurable (fun a :
      (ClockLaw.Clock × ((Point d × Point d) × Point d)) ×
        Tape d (assembled P hR hc hsmall anchorClock ell) =>
      ((a.1.1,a.1.2.1),e.symm (a.1.2.2,a.2))) :=
    (measurable_fst.fst.prodMk measurable_fst.snd.fst).prodMk
      (e.symm.measurable.comp (measurable_fst.snd.snd.prodMk measurable_snd))
  exact (ClockJointClockExecutionKernel.output_measurable P hR hc hsmall ell G hG).comp hf

def kernel (G : Point d → Point d) (hG : Measurable G) :
    Kernel (ClockLaw.Clock × ((Point d × Point d) × Point d)) (Point d) :=
  let : MeasurableSpace (Tape d (assembled P hR hc hsmall anchorClock ell)) :=
    tapeSpace d (assembled P hR hc hsmall anchorClock ell)
  letI : IsProbabilityMeasure (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
      (assembled P hR hc hsmall anchorClock ell)) :=
    tapeLaw_probability (ClockPublicSetupTapeLaw.standardLaws d)
      (assembled P hR hc hsmall anchorClock ell)
  Channels.freshKernel
    (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
      (assembled P hR hc hsmall anchorClock ell))
    (output P hR hc hsmall ell G) (output_measurable P hR hc hsmall ell G hG)

instance kernel_markov (G : Point d → Point d) (hG : Measurable G) :
    IsMarkovKernel (kernel P hR hc hsmall ell G hG) := by
  let : MeasurableSpace (Tape d (assembled P hR hc hsmall anchorClock ell)) :=
    tapeSpace d (assembled P hR hc hsmall anchorClock ell)
  have := tapeLaw_probability (ClockPublicSetupTapeLaw.standardLaws d)
    (assembled P hR hc hsmall anchorClock ell)
  unfold kernel
  infer_instance

theorem prefix_commutes (clock : ClockLaw.Clock) (E0 : Point d)
    (ω : Tape d (assembled P hR hc hsmall anchorClock ell)) :
    let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
      tapeSpace d (code P hR hc hsmall anchorClock ell)
    let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
      tapeSpace d (code P hR hc hsmall clock ell)
    let : MeasurableSpace (Tape d (assembled P hR hc hsmall anchorClock ell)) :=
      tapeSpace d (assembled P hR hc hsmall anchorClock ell)
    let : MeasurableSpace (Tape d (assembled P hR hc hsmall clock ell)) :=
      tapeSpace d (assembled P hR hc hsmall clock ell)
    anchorTapeEquiv P hR hc hsmall clock d ell
      ((publicPrefixMeasurableEquiv P hR hc hsmall anchorClock ell).symm (E0,ω)) =
    (publicPrefixMeasurableEquiv P hR hc hsmall clock ell).symm
      (E0, assembledTapeEquiv P hR hc hsmall ell clock ω) := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
    tapeSpace d (code P hR hc hsmall anchorClock ell)
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
    tapeSpace d (code P hR hc hsmall clock ell)
  let : MeasurableSpace (Tape d (assembled P hR hc hsmall anchorClock ell)) :=
    tapeSpace d (assembled P hR hc hsmall anchorClock ell)
  let : MeasurableSpace (Tape d (assembled P hR hc hsmall clock ell)) :=
    tapeSpace d (assembled P hR hc hsmall clock ell)
  let hcode := (codeShape_clock P hR hc hsmall clock ell).symm
  let hasm := (assembledShape_clock P hR hc hsmall ell clock).symm
  have hsplit (j : Fin 2) :
      (⟨size P hR hc hsmall anchorClock,
        splitRow P hR hc hsmall anchorClock j⟩ :
        Σ c : ℕ, Prog c ClockPublicSetup.rawCtx .point) =
      ⟨size P hR hc hsmall clock,
        splitRow P hR hc hsmall clock j⟩ := by
    apply Sigma.ext (whole_size_clock P hR hc hsmall anchorClock clock)
    exact splitRow_heq P hR hc hsmall j anchorClock clock
  have hdirect (i : ClockNoisyLayer.Index P) :
      (⟨size P hR hc hsmall anchorClock,
        publicDirectRow P hR hc hsmall anchorClock i⟩ :
        Σ c : ℕ, Prog c ClockPublicSetup.splitCtx .point) =
      ⟨size P hR hc hsmall clock,
        publicDirectRow P hR hc hsmall clock i⟩ := by
    apply Sigma.ext (whole_size_clock P hR hc hsmall anchorClock clock)
    exact publicDirectRow_heq P hR hc hsmall i anchorClock clock
  have hA :
      (∀ j : Fin 2, Tape d (splitRow P hR hc hsmall anchorClock j)) =
      (∀ j : Fin 2, Tape d (splitRow P hR hc hsmall clock j)) := by
    exact congrArg (fun F : Fin 2 → Type => ∀ j, F j) (funext fun j =>
      congrArg (fun v : Σ c : ℕ, Prog c ClockPublicSetup.rawCtx .point => Tape d v.2)
        (hsplit j))
  have hB :
      (∀ i : ClockNoisyLayer.Index P,
        Tape d (publicDirectRow P hR hc hsmall anchorClock i)) =
      (∀ i : ClockNoisyLayer.Index P,
        Tape d (publicDirectRow P hR hc hsmall clock i)) := by
    exact congrArg (fun F : ClockNoisyLayer.Index P → Type => ∀ i, F i)
      (funext fun i =>
        congrArg (fun v : Σ c : ℕ, Prog c ClockPublicSetup.splitCtx .point => Tape d v.2)
          (hdirect i))
  have hC : Tape d (assembled P hR hc hsmall anchorClock ell) =
      Tape d (assembled P hR hc hsmall clock ell) :=
    congrArg (fun v : Σ c : ℕ, Prog c (ClockPublicSetup.readyCtx P) .point => Tape d v.2)
      hasm
  have hFull : Tape d (code P hR hc hsmall anchorClock ell) =
      Tape d (code P hR hc hsmall clock ell) :=
    congrArg (fun v : Σ c : ℕ, Program c .point => Tape d v.2) hcode
  let u := (publicPrefixMeasurableEquiv P hR hc hsmall anchorClock ell).symm (E0,ω)
  have hu : anchorTapeEquiv P hR hc hsmall clock d ell u = cast hFull u := by
    change codeTapeEquivOfShapeEq d hcode u = _
    exact codeTapeEquivOfShapeEq_eq_cast d hcode u
  have hv : assembledTapeEquiv P hR hc hsmall ell clock ω = cast hC ω := by
    change tapeEquivOfShapeEq P d hasm ω = _
    exact tapeEquivOfShapeEq_eq_cast P d hasm ω
  have hp := cast_prefix_coordinates (d := d) hA hB hC hFull u
  apply (publicPrefixMeasurableEquiv P hR hc hsmall clock ell).injective
  apply Prod.ext
  · change (anchorTapeEquiv P hR hc hsmall clock d ell u).2.2.1 = E0
    exact (congrArg (fun t : Tape d (code P hR hc hsmall clock ell) => t.2.2.1) hu).trans
      (hp.1.trans (by rfl))
  · change (anchorTapeEquiv P hR hc hsmall clock d ell u).2.2.2.2.2 =
      assembledTapeEquiv P hR hc hsmall ell clock ω
    calc
      _ = (cast hFull u).2.2.2.2.2 := congrArg
        (fun t : Tape d (code P hR hc hsmall clock ell) => t.2.2.2.2.2) hu
      _ = cast hC u.2.2.2.2.2 := hp.2
      _ = cast hC ω := congrArg (cast hC) (by rfl)
      _ = assembledTapeEquiv P hR hc hsmall ell clock ω := hv.symm

/-- Transporting the complete literal tape leaves its first public Gaussian
draw unchanged, even though all later tape coordinates have dependent types. -/
theorem anchorTape_firstGaussian (clock : ClockLaw.Clock)
    (ω : Tape d (code P hR hc hsmall anchorClock ell)) :
    let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
      tapeSpace d (code P hR hc hsmall anchorClock ell)
    let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
      tapeSpace d (code P hR hc hsmall clock ell)
    (anchorTapeEquiv P hR hc hsmall clock d ell ω).2.2.1 = ω.2.2.1 := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
    tapeSpace d (code P hR hc hsmall anchorClock ell)
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
    tapeSpace d (code P hR hc hsmall clock ell)
  let : MeasurableSpace (Tape d (assembled P hR hc hsmall anchorClock ell)) :=
    tapeSpace d (assembled P hR hc hsmall anchorClock ell)
  let : MeasurableSpace (Tape d (assembled P hR hc hsmall clock ell)) :=
    tapeSpace d (assembled P hR hc hsmall clock ell)
  let e := publicPrefixMeasurableEquiv P hR hc hsmall anchorClock ell (d := d)
  have h := prefix_commutes P hR hc hsmall ell clock (e ω).1 (e ω).2
  have hpre : e.symm ((e ω).1, (e ω).2) = ω := by
    simpa only [Prod.mk.eta] using e.symm_apply_apply ω
  rw [hpre] at h
  have hp := congrArg (fun t : Tape d (code P hR hc hsmall clock ell) => t.2.2.1) h
  exact hp

theorem output_transport (G : Point d → Point d)
    (clock : ClockLaw.Clock) (x : Point d × Point d) (E0 : Point d)
    (ω : Tape d (assembled P hR hc hsmall anchorClock ell)) :
    let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
      tapeSpace d (code P hR hc hsmall anchorClock ell)
    let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
      tapeSpace d (code P hR hc hsmall clock ell)
    let : MeasurableSpace (Tape d (assembled P hR hc hsmall anchorClock ell)) :=
      tapeSpace d (assembled P hR hc hsmall anchorClock ell)
    let : MeasurableSpace (Tape d (assembled P hR hc hsmall clock ell)) :=
      tapeSpace d (assembled P hR hc hsmall clock ell)
    output P hR hc hsmall ell G ((clock,(x,E0)),ω) =
      ClockExposedGaussianKernel.output P hR hc hsmall clock ell G
        ((x,E0),assembledTapeEquiv P hR hc hsmall ell clock ω) := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
    tapeSpace d (code P hR hc hsmall anchorClock ell)
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
    tapeSpace d (code P hR hc hsmall clock ell)
  let : MeasurableSpace (Tape d (assembled P hR hc hsmall anchorClock ell)) :=
    tapeSpace d (assembled P hR hc hsmall anchorClock ell)
  let : MeasurableSpace (Tape d (assembled P hR hc hsmall clock ell)) :=
    tapeSpace d (assembled P hR hc hsmall clock ell)
  have hp := prefix_commutes P hR hc hsmall ell clock E0 ω
  have hr := run_anchorTape P hR hc hsmall clock ell G x.1 x.2
    ((publicPrefixMeasurableEquiv P hR hc hsmall anchorClock ell).symm (E0,ω))
  rw [hp] at hr
  exact (congrArg (fun r => r.value) hr).symm

theorem kernel_apply (G : Point d → Point d) (hG : Measurable G)
    (clock : ClockLaw.Clock) (x : Point d × Point d) (E0 : Point d) :
    kernel P hR hc hsmall ell G hG (clock,(x,E0)) =
      ClockExposedGaussianKernel.kernel P hR hc hsmall clock ell G hG (x,E0) := by
  let : MeasurableSpace (Tape d (assembled P hR hc hsmall anchorClock ell)) :=
    tapeSpace d (assembled P hR hc hsmall anchorClock ell)
  let : MeasurableSpace (Tape d (assembled P hR hc hsmall clock ell)) :=
    tapeSpace d (assembled P hR hc hsmall clock ell)
  let μ := tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
    (assembled P hR hc hsmall anchorClock ell)
  let ν := tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
    (assembled P hR hc hsmall clock ell)
  let e := assembledTapeEquiv P hR hc hsmall ell clock (d := d)
  let f : Tape d (assembled P hR hc hsmall clock ell) → Point d :=
    fun ω => ClockExposedGaussianKernel.output P hR hc hsmall clock ell G ((x,E0),ω)
  let g : Tape d (assembled P hR hc hsmall anchorClock ell) → Point d :=
    fun ω => output P hR hc hsmall ell G ((clock,(x,E0)),ω)
  have hf : Measurable f :=
    (ClockExposedGaussianKernel.output_measurable P hR hc hsmall clock ell G hG).comp
      measurable_prodMk_left
  have hge : g = f ∘ e := by
    funext ω
    exact output_transport P hR hc hsmall ell G clock x E0 ω
  change μ.map g = ν.map f
  calc
    μ.map g = μ.map (f ∘ e) := by rw [hge]
    _ = (μ.map e).map f := by rw [Measure.map_map hf e.measurable]
    _ = ν.map f := by rw [map_assembledTapeLaw P hR hc hsmall ell clock]

theorem compProd_kernel (G : Point d → Point d) (hG : Measurable G)
    (ξ : Measure (ClockLaw.Clock × ((Point d × Point d) × Point d)))
    [SFinite ξ] :
    let : MeasurableSpace (Tape d (assembled P hR hc hsmall anchorClock ell)) :=
      tapeSpace d (assembled P hR hc hsmall anchorClock ell)
    ξ ⊗ₘ kernel P hR hc hsmall ell G hG =
      (ξ.prod (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
        (assembled P hR hc hsmall anchorClock ell))).map
        (fun a => (a.1, output P hR hc hsmall ell G a)) := by
  let : MeasurableSpace (Tape d (assembled P hR hc hsmall anchorClock ell)) :=
    tapeSpace d (assembled P hR hc hsmall anchorClock ell)
  have := tapeLaw_probability (ClockPublicSetupTapeLaw.standardLaws d)
    (assembled P hR hc hsmall anchorClock ell)
  exact Channels.compProd_freshKernel ξ _ _
    (output_measurable P hR hc hsmall ell G hG)

def originalGradientKernel (V : Point d → ℝ) (hV : ContDiff ℝ 2 V) :
    Kernel (ClockLaw.Clock × ((Point d × Point d) × Point d)) (Point d) :=
  kernel P hR hc hsmall ell (gradient V)
    (ClockOriginalGradientKernel.originalGradient_measurable hV)

instance originalGradientKernel_markov (V : Point d → ℝ) (hV : ContDiff ℝ 2 V) :
    IsMarkovKernel (originalGradientKernel P hR hc hsmall ell V hV) := by
  unfold originalGradientKernel
  infer_instance

theorem originalGradientKernel_apply (V : Point d → ℝ) (hV : ContDiff ℝ 2 V)
    (clock : ClockLaw.Clock) (x : Point d × Point d) (E0 : Point d) :
    originalGradientKernel P hR hc hsmall ell V hV (clock,(x,E0)) =
      ClockExposedGaussianKernel.kernel P hR hc hsmall clock ell (gradient V)
        (ClockOriginalGradientKernel.originalGradient_measurable hV) (x,E0) :=
  kernel_apply P hR hc hsmall ell (gradient V)
    (ClockOriginalGradientKernel.originalGradient_measurable hV) clock x E0

end AcceleratedLogConcave.Root.ClockJointClockExposedKernel
