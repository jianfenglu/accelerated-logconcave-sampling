import AcceleratedLogConcave.Root.ClockRetainedShape
import AcceleratedLogConcave.Oracle.SamplingCanonicalTapeLaw

/-! One canonical complete tape for every clock of the literal retained root.
Transport is induced solely by equality of the full typed program, preserving
every Gaussian, uniform, child and continuation coordinate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace AcceleratedLogConcave.Root.ClockRetainedTapeTransport
open MeasureTheory Oracle Oracle.TapeLowering
open Oracle.CanonicalTapeMeasurability Oracle.CanonicalTapeLaw
open ClockRetainedFinalSplice ClockRetainedShape

variable (P : SourceSchedule) (hR : P.R ≤ 1/2) (hc : 0 < P.csch)
  (hsmall : P.csch < 1/160)

def anchorClock : ClockLaw.Clock := ⟨0, by constructor <;> norm_num⟩

def codeShape (clock : ClockLaw.Clock) (ell : ℕ) :
    Σ c : ℕ, Program c .point :=
  ⟨size P hR hc hsmall clock, code P hR hc hsmall clock ell⟩

theorem codeShape_clock (clock : ClockLaw.Clock) (ell : ℕ) :
    codeShape P hR hc hsmall clock ell =
      codeShape P hR hc hsmall (anchorClock) ell := by
  exact whole_code_shape_clock P hR hc hsmall ell clock anchorClock

private def tapeEquivOfShapeEq (d : ℕ)
    {s t : Σ c : ℕ, Program c .point} (h : s = t) :
    let : MeasurableSpace (Tape d s.2) := tapeSpace d s.2
    let : MeasurableSpace (Tape d t.2) := tapeSpace d t.2
    Tape d s.2 ≃ᵐ Tape d t.2 := by
  cases h
  letI : MeasurableSpace (Tape d s.2) := tapeSpace d s.2
  exact MeasurableEquiv.refl _

private theorem map_tapeLaw_ofShapeEq (d : ℕ) (L : PrimitiveLaws d)
    {s t : Σ c : ℕ, Program c .point} (h : s = t) :
    let : MeasurableSpace (Tape d s.2) := tapeSpace d s.2
    let : MeasurableSpace (Tape d t.2) := tapeSpace d t.2
    (tapeLaw L s.2).map (tapeEquivOfShapeEq d h) = tapeLaw L t.2 := by
  cases h
  let : MeasurableSpace (Tape d s.2) := tapeSpace d s.2
  change Measure.map id (tapeLaw L s.2) = tapeLaw L s.2
  simp

private def coeffCast {s t : Σ c : ℕ, Program c .point} (h : s = t)
    (coeff : Fin s.1 → ℝ) : Fin t.1 → ℝ := by
  cases h
  exact coeff

private theorem coeffCast_symm {s t : Σ c : ℕ, Program c .point}
    (h : s = t) (coeff : Fin s.1 → ℝ) :
    coeffCast h.symm (coeffCast h coeff) = coeff := by
  cases h
  rfl

/-- The complete tape of every clock is measurably equivalent to the tape of
the fixed zero clock, at the same origin label `ell`. -/
def anchorTapeEquiv (clock : ClockLaw.Clock) (d ell : ℕ) :
    let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
      tapeSpace d (code P hR hc hsmall anchorClock ell)
    let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
      tapeSpace d (code P hR hc hsmall clock ell)
    Tape d (code P hR hc hsmall anchorClock ell) ≃ᵐ
      Tape d (code P hR hc hsmall clock ell) :=
  tapeEquivOfShapeEq d (codeShape_clock P hR hc hsmall clock ell).symm

/-- Canonical fresh-tape law is exactly preserved by the complete transport. -/
theorem map_anchorTapeLaw (clock : ClockLaw.Clock) (d ell : ℕ)
    (L : PrimitiveLaws d) :
    let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
      tapeSpace d (code P hR hc hsmall anchorClock ell)
    let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
      tapeSpace d (code P hR hc hsmall clock ell)
    (tapeLaw L (code P hR hc hsmall anchorClock ell)).map
      (anchorTapeEquiv P hR hc hsmall clock d ell) =
      tapeLaw L (code P hR hc hsmall clock ell) :=
  map_tapeLaw_ofShapeEq d L (codeShape_clock P hR hc hsmall clock ell).symm

/-- The literal clock table, reindexed to the anchor program's fixed register
count. No measurability of this family is asserted here. -/
def anchorTable (clock : ClockLaw.Clock) (ell : ℕ) :
    Fin (size P hR hc hsmall anchorClock) → ℝ :=
  coeffCast (codeShape_clock P hR hc hsmall clock ell)
    (table P hR hc hsmall clock)

private theorem run_of_shapeEq (d : ℕ)
    {s t : Σ c : ℕ, Program c .point} (h : s = t)
    (G : Point d → Point d) (coeff : Fin s.1 → ℝ)
    (x momentum : Point d) (ω : Tape d s.2) :
    run t.2 G ⟨coeffCast h coeff, x, momentum⟩ Env.empty
      (tapeEquivOfShapeEq d h ω) =
    run s.2 G ⟨coeff, x, momentum⟩ Env.empty ω := by
  cases h
  simp [coeffCast, tapeEquivOfShapeEq]

/-- Running the literal clock code on the transported whole tape is exactly
running the anchor code with the clock's complete coefficient table. -/
theorem run_anchorTape (clock : ClockLaw.Clock) (ell : ℕ) {d : ℕ}
    (G : Point d → Point d) (x momentum : Point d)
    (ω : Tape d (code P hR hc hsmall anchorClock ell)) :
    run (code P hR hc hsmall clock ell) G
      ⟨table P hR hc hsmall clock, x, momentum⟩ Env.empty
      (anchorTapeEquiv P hR hc hsmall clock d ell ω) =
    run (code P hR hc hsmall anchorClock ell) G
      ⟨anchorTable P hR hc hsmall clock ell, x, momentum⟩ Env.empty ω := by
  have h := codeShape_clock P hR hc hsmall clock ell
  have ht : coeffCast h.symm (anchorTable P hR hc hsmall clock ell) =
      table P hR hc hsmall clock := by
    exact coeffCast_symm h (table P hR hc hsmall clock)
  rw [← ht]
  exact run_of_shapeEq d h.symm G (anchorTable P hR hc hsmall clock ell)
    x momentum ω

end AcceleratedLogConcave.Root.ClockRetainedTapeTransport
