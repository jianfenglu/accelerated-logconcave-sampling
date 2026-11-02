import AcceleratedLogConcave.Oracle.FreshChildCanonicalSeedLaw
import AcceleratedLogConcave.Probability.MixedResidualAbsorption
import AcceleratedLogConcave.Oracle.CovarianceSetup

/-! Gaussian completion of the literal fresh-child seed. The comparison input
is independent of the COMPLETE fresh-child tape in the stated input product.
The designated momentum and every original residual coordinate are retained.
An arbitrary further saved factor may be retained when it is independent of
that full comparison/child block. No independence conditional on the original
parent momentum, and no Gaussian law for the transformed auxiliaries alone,
is asserted. -/

noncomputable section
namespace AcceleratedLogConcave.Oracle.FreshChildAbsorbedLaw
open MeasureTheory ProbabilityTheory AffineLowering TapeLowering NoisyLayer
open CanonicalTapeLaw CanonicalTapeMeasurability FreshChildCanonicalSeedLaw
open Conditional.GaussianAssembly
open AcceleratedLogConcave.Probability.MixedResidualAbsorption

variable {c c' d n : ℕ} {Δ : Ctx}

/-- Literal completed full seed, using the existing fresh-child tape projection. -/
def completedSeed (p : Program c .point) (e : GaussianSlot p ≃ Fin n)
    (κ : Fin (n*n+c) → Fin c') (old : Ref Δ .point)
    (designated : Origin) (auxiliary : Fin n → Origin)
    (rho radius : ℝ) (shift : Fin n → ℝ)
    (gw : Point d × Tape d (freshChild p e κ old designated auxiliary)) :
    Point d × ((Fin n → Point d) × ResidualTape p) :=
  let z := freshChildTapeEquiv p e κ old designated auxiliary gw.2
  (z.1,(absorbed (CovarianceSetup.scaledShift rho radius shift)
    ((MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin n) => Point d)).symm
      (z.2.1,gw.1)),z.2.2))

private theorem completion_mass (rho radius Ds : ℝ) (shift : Fin n → ℝ)
    (hrho : 0 ≤ rho) (hr : 0 < radius) (hDs : 0 < Ds)
    (hv : CovarianceSetup.shiftSq shift ≤ Ds^2) (hsmall : rho ≤ radius/(2*Ds)) :
    mass (CovarianceSetup.scaledShift rho radius shift) < 1 := by
  have h := CovarianceSetup.child_shift_quarter shift hrho hr hDs hv hsmall
  change CovarianceSetup.shiftSq (CovarianceSetup.scaledShift rho radius shift) < 1
  linarith

/-- The completion is exactly the prescribed `childRoot` transform minus the
comparison shift. The same designated momentum and full residual are untouched. -/
theorem completedSeed_eq_literal (p : Program c .point) (e : GaussianSlot p ≃ Fin n)
    (κ : Fin (n*n+c) → Fin c') (old : Ref Δ .point)
    (designated : Origin) (auxiliary : Fin n → Origin)
    (rho radius Ds : ℝ) (shift : Fin n → ℝ)
    (hrho : 0 ≤ rho) (hr : 0 < radius) (hDs : 0 < Ds)
    (hv : CovarianceSetup.shiftSq shift ≤ Ds^2) (hsmall : rho ≤ radius/(2*Ds))
    (gw : Point d × Tape d (freshChild p e κ old designated auxiliary)) :
    completedSeed p e κ old designated auxiliary rho radius shift gw =
      let z := freshChildTapeEquiv p e κ old designated auxiliary gw.2
      (z.1,((fun j => transformedGaussian (CovarianceSetup.childRoot rho radius shift)
        z.2.1 j - ((rho/radius)*shift j) • gw.1),z.2.2)) := by
  dsimp only [completedSeed]
  congr 2
  funext j
  simpa only [CovarianceSetup.childRoot, CovarianceSetup.childCovariance,
    CovarianceSetup.scaledShift, transformedGaussian,
    pack_input_apply, Option.elim_some, Option.elim_none] using
    absorbed_eq_sqrt (completion_mass rho radius Ds shift hrho hr hDs hv hsmall)
      ((MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin n) => Point d)).symm
        ((freshChildTapeEquiv p e κ old designated auxiliary gw.2).2.1,gw.1)) j

/-- Canonical full-seed law is derived from the actual fresh-child law and the
independent comparison input, with no replacement of residual leaves. -/
theorem completedSeed_preserving (L : PrimitiveLaws d)
    (hL : L.pointDraw = stdGaussian (Point d))
    (p : Program c .point) (e : GaussianSlot p ≃ Fin n)
    (κ : Fin (n*n+c) → Fin c') (old : Ref Δ .point)
    (designated : Origin) (auxiliary : Fin n → Origin)
    (rho radius Ds : ℝ) (shift : Fin n → ℝ)
    (hrho : 0 ≤ rho) (hr : 0 < radius) (hDs : 0 < Ds)
    (hv : CovarianceSetup.shiftSq shift ≤ Ds^2) (hsmall : rho ≤ radius/(2*Ds)) :
    let : MeasurableSpace (Tape d (freshChild p e κ old designated auxiliary)) := tapeSpace d _
    let : MeasurableSpace (ResidualTape p) := residualSpace p
    MeasurePreserving (completedSeed p e κ old designated auxiliary rho radius shift)
      ((stdGaussian (Point d)).prod (tapeLaw L (freshChild p e κ old designated auxiliary)))
      (sourceSeedLaw L p n) := by
  let : MeasurableSpace (Tape d (freshChild p e κ old designated auxiliary)) := tapeSpace d _
  let : MeasurableSpace (ResidualTape p) := residualSpace p
  let : IsProbabilityMeasure L.uniformDraw := L.uniform_probability
  let : IsProbabilityMeasure (residualLaw L.uniformDraw p) :=
    residualLaw_probability L.uniformDraw p
  let : IsProbabilityMeasure (tapeLaw L (freshChild p e κ old designated auxiliary)) :=
    tapeLaw_probability L _
  let γ := stdGaussian (Point d)
  let ν := (Measure.pi fun _ : Fin n => γ).prod (residualLaw L.uniformDraw p)
  have hp := freshChildSeed_preserving L p e κ old designated auxiliary
  dsimp only [sourceSeedLaw] at hp ⊢
  rw [hL] at hp ⊢
  have hswap := (measurePreserving_prodAssoc γ γ ν).comp
    (((Measure.measurePreserving_swap (μ := γ) (ν := γ)).prod (MeasurePreserving.id ν)).comp
      (measurePreserving_prodAssoc γ γ ν).symm)
  have hc := (MeasurePreserving.id γ).prod
    (comparisonMixed_preserving (E := Point d)
      (completion_mass rho radius Ds shift hrho hr hDs hv hsmall)
      (residualLaw L.uniformDraw p))
  exact hc.comp (hswap.comp ((MeasurePreserving.id γ).prod hp))

/-- Rebuild the actual source tape from the completed Gaussian inventory and
its unchanged original residual, keeping the designated momentum. -/
def completedSource (p : Program c .point) (e : GaussianSlot p ≃ Fin n)
    (κ : Fin (n*n+c) → Fin c') (old : Ref Δ .point)
    (designated : Origin) (auxiliary : Fin n → Origin)
    (rho radius : ℝ) (shift : Fin n → ℝ)
    (gw : Point d × Tape d (freshChild p e κ old designated auxiliary)) : Point d × Tape d p :=
  let z := completedSeed p e κ old designated auxiliary rho radius shift gw
  (z.1,joinTape p (fun s => z.2.1 (e s)) z.2.2)

/-- The designated input is the literal same draw of the executed child. -/
theorem completedSource_designated (p : Program c .point) (e : GaussianSlot p ≃ Fin n)
    (κ : Fin (n*n+c) → Fin c') (old : Ref Δ .point)
    (designated : Origin) (auxiliary : Fin n → Origin)
    (rho radius : ℝ) (shift : Fin n → ℝ)
    (gw : Point d × Tape d (freshChild p e κ old designated auxiliary)) :
    (completedSource p e κ old designated auxiliary rho radius shift gw).1 =
      (freshChildTapeEquiv p e κ old designated auxiliary gw.2).1 := rfl

/-- Every original residual coordinate is kept pathwise, including uniforms. -/
theorem completedSource_residual (p : Program c .point) (e : GaussianSlot p ≃ Fin n)
    (κ : Fin (n*n+c) → Fin c') (old : Ref Δ .point)
    (designated : Origin) (auxiliary : Fin n → Origin)
    (rho radius : ℝ) (shift : Fin n → ℝ)
    (gw : Point d × Tape d (freshChild p e κ old designated auxiliary)) :
    (splitTape p (completedSource p e κ old designated auxiliary rho radius shift gw).2).2 =
      (freshChildTapeEquiv p e κ old designated auxiliary gw.2).2.2 := by
  simp only [completedSource, splitTape_joinTape, completedSeed]

private theorem joinEnumerated_preserving (L : PrimitiveLaws d)
    (p : Program c .point) (e : GaussianSlot p ≃ Fin n) :
    let : MeasurableSpace (Tape d p) := tapeSpace d p
    let : MeasurableSpace (ResidualTape p) := residualSpace p
    MeasurePreserving (fun zr : (Fin n → Point d) × ResidualTape p =>
      joinTape p (fun s => zr.1 (e s)) zr.2)
      ((Measure.pi fun _ : Fin n => L.pointDraw).prod (residualLaw L.uniformDraw p))
      (tapeLaw L p) := by
  let : MeasurableSpace (Tape d p) := tapeSpace d p
  let : MeasurableSpace (ResidualTape p) := residualSpace p
  let : IsProbabilityMeasure L.pointDraw := L.point_probability
  let : IsProbabilityMeasure L.uniformDraw := L.uniform_probability
  let : IsProbabilityMeasure (residualLaw L.uniformDraw p) :=
    residualLaw_probability L.uniformDraw p
  let es : Tape d p ≃ᵐ ((GaussianSlot p → Point d) × ResidualTape p) :=
    ⟨splitGaussianTape d p, measurable_splitTape d p, measurable_joinTape d p⟩
  have hs : MeasurePreserving es (tapeLaw L p)
      ((Measure.pi fun _ : GaussianSlot p => L.pointDraw).prod (residualLaw L.uniformDraw p)) :=
    CanonicalTapeFactorization.measurePreserving_splitTape L p
  have hj := hs.symm
  have h := hj.comp
    ((measurePreserving_piCongrLeft (fun _ : GaussianSlot p => L.pointDraw) e.symm).prod
      (MeasurePreserving.id (residualLaw L.uniformDraw p)))
  convert h using 1
  funext zr
  apply congrArg (fun z => joinTape p z zr.2)
  funext s
  simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

/-- The literal completed source tape and designated momentum have the full
canonical standalone law, including every original uniform/unit coordinate. -/
theorem completedSource_preserving (L : PrimitiveLaws d)
    (hL : L.pointDraw = stdGaussian (Point d))
    (p : Program c .point) (e : GaussianSlot p ≃ Fin n)
    (κ : Fin (n*n+c) → Fin c') (old : Ref Δ .point)
    (designated : Origin) (auxiliary : Fin n → Origin)
    (rho radius Ds : ℝ) (shift : Fin n → ℝ)
    (hrho : 0 ≤ rho) (hr : 0 < radius) (hDs : 0 < Ds)
    (hv : CovarianceSetup.shiftSq shift ≤ Ds^2) (hsmall : rho ≤ radius/(2*Ds)) :
    let : MeasurableSpace (Tape d (freshChild p e κ old designated auxiliary)) := tapeSpace d _
    let : MeasurableSpace (Tape d p) := tapeSpace d p
    MeasurePreserving (completedSource p e κ old designated auxiliary rho radius shift)
      ((stdGaussian (Point d)).prod (tapeLaw L (freshChild p e κ old designated auxiliary)))
      (L.pointDraw.prod (tapeLaw L p)) := by
  let : MeasurableSpace (Tape d (freshChild p e κ old designated auxiliary)) := tapeSpace d _
  let : MeasurableSpace (Tape d p) := tapeSpace d p
  let : MeasurableSpace (ResidualTape p) := residualSpace p
  let : IsProbabilityMeasure L.pointDraw := L.point_probability
  let : IsProbabilityMeasure L.uniformDraw := L.uniform_probability
  let : IsProbabilityMeasure (residualLaw L.uniformDraw p) :=
    residualLaw_probability L.uniformDraw p
  exact ((MeasurePreserving.id L.pointDraw).prod (joinEnumerated_preserving L p e)).comp
    (completedSeed_preserving L hL p e κ old designated auxiliary rho radius Ds shift
      hrho hr hDs hv hsmall)

/-- Retain a whole saved/coarse-host factor under the stated product law. This
does not assert that the comparison remains independent after conditioning on
the original parent momentum or other tape-dependent observations. -/
theorem completedSource_saved_preserving {R : Type*} [MeasurableSpace R]
    (L : PrimitiveLaws d) (hL : L.pointDraw = stdGaussian (Point d))
    (p : Program c .point) (e : GaussianSlot p ≃ Fin n)
    (κ : Fin (n*n+c) → Fin c') (old : Ref Δ .point)
    (designated : Origin) (auxiliary : Fin n → Origin)
    (rho radius Ds : ℝ) (shift : Fin n → ℝ)
    (hrho : 0 ≤ rho) (hr : 0 < radius) (hDs : 0 < Ds)
    (hv : CovarianceSetup.shiftSq shift ≤ Ds^2) (hsmall : rho ≤ radius/(2*Ds))
    (saved : Measure R) [SFinite saved] :
    let : MeasurableSpace (Tape d (freshChild p e κ old designated auxiliary)) := tapeSpace d _
    let : MeasurableSpace (Tape d p) := tapeSpace d p
    MeasurePreserving
      (fun gs : (Point d × Tape d (freshChild p e κ old designated auxiliary)) × R =>
        (completedSource p e κ old designated auxiliary rho radius shift gs.1,gs.2))
      (((stdGaussian (Point d)).prod
        (tapeLaw L (freshChild p e κ old designated auxiliary))).prod saved)
      ((L.pointDraw.prod (tapeLaw L p)).prod saved) := by
  let : MeasurableSpace (Tape d (freshChild p e κ old designated auxiliary)) := tapeSpace d _
  let : MeasurableSpace (Tape d p) := tapeSpace d p
  let : IsProbabilityMeasure L.pointDraw := L.point_probability
  let : IsProbabilityMeasure (tapeLaw L p) := tapeLaw_probability L p
  let : IsProbabilityMeasure (tapeLaw L (freshChild p e κ old designated auxiliary)) :=
    tapeLaw_probability L _
  exact (completedSource_preserving L hL p e κ old designated auxiliary rho radius Ds shift
    hrho hr hDs hv hsmall).prod (MeasurePreserving.id saved)

end AcceleratedLogConcave.Oracle.FreshChildAbsorbedLaw
