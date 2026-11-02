import AcceleratedLogConcave.Oracle.FreshChildAbsorbedLaw
import AcceleratedLogConcave.Oracle.RetainedMeanFinalBatch

/-! Completion for the literal designatedChild. Its designated input is an
existing retained value, not a Gaussian instruction of this child. Only the
actual auxiliary and residual tape is extracted and completed. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.DesignatedChildAbsorbedLaw
open AffineLowering TapeLowering NoisyLayer RetainedMeanFinalBatch
open CanonicalTapeLaw CanonicalTapeMeasurability FreshChildCanonicalSeedLaw
open Conditional.GaussianAssembly
open AcceleratedLogConcave.Probability.MixedResidualAbsorption
variable {c c' d n : ℕ} {Γ : Ctx}

local instance canonicalTapeSpace (d : ℕ) (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
local instance canonicalResidualSpace (p : Prog c Γ τ) :
    MeasurableSpace (ResidualTape p) := residualSpace p

/-- Actual compiler Gaussian/residual seed; no designated momentum is drawn. -/
def tapeSeed (p : Program c .point) (e : GaussianSlot p ≃ Fin n)
    (κ : Fin (n*n+c) → Fin c') (center P : Ref Γ .point) (auxiliary : Fin n → Origin)
    (ω : Tape d (designatedChild p e κ center P auxiliary)) :
    (Fin n → Point d) × ResidualTape p :=
  compiledTapeEquivWith p e auxiliary
    (restoreTape κ (compileWith p e auxiliary) (fun a => nomatch a) center P ω)

theorem tapeSeed_preserving (L : PrimitiveLaws d) (p : Program c .point)
    (e : GaussianSlot p ≃ Fin n) (κ : Fin (n*n+c) → Fin c')
    (center P : Ref Γ .point) (auxiliary : Fin n → Origin) :
    MeasurePreserving (tapeSeed p e κ center P auxiliary)
      (tapeLaw L (designatedChild p e κ center P auxiliary))
      ((Measure.pi fun _ : Fin n => L.pointDraw).prod (residualLaw L.uniformDraw p)) :=
  (compiledSeed_preserving L p e auxiliary).comp
    (restoreTape_preserving L κ (compileWith p e auxiliary) (fun a => nomatch a) center P)

/-- Original comparison, stored designated value, and complete literal tape. -/
abbrev Raw (d : ℕ) (p : Program c .point) (e : GaussianSlot p ≃ Fin n)
    (κ : Fin (n*n+c) → Fin c') (center P : Ref Γ .point) (auxiliary : Fin n → Origin) :=
  Point d × (Point d × Tape d (designatedChild p e κ center P auxiliary))

def completedSeed (p : Program c .point) (e : GaussianSlot p ≃ Fin n)
    (κ : Fin (n*n+c) → Fin c') (center P : Ref Γ .point) (auxiliary : Fin n → Origin)
    (rho radius : ℝ) (shift : Fin n → ℝ) (gw : Raw d p e κ center P auxiliary) :
    Point d × ((Fin n → Point d) × ResidualTape p) :=
  let hu := tapeSeed p e κ center P auxiliary gw.2.2
  (gw.2.1,(absorbed (CovarianceSetup.scaledShift rho radius shift)
    ((MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin n) => Point d)).symm
      (hu.1,gw.1)),hu.2))

private theorem completion_mass (rho radius Ds : ℝ) (shift : Fin n → ℝ)
    (hrho : 0 ≤ rho) (hr : 0 < radius) (hDs : 0 < Ds)
    (hv : CovarianceSetup.shiftSq shift ≤ Ds^2) (hsmall : rho ≤ radius/(2*Ds)) :
    mass (CovarianceSetup.scaledShift rho radius shift) < 1 := by
  have h := CovarianceSetup.child_shift_quarter shift hrho hr hDs hv hsmall
  change CovarianceSetup.shiftSq (CovarianceSetup.scaledShift rho radius shift) < 1
  linarith

theorem completedSeed_eq_literal (p : Program c .point) (e : GaussianSlot p ≃ Fin n)
    (κ : Fin (n*n+c) → Fin c') (center P : Ref Γ .point) (auxiliary : Fin n → Origin)
    (rho radius Ds : ℝ) (shift : Fin n → ℝ)
    (hrho : 0 ≤ rho) (hr : 0 < radius) (hDs : 0 < Ds)
    (hv : CovarianceSetup.shiftSq shift ≤ Ds^2) (hsmall : rho ≤ radius/(2*Ds))
    (gw : Raw d p e κ center P auxiliary) :
    completedSeed p e κ center P auxiliary rho radius shift gw =
      let hu := tapeSeed p e κ center P auxiliary gw.2.2
      (gw.2.1,((fun j => transformedGaussian (CovarianceSetup.childRoot rho radius shift)
        hu.1 j - ((rho/radius)*shift j) • gw.1),hu.2)) := by
  dsimp only [completedSeed]
  congr 2
  funext j
  simpa only [CovarianceSetup.childRoot, CovarianceSetup.childCovariance,
    CovarianceSetup.scaledShift, transformedGaussian,
    pack_input_apply, Option.elim_some, Option.elim_none] using
    absorbed_eq_sqrt (completion_mass rho radius Ds shift hrho hr hDs hv hsmall)
      ((MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin n) => Point d)).symm
        ((tapeSeed p e κ center P auxiliary gw.2.2).1,gw.1)) j

/-- The product input is a projected source law to be proved from the actual
assembly, not a claim of independence conditional on the original parent P. -/
theorem completedSeed_preserving (L : PrimitiveLaws d) (hL : L.pointDraw = stdGaussian (Point d))
    (p : Program c .point) (e : GaussianSlot p ≃ Fin n)
    (κ : Fin (n*n+c) → Fin c') (center P : Ref Γ .point) (auxiliary : Fin n → Origin)
    (rho radius Ds : ℝ) (shift : Fin n → ℝ)
    (hrho : 0 ≤ rho) (hr : 0 < radius) (hDs : 0 < Ds)
    (hv : CovarianceSetup.shiftSq shift ≤ Ds^2) (hsmall : rho ≤ radius/(2*Ds)) :
    MeasurePreserving (completedSeed p e κ center P auxiliary rho radius shift)
      ((stdGaussian (Point d)).prod (L.pointDraw.prod
        (tapeLaw L (designatedChild p e κ center P auxiliary))))
      (sourceSeedLaw L p n) := by
  let : IsProbabilityMeasure L.uniformDraw := L.uniform_probability
  let : IsProbabilityMeasure (residualLaw L.uniformDraw p) := residualLaw_probability L.uniformDraw p
  let : IsProbabilityMeasure (tapeLaw L (designatedChild p e κ center P auxiliary)) := tapeLaw_probability L _
  let γ := stdGaussian (Point d)
  let ν := (Measure.pi fun _ : Fin n => γ).prod (residualLaw L.uniformDraw p)
  have hp := tapeSeed_preserving L p e κ center P auxiliary
  dsimp only [sourceSeedLaw]
  rw [hL] at hp ⊢
  have hswap := (measurePreserving_prodAssoc γ γ ν).comp
    (((Measure.measurePreserving_swap (μ := γ) (ν := γ)).prod (MeasurePreserving.id ν)).comp
      (measurePreserving_prodAssoc γ γ ν).symm)
  have hc := (MeasurePreserving.id γ).prod
    (comparisonMixed_preserving (E := Point d)
      (completion_mass rho radius Ds shift hrho hr hDs hv hsmall) (residualLaw L.uniformDraw p))
  exact hc.comp (hswap.comp ((MeasurePreserving.id γ).prod ((MeasurePreserving.id γ).prod hp)))

def completedSource (p : Program c .point) (e : GaussianSlot p ≃ Fin n)
    (κ : Fin (n*n+c) → Fin c') (center P : Ref Γ .point) (auxiliary : Fin n → Origin)
    (rho radius : ℝ) (shift : Fin n → ℝ) (gw : Raw d p e κ center P auxiliary) : Point d × Tape d p :=
  let z := completedSeed p e κ center P auxiliary rho radius shift gw
  (z.1,joinTape p (fun s => z.2.1 (e s)) z.2.2)

@[simp] theorem completedSource_designated (p : Program c .point) (e : GaussianSlot p ≃ Fin n)
    (κ : Fin (n*n+c) → Fin c') (center P : Ref Γ .point) (auxiliary : Fin n → Origin)
    (rho radius : ℝ) (shift : Fin n → ℝ) (gw : Raw d p e κ center P auxiliary) :
    (completedSource p e κ center P auxiliary rho radius shift gw).1 = gw.2.1 := rfl

theorem completedSource_residual (p : Program c .point) (e : GaussianSlot p ≃ Fin n)
    (κ : Fin (n*n+c) → Fin c') (center P : Ref Γ .point) (auxiliary : Fin n → Origin)
    (rho radius : ℝ) (shift : Fin n → ℝ) (gw : Raw d p e κ center P auxiliary) :
    (splitTape p (completedSource p e κ center P auxiliary rho radius shift gw).2).2 =
      (tapeSeed p e κ center P auxiliary gw.2.2).2 := by
  simp only [completedSource, splitTape_joinTape, completedSeed]

private theorem joinEnumerated_preserving (L : PrimitiveLaws d) (p : Program c .point)
    (e : GaussianSlot p ≃ Fin n) :
    MeasurePreserving (fun zr : (Fin n → Point d) × ResidualTape p =>
      joinTape p (fun s => zr.1 (e s)) zr.2)
      ((Measure.pi fun _ : Fin n => L.pointDraw).prod (residualLaw L.uniformDraw p))
      (tapeLaw L p) := by
  let : IsProbabilityMeasure L.pointDraw := L.point_probability
  let : IsProbabilityMeasure L.uniformDraw := L.uniform_probability
  let : IsProbabilityMeasure (residualLaw L.uniformDraw p) := residualLaw_probability L.uniformDraw p
  let es : Tape d p ≃ᵐ ((GaussianSlot p → Point d) × ResidualTape p) :=
    ⟨splitGaussianTape d p, measurable_splitTape d p, measurable_joinTape d p⟩
  have hs : MeasurePreserving es (tapeLaw L p)
      ((Measure.pi fun _ : GaussianSlot p => L.pointDraw).prod (residualLaw L.uniformDraw p)) :=
    CanonicalTapeFactorization.measurePreserving_splitTape L p
  have h := hs.symm.comp
    ((measurePreserving_piCongrLeft (fun _ : GaussianSlot p => L.pointDraw) e.symm).prod
      (MeasurePreserving.id (residualLaw L.uniformDraw p)))
  convert h using 1
  funext zr
  apply congrArg (fun z => joinTape p z zr.2)
  funext s
  simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

theorem completedSource_preserving (L : PrimitiveLaws d) (hL : L.pointDraw = stdGaussian (Point d))
    (p : Program c .point) (e : GaussianSlot p ≃ Fin n)
    (κ : Fin (n*n+c) → Fin c') (center P : Ref Γ .point) (auxiliary : Fin n → Origin)
    (rho radius Ds : ℝ) (shift : Fin n → ℝ)
    (hrho : 0 ≤ rho) (hr : 0 < radius) (hDs : 0 < Ds)
    (hv : CovarianceSetup.shiftSq shift ≤ Ds^2) (hsmall : rho ≤ radius/(2*Ds)) :
    MeasurePreserving (completedSource p e κ center P auxiliary rho radius shift)
      ((stdGaussian (Point d)).prod (L.pointDraw.prod
        (tapeLaw L (designatedChild p e κ center P auxiliary))))
      (L.pointDraw.prod (tapeLaw L p)) := by
  let : IsProbabilityMeasure L.pointDraw := L.point_probability
  let : IsProbabilityMeasure L.uniformDraw := L.uniform_probability
  let : IsProbabilityMeasure (residualLaw L.uniformDraw p) := residualLaw_probability L.uniformDraw p
  let : IsProbabilityMeasure (tapeLaw L p) := tapeLaw_probability L p
  exact ((MeasurePreserving.id L.pointDraw).prod (joinEnumerated_preserving L p e)).comp
    (completedSeed_preserving L hL p e κ center P auxiliary rho radius Ds shift hrho hr hDs hv hsmall)

end AcceleratedLogConcave.Oracle.DesignatedChildAbsorbedLaw
