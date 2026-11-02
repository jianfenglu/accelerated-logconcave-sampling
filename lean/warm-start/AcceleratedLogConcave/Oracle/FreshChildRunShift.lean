import AcceleratedLogConcave.Oracle.FreshChildRetainedCoupling
import AcceleratedLogConcave.Oracle.RecursiveExecutableShiftBudget

/-! Deterministic execution identity for the same completed occurrence used by
`FreshChildRetainedCoupling`. The original transformed source run at x+rho G
equals the completed source run at x, with its exact original designated input
and residual tape. The fresh-child corollary also preserves its paid Gaussian
prefix and original-gradient transcript. No approximation estimate is assumed. -/

noncomputable section
namespace AcceleratedLogConcave.Oracle.FreshChildRunShift
open TapeLowering NoisyLayer ChildAbsorption CovarianceSetup AffineLowering
open FreshChildAbsorbedLaw
variable {c c' d n : ℕ} {Γ : Ctx}

/-- Literal tape read by the completed lower-child execution. -/
theorem completedSource_eq_literal (p : Program c .point) (e : GaussianSlot p ≃ Fin n)
    (κ : Fin (n*n+c) → Fin c') (old : Ref Γ .point)
    (designated : Origin) (auxiliary : Fin n → Origin)
    (rho radius Ds : ℝ) (shift : Fin n → ℝ)
    (hrho : 0 ≤ rho) (hr : 0 < radius) (hDs : 0 < Ds)
    (hv : shiftSq shift ≤ Ds^2) (hsmall : rho ≤ radius/(2*Ds))
    (gw : Point d × Tape d (freshChild p e κ old designated auxiliary)) :
    completedSource p e κ old designated auxiliary rho radius shift gw =
      let data := freshChildTapeEquiv p e κ old designated auxiliary gw.2
      (data.1,joinTape p (fun s =>
        transformedGaussian (childRoot rho radius shift) data.2.1 (e s) -
          ((rho/radius)*shift (e s)) • gw.1) data.2.2) := by
  unfold completedSource
  rw [completedSeed_eq_literal p e κ old designated auxiliary rho radius Ds shift
    hrho hr hDs hv hsmall]

/-- Query absorption identifies the COMPLETE result of the completed run with
the original transformed source run at the noisy center, on every actual tape. -/
theorem run_completedSource (p : Program c .point) (e : GaussianSlot p ≃ Fin n)
    (κ : Fin (n*n+c) → Fin c') (old : Ref Γ .point)
    (designated : Origin) (auxiliary : Fin n → Origin)
    (rho radius Ds : ℝ) (shift : Fin n → ℝ) (coeff : Fin c → ℝ)
    (hrho : 0 ≤ rho) (hr : 0 < radius) (hDs : 0 < Ds)
    (hv : shiftSq shift ≤ Ds^2) (hsmall : rho ≤ radius/(2*Ds))
    (hshift : QueryShift p e coeff radius shift)
    (G : Point d → Point d) (x : Point d)
    (gw : Point d × Tape d (freshChild p e κ old designated auxiliary)) :
    let completed := completedSource p e κ old designated auxiliary rho radius shift gw
    let data := freshChildTapeEquiv p e κ old designated auxiliary gw.2
    run p G ⟨coeff,x,completed.1⟩ Env.empty completed.2 =
      run p G ⟨coeff,x+rho • gw.1,data.1⟩ Env.empty
        (transformedSourceTape p e (childRoot rho radius shift) data.2.1 data.2.2) := by
  let data := freshChildTapeEquiv p e κ old designated auxiliary gw.2
  let H := fun j => transformedGaussian (childRoot rho radius shift) data.2.1 j -
    ((rho/radius)*shift j) • gw.1
  have hs := hshift d G x data.1 (rho • gw.1) H data.2.2
  have hc (j : Fin n) : (shift j/radius)*rho = (rho/radius)*shift j := by ring
  have hh : (fun s => H (e s)+(shift (e s)/radius) • (rho • gw.1)) =
      fun s => transformedGaussian (childRoot rho radius shift) data.2.1 (e s) := by
    funext s
    simp only [H,smul_smul,hc,sub_add_cancel]
  rw [hh] at hs
  dsimp only
  rw [completedSource_eq_literal p e κ old designated auxiliary rho radius Ds shift
    hrho hr hDs hv hsmall]
  exact hs.symm

/-- Actual fresh-child run, with the very same completed source value and
original paid Gaussian prefix; the trace equality is not discarded. -/
theorem run_freshChild_completed (p : Program c .point) (e : GaussianSlot p ≃ Fin n)
    (κ : Fin (n*n+c) → Fin c') (old : Ref Γ .point)
    (designated : Origin) (auxiliary : Fin n → Origin)
    (rho radius Ds : ℝ) (shift : Fin n → ℝ) (coeff : Fin c → ℝ)
    (hrho : 0 ≤ rho) (hr : 0 < radius) (hDs : 0 < Ds)
    (hv : shiftSq shift ≤ Ds^2) (hsmall : rho ≤ radius/(2*Ds))
    (hshift : QueryShift p e coeff radius shift)
    (G : Point d → Point d) (input : Inputs d c') (env : Env d Γ) (x : Point d)
    (htable : input.coefficient ∘ κ = matrixTable (childRoot rho radius shift) coeff)
    (gw : Point d × Tape d (freshChild p e κ old designated auxiliary))
    (hcenter : storedPoint env old = x+rho • gw.1) :
    let completed := completedSource p e κ old designated auxiliary rho radius shift gw
    let source := run p G ⟨coeff,x,completed.1⟩ Env.empty completed.2
    run (freshChild p e κ old designated auxiliary) G input env gw.2 =
      ⟨source.value,[Event.gaussian designated] ++
        List.ofFn (fun j => Event.gaussian (auxiliary j)) ++ source.trace.filter keepNonGaussian⟩ := by
  have h := run_freshChild_shift p e κ old designated auxiliary rho radius shift coeff hr
    hshift G input env x gw.1 htable hcenter gw.2
  dsimp only
  rw [completedSource_eq_literal p e κ old designated auxiliary rho radius Ds shift
    hrho hr hDs hv hsmall]
  exact h

/-- The executed occurrence residual equals the lower-child residual on the
same retained coupling sample and reference momentum. -/
theorem freshChild_error_eq (p : Program c .point) (e : GaussianSlot p ≃ Fin n)
    (κ : Fin (n*n+c) → Fin c') (old : Ref Γ .point)
    (designated : Origin) (auxiliary : Fin n → Origin)
    (rho radius Ds : ℝ) (shift : Fin n → ℝ) (coeff : Fin c → ℝ)
    (hrho : 0 ≤ rho) (hr : 0 < radius) (hDs : 0 < Ds)
    (hv : shiftSq shift ≤ Ds^2) (hsmall : rho ≤ radius/(2*Ds))
    (hshift : QueryShift p e coeff radius shift)
    (G : Point d → Point d) (input : Inputs d c') (env : Env d Γ) (x : Point d)
    (htable : input.coefficient ∘ κ = matrixTable (childRoot rho radius shift) coeff)
    (gw : Point d × Tape d (freshChild p e κ old designated auxiliary))
    (hcenter : storedPoint env old = x+rho • gw.1) (u P' : Point d) (σ : ℝ) :
    (show Point d from (run (freshChild p e κ old designated auxiliary) G input env gw.2).value) -
        (u+σ • P') =
      let completed := completedSource p e κ old designated auxiliary rho radius shift gw
      (show Point d from (run p G ⟨coeff,x,completed.1⟩ Env.empty completed.2).value) -
        (u+σ • P') := by
  rw [run_freshChild_completed p e κ old designated auxiliary rho radius Ds shift coeff
    hrho hr hDs hv hsmall hshift G input env x htable gw hcenter]

open Numerics.AffineGraph Precision RecursiveExecutable

/-- Actual recursive-mean specialization. Its query-shift and finite shift-mass
premises are proved from the source public support-height budget, not supplied
as a correctness certificate for the selected child. -/
theorem recursiveMean_run_completedSource
    (M : MeanGeometry m) (nodes : Fin nm ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
    (mesh : IntervalMesh 0 (samplingEnd (M.R/backwardEnd M.R)))
    (snodes : Fin ns ≃ mesh.Source m)
    (Ds δ t w : ℝ) (layers : ℕ) (ht : 0 < t) (htq : t ≤ 1/4)
    (K scale : ℝ) (hDs : 0 < Ds) (hpsi : M.psi ≤ M.R^4)
    (inventory Hs : ℕ) (hcount : nm+ns ≤ inventory) (hK : (1/2:ℝ) < K)
    (hHs : 8*K+4 ≤ (Hs:ℝ))
    (hbudget : sourceShiftBase layers inventory ^ (Hs+1) ≤ Ds)
    (r σ q : ℝ) (hr : 0 < r) (hqK : q ≤ K) :
    let data := mean M nodes anchors seeds Ds δ t w ht htq layers mesh snodes scale r σ q
    ∀ (κ : Fin ((tapeShape data.program).gaussianBlocks *
        (tapeShape data.program).gaussianBlocks + data.size) → Fin c')
      (old : Ref Γ .point) (designated : Origin)
      (auxiliary : Fin (tapeShape data.program).gaussianBlocks → Origin)
      (rho : ℝ), 0 ≤ rho → rho ≤ r/(2*Ds) →
      ∀ (G : Point d → Point d) (x : Point d)
        (gw : Point d × Tape d (freshChild data.program data.enumeration κ old designated auxiliary)),
      let completed := completedSource data.program data.enumeration κ old designated auxiliary
        rho r data.shiftVector gw
      let raw := freshChildTapeEquiv data.program data.enumeration κ old designated auxiliary gw.2
      run data.program G ⟨data.coefficient,x,completed.1⟩ Env.empty completed.2 =
        run data.program G ⟨data.coefficient,x+rho • gw.1,raw.1⟩ Env.empty
          (transformedSourceTape data.program data.enumeration
            (childRoot rho r data.shiftVector) raw.2.1 raw.2.2) := by
  dsimp only
  intro κ old designated auxiliary rho hrho hsmall G x gw
  let data := mean M nodes anchors seeds Ds δ t w ht htq layers mesh snodes scale r σ q
  have hqs := source_mean_queryShift_and_mass M nodes anchors seeds mesh snodes Ds δ t w
    layers ht htq K scale hDs hpsi inventory Hs hcount hK hHs hbudget r σ q hr hqK
  have hb := source_shift_budget (layers := layers) hcount hK hHs hbudget
  have hm : shiftSq data.shiftVector ≤ Ds^2 := hqs.2.trans
    ((pow_le_pow_right₀ (shiftBase_ge_one layers nm ns)
      (precisionRank_mono (by norm_num : (0:ℝ) < 1/4) hqK)).trans hb)
  exact run_completedSource data.program data.enumeration κ old designated auxiliary
    rho r Ds data.shiftVector data.coefficient hrho hr hDs hm hsmall hqs.1 G x gw

open MeasureTheory ProbabilityTheory CanonicalTapeLaw CanonicalTapeMeasurability

local instance canonicalTapeSpace (d : ℕ) (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p

/-- The lower-child error reads the actual lower program, retained designated
input, complete source tape, and the reference momentum of its joint coupling. -/
def lowerError (p : Program c .point) (G : Point d → Point d) (coeff : Fin c → ℝ)
    (x u : Point d) (σ : ℝ) (z : (Point d × Tape d p) × Point d) : Point d :=
  (show Point d from (run p G ⟨coeff,x,z.1.1⟩ Env.empty z.1.2).value) - (u+σ • z.2)

/-- Literal executed fresh-child error on the original full occurrence seed.
Parent inputs/stores may depend on this same seed; no separate moment is
required for either store or for either absolute output. -/
def actualError (p : Program c .point) (e : GaussianSlot p ≃ Fin n)
    (κ : Fin (n*n+c) → Fin c') (old : Ref Γ .point)
    (designated : Origin) (auxiliary : Fin n → Origin) (G : Point d → Point d)
    (input : (Point d × Tape d (freshChild p e κ old designated auxiliary)) → Inputs d c')
    (env : (Point d × Tape d (freshChild p e κ old designated auxiliary)) → Env d Γ)
    (u : Point d) (σ : ℝ)
    (z : (Point d × Tape d (freshChild p e κ old designated auxiliary)) × Point d) : Point d :=
  (show Point d from (run (freshChild p e κ old designated auxiliary) G
    (input z.1) (env z.1) z.1.2).value) - (u+σ • z.2)

section ErrorTransfer
variable (L : PrimitiveLaws d) (hL : L.pointDraw = stdGaussian (Point d))
    (p : Program c .point) (e : GaussianSlot p ≃ Fin n)
    (κ : Fin (n*n+c) → Fin c') (old : Ref Γ .point)
    (designated : Origin) (auxiliary : Fin n → Origin)
    (rho radius Ds : ℝ) (shift : Fin n → ℝ) (coeff : Fin c → ℝ)
    (hrho : 0 ≤ rho) (hr : 0 < radius) (hDs : 0 < Ds)
    (hv : shiftSq shift ≤ Ds^2) (hsmall : rho ≤ radius/(2*Ds))
    (hshift : QueryShift p e coeff radius shift)
    (G : Point d → Point d) (x u : Point d) (σ : ℝ)
    (input : (Point d × Tape d (freshChild p e κ old designated auxiliary)) → Inputs d c')
    (env : (Point d × Tape d (freshChild p e κ old designated auxiliary)) → Env d Γ)
    (htable : ∀ gw, (input gw).coefficient ∘ κ = matrixTable (childRoot rho radius shift) coeff)
    (hcenter : ∀ gw, storedPoint (env gw) old = x+rho • gw.1)
    (joint : Kernel (Point d) ((Point d × Tape d p) × Point d)) [IsMarkovKernel joint]
    (hsource : joint.fst = Kernel.const (Point d) (FreshChildRetainedCoupling.sourceLaw L p))

include hshift htable hcenter hsource

/-- Only the LOWER child's error moment is an input. The conclusion concerns
the literal executed occurrence, on the same retained original sample. -/
theorem actual_error_memLp (herr : MemLp (lowerError p G coeff x u σ) 2 (joint x)) :
    MemLp (actualError p e κ old designated auxiliary G input env u σ) 2
      (FreshChildRetainedCoupling.occurrenceLaw L hL p e κ old designated auxiliary
        rho radius Ds shift hrho hr hDs hv hsmall joint x) := by
  have he : actualError p e κ old designated auxiliary G input env u σ =
      fun z => lowerError p G coeff x u σ
        (completedSource p e κ old designated auxiliary rho radius shift z.1,z.2) := by
    funext z
    exact freshChild_error_eq p e κ old designated auxiliary rho radius Ds shift coeff
      hrho hr hDs hv hsmall hshift G (input z.1) (env z.1) x (htable z.1) z.1
      (hcenter z.1) u z.2 σ
  rw [he]
  exact FreshChildRetainedCoupling.error_memLp L hL p e κ old designated auxiliary
    rho radius Ds shift hrho hr hDs hv hsmall joint hsource x (lowerError p G coeff x u σ) herr

/-- Exact squared-error payment for the original executed occurrence. This
replaces no tape/input and assumes no estimate for the enclosing parent. -/
theorem actual_error_square_integral
    (herr : MemLp (lowerError p G coeff x u σ) 2 (joint x)) :
    (∫ z, ‖actualError p e κ old designated auxiliary G input env u σ z‖^2
      ∂FreshChildRetainedCoupling.occurrenceLaw L hL p e κ old designated auxiliary
        rho radius Ds shift hrho hr hDs hv hsmall joint x) =
      ∫ z, ‖lowerError p G coeff x u σ z‖^2 ∂joint x := by
  have he : actualError p e κ old designated auxiliary G input env u σ =
      fun z => lowerError p G coeff x u σ
        (completedSource p e κ old designated auxiliary rho radius shift z.1,z.2) := by
    funext z
    exact freshChild_error_eq p e κ old designated auxiliary rho radius Ds shift coeff
      hrho hr hDs hv hsmall hshift G (input z.1) (env z.1) x (htable z.1) z.1
      (hcenter z.1) u z.2 σ
  rw [he]
  exact FreshChildRetainedCoupling.error_square_integral L hL p e κ old designated auxiliary
    rho radius Ds shift hrho hr hDs hv hsmall joint hsource x (lowerError p G coeff x u σ) herr

end ErrorTransfer

end AcceleratedLogConcave.Oracle.FreshChildRunShift
