import AcceleratedLogConcave.Root.ClockRepeatedLayers
import AcceleratedLogConcave.Root.FinalMeanScheduledData
import AcceleratedLogConcave.Oracle.RetainedMeanFinalValue
import AcceleratedLogConcave.Root.RetainedLaw

/-!
This is the normalized retained active-final correction, NOT a physical final
position readout and NOT a reopened dormant-W12 estimate.
The supplied xF is the entering normalized position. The retained parent is
ClockPublicSetup.hRef (H0), NOT pRef (the momentum before the public split).

The assembly precedes center initialization. The same P_i survive every one
of K+4 layers and are used by designatedChild, never by freshChild. The
comparison reserve is algebraic only; no reserve Gaussian is drawn.

No law, measurability, accuracy, W12, or analytic regularity theorem is claimed.
Full public-prefix Result and whole-code pack/unpack are checked below.
The pack/unpack bijection keeps every raw coordinate;
neither this bijection nor every-tape semantics asserts a probability law.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
namespace AcceleratedLogConcave.Root.ClockRetainedFinalSplice
open Oracle Oracle.AffineLowering Oracle.NoisyLayer Oracle.TapeLowering
open Oracle.RecursiveMeanProgram Oracle.RecursiveMeanContinuation
open Oracle.RetainedMeanFinalBatch
open ClockNoisyLayer
open scoped BigOperators

variable (P : SourceSchedule) (hR : P.R ≤ 1/2) (hc : 0 < P.csch)
  (hsmall : P.csch < 1/160) (clock : ClockLaw.Clock)

abbrev final (i : Index P) : ExecutableData :=
  FinalMeanScheduledData.finalData P hR hc hsmall i clock
abbrev cf (i : Index P) := (final P hR hc hsmall clock i).size
abbrev pf (i : Index P) : Program (cf P hR hc hsmall clock i) .point :=
  (final P hR hc hsmall clock i).program
abbrev ef (i : Index P) := (final P hR hc hsmall clock i).enumeration
abbrev gf (i : Index P) := (tapeShape (pf P hR hc hsmall clock i)).gaussianBlocks

def weight (i : Index P) : ℝ := ClockSchedule.weight
  (ClockSchedule.sourceCells P.delta) (ClockSchedule.sourceOrder P.K) clock i
def coefficient (i : Index P) : ℝ := -weight P clock i
def width (i : Index P) : ℝ := (FinalMeanScheduledData.state P i clock).width
/-- Normalize the final mean reply to the same unit H0 scale as RetainedLaw. -/
def correctionWeight (i : Index P) : ℝ := coefficient P clock i / width P clock i

def finalRoot (i : Index P) : CovarianceSetup.Mat (gf P hR hc hsmall clock i) :=
  CovarianceSetup.childRoot (rhoC P) (FinalMeanScheduledData.state P i clock).radius
    (final P hR hc hsmall clock i).shiftVector

abbrev oldSize := ClockPublicSetup.size P hR hc hsmall clock
abbrev assemblySize := N P * N P + N P
abbrev finalSize := ∑ i, childSize (pf P hR hc hsmall clock i)
abbrev correctionSize := 1 + (N P + N P)
abbrev size := oldSize P hR hc hsmall clock +
  (assemblySize P + (finalSize P hR hc hsmall clock + correctionSize P))

def oldSlot (i : Fin (oldSize P hR hc hsmall clock)) : Fin (size P hR hc hsmall clock) :=
  Fin.castAdd _ i
def assemblySlot (i : Fin (assemblySize P)) : Fin (size P hR hc hsmall clock) :=
  Fin.natAdd (oldSize P hR hc hsmall clock) (Fin.castAdd _ i)
def finalSlot (i : Index P) (k : Fin (childSize (pf P hR hc hsmall clock i))) :
    Fin (size P hR hc hsmall clock) :=
  Fin.natAdd (oldSize P hR hc hsmall clock) (Fin.natAdd (assemblySize P)
    (Fin.castAdd (correctionSize P) (finSigmaFinEquiv ⟨i,k⟩)))
def correctionSlot (i : Fin (correctionSize P)) : Fin (size P hR hc hsmall clock) :=
  Fin.natAdd (oldSize P hR hc hsmall clock) (Fin.natAdd (assemblySize P)
    (Fin.natAdd (finalSize P hR hc hsmall clock) i))

def table : Fin (size P hR hc hsmall clock) → ℝ :=
  Fin.append (ClockPublicSetup.table P hR hc hsmall clock)
    (Fin.append (MeanGaussianSetup.table (coefficient P clock))
      (Fin.append (fun k => let q := finSigmaFinEquiv.symm k
        matrixTable (finalRoot P hR hc hsmall clock q.1)
          (final P hR hc hsmall clock q.1).coefficient q.2)
        (RetainedMeanCorrection.table 1 (correctionWeight P clock) (width P clock))))

theorem table_old (i : Fin (oldSize P hR hc hsmall clock)) :
    table P hR hc hsmall clock (oldSlot P hR hc hsmall clock i) =
      ClockPublicSetup.table P hR hc hsmall clock i := by simp [table,oldSlot]
theorem table_assembly : table P hR hc hsmall clock ∘ assemblySlot P hR hc hsmall clock =
    MeanGaussianSetup.table (coefficient P clock) := by
  funext i; simp [table,assemblySlot]
theorem table_final (i : Index P) :
    table P hR hc hsmall clock ∘ finalSlot P hR hc hsmall clock i =
      matrixTable (finalRoot P hR hc hsmall clock i)
        (final P hR hc hsmall clock i).coefficient := by
  funext k
  simp only [Function.comp_apply,table,finalSlot,Fin.append_right,Fin.append_left]
  erw [Equiv.symm_apply_apply]
theorem table_correction : table P hR hc hsmall clock ∘ correctionSlot P hR hc hsmall clock =
    RetainedMeanCorrection.table 1 (correctionWeight P clock) (width P clock) := by
  funext i; simp [table,correctionSlot]

/-- Ready already contains xF, Y0, H0, E0, and every direct row. -/
abbrev assembledCtx := replyCtx (N P) (replyCtx (N P) (ClockPublicSetup.readyCtx P))
abbrev entryCtx := replyCtx (N P) (replyCtx (N P) (assembledCtx P))
def assemblySaved : RefMap (ClockPublicSetup.readyCtx P) (assembledCtx P) :=
  fun r => RefMap.shiftMany (N P) (RefMap.shiftMany (N P) r)
def entrySaved : RefMap (assembledCtx P) (entryCtx P) :=
  fun r => RefMap.shiftMany (N P) (RefMap.shiftMany (N P) r)
def parentRef : Ref (entryCtx P) .point :=
  entrySaved P (assemblySaved P (ClockPublicSetup.saved P ClockPublicSetup.hRef))
def designatedRef (i : Index P) : Ref (entryCtx P) .point := entrySaved P (batchRef i)
def directRef (i : Index P) : Ref (entryCtx P) .point :=
  entrySaved P (assemblySaved P (ClockPublicSetup.directRef P i))
def oldRef (i : Index P) : Ref (entryCtx P) .point := batchRef i

def assemblyOrigin (ell : ℕ) (i : Index P) : Origin :=
  [⟨.publicSampling,.setup,2,ell,i.val⟩]
def finalAuxiliary (ell : ℕ) (i : Index P) (j : Fin (gf P hR hc hsmall clock i)) : Origin :=
  [⟨.publicSampling,.samplingLayer,j.val+2,P.K+4,ell*N P+i.val⟩]

abbrev Finish := ∀ {Δ : Ctx}, (Index P → Ref Δ .point) →
  (Index P → Ref Δ .point) → RefMap (entryCtx P) Δ → Prog (size P hR hc hsmall clock) Δ .point

def finish (ell : ℕ) : Finish P hR hc hsmall clock := fun old _ saved =>
  paidCorrection (cf P hR hc hsmall clock) (pf P hR hc hsmall clock)
    (ef P hR hc hsmall clock) (finalSlot P hR hc hsmall clock)
    (correctionSlot P hR hc hsmall clock) (saved (parentRef P)) old
    (fun i => saved (designatedRef P i)) [] (finalAuxiliary P hR hc hsmall clock ell)

def mainSlots := oldSlot P hR hc hsmall clock ∘ ClockRepeatedLayers.slots P hR hc hsmall clock
def loop (ell : ℕ) : Prog (size P hR hc hsmall clock) (entryCtx P) .point :=
  iterateThen (c P hR hc hsmall clock) (p P hR hc hsmall clock)
    (mainSlots P hR hc hsmall clock) (e P hR hc hsmall clock) (fun _ => [])
    (ClockRepeatedLayers.designated P (P.K+4)) (ClockRepeatedLayers.residual P (P.K+4))
    (ClockRepeatedLayers.auxiliary P hR hc hsmall clock (P.K+4))
    (finish P hR hc hsmall clock ell) (P.K+4) (oldRef P) (directRef P) (fun r => r)

def initialized (ell : ℕ) : Prog (size P hR hc hsmall clock) (assembledCtx P) .point :=
  initializeCenters (oldSlot P hR hc hsmall clock (ClockRepeatedLayers.rhoSlot P hR hc hsmall clock))
    (fun i => assemblySaved P (ClockPublicSetup.directRef P i)) []
    (ClockInitialLayer.initialOrigin P ell) (loop P hR hc hsmall clock ell)

def assembled (ell : ℕ) : Prog (size P hR hc hsmall clock) (ClockPublicSetup.readyCtx P) .point :=
  MeanGaussianSetup.setup (assemblySlot P hR hc hsmall clock)
    (ClockPublicSetup.saved P ClockPublicSetup.hRef) (assemblyOrigin P ell)
    (initialized P hR hc hsmall clock ell)

/-- Reindex only the old pure rows. No replacement Gaussian input is inserted. -/
def splitRow (j : Fin 2) : Prog (size P hR hc hsmall clock) ClockPublicSetup.rawCtx .point :=
  (ClockPublicSetup.splitRow P hR hc hsmall clock j).lower
    (oldSlot P hR hc hsmall clock) (fun r => r)
    (.there (.there .here)) (.there .here)
def publicDirectRow (i : Index P) : Prog (size P hR hc hsmall clock) ClockPublicSetup.splitCtx .point :=
  (ClockPublicSetup.directRow P hR hc hsmall clock i).lower
    (oldSlot P hR hc hsmall clock) (fun r => r) ClockPublicSetup.xRef ClockPublicSetup.pRef

def code (ell : ℕ) : Program (size P hR hc hsmall clock) .point :=
  .step [] .center (.step [] .momentum (.step (ClockPublicSetup.origin ell) .gaussian
    (.batch [] (splitRow P hR hc hsmall clock) (.batch [] (publicDirectRow P hR hc hsmall clock)
      (assembled P hR hc hsmall clock ell)))))

/-- Local final semantics includes all child traces, even zero-weight children. -/
theorem run_finish {d : ℕ} {Δ : Ctx} (ell : ℕ)
    (old direct : Index P → Ref Δ .point) (saved : RefMap (entryCtx P) Δ)
    (G : Point d → Point d) (xF momentum : Point d) (env : Env d Δ)
    (tape : Tape d (finish P hR hc hsmall clock ell old direct saved)) :
    let input : Inputs d (size P hR hc hsmall clock) := ⟨table P hR hc hsmall clock,xF,momentum⟩
    let children := fun i => run
      (designatedChild (pf P hR hc hsmall clock i) (ef P hR hc hsmall clock i)
        (finalSlot P hR hc hsmall clock i) (old i) (saved (designatedRef P i))
        (finalAuxiliary P hR hc hsmall clock ell i)) G input env (tape.1 i)
    run (finish P hR hc hsmall clock ell old direct saved) G input env tape =
      pointResult ((1 : ℝ) • storedPoint env (saved (parentRef P)) + ∑ i, correctionWeight P clock i •
        (childPoint (children i) - width P clock i • storedPoint env (saved (designatedRef P i))))
        (((List.ofFn fun i => (children i).trace).flatten).map (Event.withPrefix [])) :=
  run_paidCorrection _ _ _ _ _ _ _ _ _ _ 1 (correctionWeight P clock) (width P clock)
    G ⟨table P hR hc hsmall clock,xF,momentum⟩ env (table_correction P hR hc hsmall clock) tape

/-- Nothing in the loop may overwrite the original parent or designated inputs. -/
theorem loop_saved {d : ℕ} (ell : ℕ) (G : Point d → Point d)
    (input : Inputs d (size P hR hc hsmall clock)) (env : Env d (entryCtx P))
    (tape : Tape d (loop P hR hc hsmall clock ell)) (r : Ref (entryCtx P) .point) :
    let st := finalState (c P hR hc hsmall clock) (p P hR hc hsmall clock)
      (mainSlots P hR hc hsmall clock) (e P hR hc hsmall clock) (fun _ => [])
      (ClockRepeatedLayers.designated P (P.K+4)) (ClockRepeatedLayers.residual P (P.K+4))
      (ClockRepeatedLayers.auxiliary P hR hc hsmall clock (P.K+4))
      (finish P hR hc hsmall clock ell) G input (P.K+4) (oldRef P) (directRef P)
      (fun r => r) env tape
    storedPoint st.env (st.saved r) = storedPoint env r :=
  finalState_saved _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r

/-- Full typed loop tape, including residual uniform/unit coordinates and the
literal paid final tape at depth zero. This does not assert a tape law. -/
def loopTapeEquiv (d ell : ℕ) :=
  rawTapeEquiv (c P hR hc hsmall clock) (p P hR hc hsmall clock)
    (mainSlots P hR hc hsmall clock) (e P hR hc hsmall clock) (fun _ => [])
    (ClockRepeatedLayers.designated P (P.K+4)) (ClockRepeatedLayers.residual P (P.K+4))
    (ClockRepeatedLayers.auxiliary P hR hc hsmall clock (P.K+4))
    (finish P hR hc hsmall clock ell) d (P.K+4) (oldRef P) (directRef P) (fun r => r)

theorem loop_tape_roundtrip {d : ℕ} (ell : ℕ) (tape : Tape d (loop P hR hc hsmall clock ell)) :
    (loopTapeEquiv P hR hc hsmall clock d ell).symm
      (loopTapeEquiv P hR hc hsmall clock d ell tape) = tape := Equiv.symm_apply_apply _ _

def designatedTapeEquiv {d : ℕ} {Δ : Ctx} (ell : ℕ) (i : Index P)
    (center active : Ref Δ .point) :
    Tape d (designatedChild (pf P hR hc hsmall clock i) (ef P hR hc hsmall clock i)
      (finalSlot P hR hc hsmall clock i) center active (finalAuxiliary P hR hc hsmall clock ell i)) ≃
      ((Fin (gf P hR hc hsmall clock i) → Point d) × ResidualTape (pf P hR hc hsmall clock i)) :=
  (lowerTapeEquiv (finalSlot P hR hc hsmall clock i)
    (compileWith (pf P hR hc hsmall clock i) (ef P hR hc hsmall clock i)
      (finalAuxiliary P hR hc hsmall clock ell i)) (fun r => nomatch r) center active).symm.trans
    (compiledTapeEquivWith (pf P hR hc hsmall clock i) (ef P hR hc hsmall clock i)
      (finalAuxiliary P hR hc hsmall clock ell i))


/-! The following equivalences are deterministic structural bijections only.
All residual source tapes (including uniform and unit coordinates) are kept.
The raw assembly and initialization arrays are separate coordinates; no
probabilistic independence or distributional assertion is made here. -/

/-- Structural tape of the pure, unlowered final correction. -/
def correctionPureTape {d m : ℕ} {Γ : Ctx} (parent : Ref Γ .point)
    (reply designated : Fin m → Ref Γ .point) :
    Tape d (RetainedMeanCorrection.code parent reply designated) :=
  ⟨PUnit.unit, PUnit.unit, rowTape d []
    (List.ofFn fun j : Fin (m+m) =>
      (Fin.natAdd 1 j, .there (.there (Fin.append reply designated j))))
    (fun r => r) .here⟩

theorem correctionPureTape_unique {d m : ℕ} {Γ : Ctx} (parent : Ref Γ .point)
    (reply designated : Fin m → Ref Γ .point)
    (tape : Tape d (RetainedMeanCorrection.code parent reply designated)) :
    tape = correctionPureTape parent reply designated := by
  rcases tape with ⟨⟨⟩, ⟨⟩, tail⟩
  exact congrArg (fun t => (PUnit.unit, PUnit.unit, t))
    (rowTape_unique [] _ (fun r => r) .here tail)

/-- Pure-row uniqueness transports across the exact lowering bijection. -/
theorem loweredTape_unique {d C C' : ℕ} {Γ Δ : Ctx} {τ : Ty}
    (slots : Fin C → Fin C') (prog : Prog C Γ τ)
    (refs : RefMap Γ Δ) (center momentum : Ref Δ .point)
    (canonical : Tape d prog) (unique : ∀ t, t = canonical)
    (tape : Tape d (prog.lower slots refs center momentum)) :
    tape = lowerTape slots prog refs center momentum canonical := by
  calc
    tape = lowerTape slots prog refs center momentum
      (restoreTape slots prog refs center momentum tape) :=
        (lowerTape_restoreTape slots prog refs center momentum tape).symm
    _ = _ := congrArg (lowerTape slots prog refs center momentum) (unique _)

/-- Every final auxiliary block and the complete residual tape of every final
child. There is no fresh designated coordinate at the final stage. -/
abbrev FinalTapeData (d : ℕ) := ∀ i : Index P,
  (Fin (gf P hR hc hsmall clock i) → Point d) ×
    ResidualTape (pf P hR hc hsmall clock i)

def finishTapeEquiv {d : ℕ} {Δ : Ctx} (ell : ℕ)
    (old direct : Index P → Ref Δ .point) (saved : RefMap (entryCtx P) Δ) :
    Tape d (finish P hR hc hsmall clock ell old direct saved) ≃
      FinalTapeData P hR hc hsmall clock d where
  toFun tape i := designatedTapeEquiv P hR hc hsmall clock ell i
    (old i) (saved (designatedRef P i)) (tape.1 i)
  invFun data := ⟨(fun i => (designatedTapeEquiv P hR hc hsmall clock ell i
      (old i) (saved (designatedRef P i))).symm (data i)),
    lowerTape (correctionSlot P hR hc hsmall clock)
      (RetainedMeanCorrection.code (RefMap.shiftMany (N P) (saved (parentRef P)))
        batchRef (fun i => RefMap.shiftMany (N P) (saved (designatedRef P i))))
      (fun r => r) (RefMap.shiftMany (N P) (saved (parentRef P)))
      (RefMap.shiftMany (N P) (saved (parentRef P)))
      (correctionPureTape _ _ _)⟩
  left_inv tape := by
    apply Prod.ext
    · funext i
      exact Equiv.symm_apply_apply _ _
    · exact (loweredTape_unique _ _ _ _ _ _ (correctionPureTape_unique _ _ _) tape.2).symm
  right_inv data := by
    funext i
    exact Equiv.apply_symm_apply _ _

/-- Chronological product of the exact main layer input carriers, ending in
all final child data. Each main carrier retains designated, auxiliary, source
residual, and residual-Gaussian coordinates. -/
def MainFinalTapeData (d : ℕ) : ℕ → Type
  | 0 => FinalTapeData P hR hc hsmall clock d
  | depth+1 => LayerInputs (c P hR hc hsmall clock)
      (p P hR hc hsmall clock) d × MainFinalTapeData d depth

def rawFinalTapeEquiv (d ell : ℕ) : (depth : ℕ) → {Δ : Ctx} →
    (old direct : Index P → Ref Δ .point) → (saved : RefMap (entryCtx P) Δ) →
    RawData (c P hR hc hsmall clock) (p P hR hc hsmall clock)
      (finish P hR hc hsmall clock ell) d depth old direct saved ≃
        MainFinalTapeData P hR hc hsmall clock d depth
  | 0, _, old, direct, saved => finishTapeEquiv P hR hc hsmall clock ell old direct saved
  | depth+1, _, _, direct, saved =>
      Equiv.prodCongr (Equiv.refl _)
        (rawFinalTapeEquiv d ell depth batchRef
          (fun i => preserveDirect (direct i)) (fun r => preserveDirect (saved r)))

def completeLoopTapeEquiv (d ell : ℕ) :
    Tape d (loop P hR hc hsmall clock ell) ≃
      MainFinalTapeData P hR hc hsmall clock d (P.K+4) :=
  (loopTapeEquiv P hR hc hsmall clock d ell).trans
    (rawFinalTapeEquiv P hR hc hsmall clock d ell (P.K+4)
      (oldRef P) (directRef P) (fun r => r))

/-- The pure assembly row contributes only forced unit coordinates. -/
def assemblyPureTape {d : ℕ} (i : Index P) :
    Tape d (MeanGaussianSetup.row (assemblySlot P hR hc hsmall clock)
      (ClockPublicSetup.saved P ClockPublicSetup.hRef) i) :=
  ⟨PUnit.unit, PUnit.unit, rowTape d []
    (List.ofFn fun j : Index P =>
      (assemblySlot P hR hc hsmall clock (matrixIndex (N P) i j),
        .there (.there (batchRef j)))) (fun r => r) .here⟩

theorem assemblyPureTape_unique {d : ℕ} (i : Index P)
    (tape : Tape d (MeanGaussianSetup.row (assemblySlot P hR hc hsmall clock)
      (ClockPublicSetup.saved P ClockPublicSetup.hRef) i)) :
    tape = assemblyPureTape P hR hc hsmall clock i := by
  rcases tape with ⟨⟨⟩, ⟨⟩, tail⟩
  exact congrArg (fun t => (PUnit.unit, PUnit.unit, t))
    (rowTape_unique [] _ (fun r => r) .here tail)

def assemblyTapeEquiv (d ell : ℕ) :
    Tape d (assembled P hR hc hsmall clock ell) ≃
      ((Index P → Point d) × Tape d (initialized P hR hc hsmall clock ell)) where
  toFun tape := ⟨(fun i => (tape.1 i).1), tape.2.2⟩
  invFun data := ⟨(fun i => (data.1 i, PUnit.unit)),
    (fun i => assemblyPureTape P hR hc hsmall clock i), data.2⟩
  left_inv tape := by
    rcases tape with ⟨draws, rows, tail⟩
    have hd : (fun i => ((draws i).1, PUnit.unit)) = draws := by
      funext i
      rcases draws i with ⟨z, ⟨⟩⟩
      rfl
    have hr : (fun i => assemblyPureTape P hR hc hsmall clock (d := d) i) = rows := by
      funext i
      exact (assemblyPureTape_unique P hR hc hsmall clock i (rows i)).symm
    change ((fun i => ((draws i).1, PUnit.unit)),
      (fun i => assemblyPureTape P hR hc hsmall clock i), tail) = (draws, rows, tail)
    rw [hd, hr]
    rfl
  right_inv data := rfl

def publicSplitTape {d : ℕ} (j : Fin 2) : Tape d (splitRow P hR hc hsmall clock j) :=
  lowerTape (oldSlot P hR hc hsmall clock) (ClockPublicSetup.splitRow P hR hc hsmall clock j)
    (fun r => r) (.there (.there .here)) (.there .here)
    (ClockPublicSetup.splitTape P hR hc hsmall clock d j)

def publicDirectTape {d : ℕ} (i : Index P) :
    Tape d (publicDirectRow P hR hc hsmall clock i) :=
  lowerTape (oldSlot P hR hc hsmall clock) (ClockPublicSetup.directRow P hR hc hsmall clock i)
    (fun r => r) ClockPublicSetup.xRef ClockPublicSetup.pRef
    (ClockPublicSetup.directTape P hR hc hsmall clock d i)

def publicPrefixTapeEquiv (d ell : ℕ) :
    Tape d (code P hR hc hsmall clock ell) ≃
      (Point d × Tape d (assembled P hR hc hsmall clock ell)) where
  toFun tape := ⟨tape.2.2.1, tape.2.2.2.2.2⟩
  invFun data := ⟨PUnit.unit, PUnit.unit, data.1,
    (fun j => publicSplitTape P hR hc hsmall clock j),
    (fun i => publicDirectTape P hR hc hsmall clock i), data.2⟩
  left_inv tape := by
    rcases tape with ⟨⟨⟩, ⟨⟩, E0, rows, direct, tail⟩
    have hr : rows = (fun j => publicSplitTape P hR hc hsmall clock (d := d) j) := by
      funext j
      exact loweredTape_unique _ _ _ _ _ _
        (ClockPublicSetup.splitTape_unique P hR hc hsmall clock j) (rows j)
    have hd : direct = (fun i => publicDirectTape P hR hc hsmall clock (d := d) i) := by
      funext i
      exact loweredTape_unique _ _ _ _ _ _
        (ClockPublicSetup.directTape_unique P hR hc hsmall clock i) (direct i)
    subst rows direct
    rfl
  right_inv data := rfl

/-- Complete whole-code coordinates: E0, raw assembly Z, separate center-init
Z0, every main designated/auxiliary/residual coordinate, and every final
auxiliary/residual coordinate. This is not a product-law statement. -/
abbrev WholeTapeData (d : ℕ) := Point d × ((Index P → Point d) ×
  ((Index P → Point d) × MainFinalTapeData P hR hc hsmall clock d (P.K+4)))

def wholeTapeEquiv (d ell : ℕ) :
    Tape d (code P hR hc hsmall clock ell) ≃ WholeTapeData P hR hc hsmall clock d :=
  (publicPrefixTapeEquiv P hR hc hsmall clock d ell).trans
    (Equiv.prodCongr (Equiv.refl _)
      ((assemblyTapeEquiv P hR hc hsmall clock d ell).trans
        (Equiv.prodCongr (Equiv.refl _)
          ((initialTapeEquiv
            (oldSlot P hR hc hsmall clock (ClockRepeatedLayers.rhoSlot P hR hc hsmall clock))
            (fun i => assemblySaved P (ClockPublicSetup.directRef P i)) []
            (ClockInitialLayer.initialOrigin P ell) (loop P hR hc hsmall clock ell)).trans
            (Equiv.prodCongr (Equiv.refl _) (completeLoopTapeEquiv P hR hc hsmall clock d ell))))))

def packWholeTape {d : ℕ} (ell : ℕ) (data : WholeTapeData P hR hc hsmall clock d) :
    Tape d (code P hR hc hsmall clock ell) :=
  (wholeTapeEquiv P hR hc hsmall clock d ell).symm data

def unpackWholeTape {d : ℕ} (ell : ℕ) (tape : Tape d (code P hR hc hsmall clock ell)) :
    WholeTapeData P hR hc hsmall clock d :=
  wholeTapeEquiv P hR hc hsmall clock d ell tape

theorem pack_unpackWholeTape {d : ℕ} (ell : ℕ)
    (tape : Tape d (code P hR hc hsmall clock ell)) :
    packWholeTape P hR hc hsmall clock ell (unpackWholeTape P hR hc hsmall clock ell tape) = tape :=
  Equiv.symm_apply_apply _ _

theorem unpack_packWholeTape {d : ℕ} (ell : ℕ)
    (data : WholeTapeData P hR hc hsmall clock d) :
    unpackWholeTape P hR hc hsmall clock ell (packWholeTape P hR hc hsmall clock ell data) = data :=
  Equiv.apply_symm_apply _ _

theorem width_pos (i : Index P) : 0 < width P clock i :=
  (FinalMeanScheduledData.root_positive P i clock).2

theorem coefficient_admissible : Conditional.GaussianAssembly.mass (coefficient P clock) < 1 :=
  ClockSchedule.admissible _ _ (ClockSchedule.sourceCells_pos P.delta_pos)
    (ClockSchedule.sourceOrder_pos P.K) clock

/-- No premise supplies the comparison reserve: it is calculated from H0,Z. -/
def reserveValue {d : ℕ} (H0 : Point d) (Z : Index P → Point d) : Point d :=
  Conditional.GaussianAssembly.residual (coefficient P clock) H0 Z

def activeValues {d : ℕ} (H0 : Point d) (Z : Index P → Point d) : Index P → Point d :=
  Conditional.GaussianAssembly.active (coefficient P clock) H0 Z

theorem reserve_literal {d : ℕ} (H0 : Point d) (Z : Index P → Point d) :
    reserveValue P clock H0 Z =
      Conditional.GaussianAssembly.reserve (coefficient P clock) • H0 +
        ∑ i, weight P clock i • Z i := by
  simp [reserveValue,Conditional.GaussianAssembly.residual,
    Conditional.GaussianAssembly.noiseSum,coefficient,Finset.sum_neg_distrib]

/-- The finite exact-real width division has an explicit nonzero proof. -/
theorem normalize_increment {d : ℕ} (a b : ℝ) (hb : b ≠ 0) (q z : Point d) :
    (a / b) • (q - b • z) = a • (b⁻¹ • q - z) := by
  simp only [smul_sub, smul_smul]
  rw [div_mul_cancel₀ a hb]
  rfl

/-- Literal executed correction versus the separately reconstructed reserve.
This is deterministic algebra on the same inputs, not a kernel identification. -/
theorem normalized_correction {d : ℕ} (H0 : Point d) (Z Q : Index P → Point d) :
    H0 + ∑ i, correctionWeight P clock i •
      (Q i - width P clock i • activeValues P clock H0 Z i) =
      (∑ i, coefficient P clock i • ((width P clock i)⁻¹ • Q i)) +
        Conditional.GaussianAssembly.reserve (coefficient P clock) • reserveValue P clock H0 Z := by
  simp only [correctionWeight]
  simp_rw [normalize_increment _ _ (ne_of_gt (width_pos P clock _))]
  have hr := Conditional.GaussianAssembly.residual_reconstruction
    (coefficient_admissible P clock) H0 Z
  change H0 = (∑ i, coefficient P clock i • activeValues P clock H0 Z i) +
    Conditional.GaussianAssembly.reserve (coefficient P clock) • reserveValue P clock H0 Z at hr
  simp only [smul_sub, Finset.sum_sub_distrib]
  nth_rw 1 [hr]
  abel

/-- Concrete assembly environment at the old public Ready store. -/
def assembledEnv {d : ℕ} (xF momentum E0 : Point d) (Z : Index P → Point d) : Env d (assembledCtx P) :=
  let H0 := ClockPublicSetup.splitValues momentum E0 1
  Env.prepend (activeValues P clock H0 Z)
    (Env.prepend Z (ClockPublicSetup.readyEnv P clock xF momentum E0))

def entryEnv {d : ℕ} (xF momentum E0 : Point d) (Z Z0 : Index P → Point d) : Env d (entryCtx P) :=
  Env.prepend (ClockRepeatedLayers.initialCenters P clock xF momentum E0 Z0)
    (Env.prepend Z0 (assembledEnv P clock xF momentum E0 Z))

theorem entry_designated {d : ℕ} (xF momentum E0 : Point d) (Z Z0 : Index P → Point d) (i : Index P) :
    storedPoint (entryEnv P clock xF momentum E0 Z Z0) (designatedRef P i) =
      activeValues P clock (ClockPublicSetup.splitValues momentum E0 1) Z i := by
  simp only [entryEnv,designatedRef,entrySaved,assembledEnv,storedPoint,prepend_shiftMany]
  exact prepend_batchRef _ _ i

theorem entry_parent {d : ℕ} (xF momentum E0 : Point d) (Z Z0 : Index P → Point d) :
    storedPoint (entryEnv P clock xF momentum E0 Z Z0) (parentRef P) =
      ClockPublicSetup.splitValues momentum E0 1 := by
  simp only [entryEnv,parentRef,entrySaved,assemblySaved,assembledEnv,storedPoint,prepend_shiftMany]
  exact (ClockPublicSetup.ready_saved P clock xF momentum E0 ClockPublicSetup.hRef).trans
    (ClockPublicSetup.split_h xF momentum E0)

/-- Every assembly tape, including pure row coordinates, gives the literal
signed positive-root active inputs; no caller supplies those values. -/
theorem run_assembled {d : ℕ} (ell : ℕ) (G : Point d → Point d) (xF momentum E0 : Point d)
    (tape : Tape d (assembled P hR hc hsmall clock ell)) :
    let Z : Index P → Point d := fun i => (tape.1 i).1
    let tail := run (initialized P hR hc hsmall clock ell) G
      ⟨table P hR hc hsmall clock,xF,momentum⟩ (assembledEnv P clock xF momentum E0 Z) tape.2.2
    run (assembled P hR hc hsmall clock ell) G ⟨table P hR hc hsmall clock,xF,momentum⟩
      (ClockPublicSetup.readyEnv P clock xF momentum E0) tape =
      ⟨tail.value,List.ofFn (fun i => Event.gaussian (assemblyOrigin P ell i)) ++ tail.trace⟩ := by
  have hh := MeanExecutablePrefix.run_setup (assemblySlot P hR hc hsmall clock)
    (ClockPublicSetup.saved P ClockPublicSetup.hRef) (assemblyOrigin P ell)
    (initialized P hR hc hsmall clock ell) G
    (⟨table P hR hc hsmall clock,xF,momentum⟩ : Inputs d (size P hR hc hsmall clock))
    (ClockPublicSetup.readyEnv P clock xF momentum E0) tape
  have hp := (ClockPublicSetup.ready_saved P clock xF momentum E0 ClockPublicSetup.hRef).trans
    (ClockPublicSetup.split_h xF momentum E0)
  simp only [hp] at hh
  have ha := funext (MeanExecutablePrefix.assemblyValues_eq_active
    (coefficient P clock) (coefficient_admissible P clock) (assemblySlot P hR hc hsmall clock)
    (⟨table P hR hc hsmall clock,xF,momentum⟩ : Inputs d (size P hR hc hsmall clock))
    (table_assembly P hR hc hsmall clock) (ClockPublicSetup.splitValues momentum E0 1)
    (fun i => (tape.1 i).1))
  rw [ha] at hh
  exact hh

def reached {d : ℕ} (ell : ℕ) (G : Point d → Point d) (xF momentum : Point d)
    (env : Env d (entryCtx P)) (tape : Tape d (loop P hR hc hsmall clock ell)) :=
  finalState (c P hR hc hsmall clock) (p P hR hc hsmall clock)
    (mainSlots P hR hc hsmall clock) (e P hR hc hsmall clock) (fun _ => [])
    (ClockRepeatedLayers.designated P (P.K+4)) (ClockRepeatedLayers.residual P (P.K+4))
    (ClockRepeatedLayers.auxiliary P hR hc hsmall clock (P.K+4))
    (finish P hR hc hsmall clock ell) G ⟨table P hR hc hsmall clock,xF,momentum⟩
    (P.K+4) (oldRef P) (directRef P) (fun r => r) env tape

/-- At the actual final state, the parent and each P_i are still those from
this exact public split and assembly, not arbitrary matching-marginal samples. -/
theorem reached_retained {d : ℕ} (ell : ℕ) (G : Point d → Point d)
    (xF momentum E0 : Point d) (Z Z0 : Index P → Point d)
    (tape : Tape d (loop P hR hc hsmall clock ell)) :
    let st := reached P hR hc hsmall clock ell G xF momentum
      (entryEnv P clock xF momentum E0 Z Z0) tape
    storedPoint st.env (st.saved (parentRef P)) = ClockPublicSetup.splitValues momentum E0 1 ∧
      ∀ i, storedPoint st.env (st.saved (designatedRef P i)) =
        activeValues P clock (ClockPublicSetup.splitValues momentum E0 1) Z i := by
  constructor
  · exact (loop_saved P hR hc hsmall clock ell G _ _ tape (parentRef P)).trans
      (entry_parent P clock xF momentum E0 Z Z0)
  · intro i
    exact (loop_saved P hR hc hsmall clock ell G _ _ tape (designatedRef P i)).trans
      (entry_designated P clock xF momentum E0 Z Z0 i)

def finalChildren {d : ℕ} (ell : ℕ) (G : Point d → Point d) (xF momentum : Point d)
    (env : Env d (entryCtx P)) (tape : Tape d (loop P hR hc hsmall clock ell)) : Index P → Result d .point :=
  let st := reached P hR hc hsmall clock ell G xF momentum env tape
  fun i => run (designatedChild (pf P hR hc hsmall clock i) (ef P hR hc hsmall clock i)
    (finalSlot P hR hc hsmall clock i) (st.old i) (st.saved (designatedRef P i))
    (finalAuxiliary P hR hc hsmall clock ell i)) G
    ⟨table P hR hc hsmall clock,xF,momentum⟩ st.env (st.tape.1 i)

def loopTrace {d : ℕ} (ell : ℕ) (G : Point d → Point d) (xF momentum : Point d)
    (env : Env d (entryCtx P)) (tape : Tape d (loop P hR hc hsmall clock ell)) : List (Event d) :=
  executionTrace (c P hR hc hsmall clock) (p P hR hc hsmall clock)
    (mainSlots P hR hc hsmall clock) (e P hR hc hsmall clock) (fun _ => [])
    (ClockRepeatedLayers.designated P (P.K+4)) (ClockRepeatedLayers.residual P (P.K+4))
    (ClockRepeatedLayers.auxiliary P hR hc hsmall clock (P.K+4))
    (finish P hR hc hsmall clock ell) G ⟨table P hR hc hsmall clock,xF,momentum⟩
    (P.K+4) (oldRef P) (directRef P) (fun r => r) env tape

/-- Every loop tape: actual final replies at actual stored centers, all main
and final traces, and the same retained H0 and active inputs from entry. -/
theorem run_loop {d : ℕ} (ell : ℕ) (G : Point d → Point d)
    (xF momentum E0 : Point d) (Z Z0 : Index P → Point d)
    (tape : Tape d (loop P hR hc hsmall clock ell)) :
    let env : Env d (entryCtx P) := entryEnv P clock xF momentum E0 Z Z0
    let Q := fun i => childPoint (finalChildren P hR hc hsmall clock ell G xF momentum env tape i)
    run (loop P hR hc hsmall clock ell) G ⟨table P hR hc hsmall clock,xF,momentum⟩ env tape =
      pointResult ((∑ i, coefficient P clock i • ((width P clock i)⁻¹ • Q i)) +
        Conditional.GaussianAssembly.reserve (coefficient P clock) •
          reserveValue P clock (ClockPublicSetup.splitValues momentum E0 1) Z)
        (loopTrace P hR hc hsmall clock ell G xF momentum env tape) := by
  let env : Env d (entryCtx P) := entryEnv P clock xF momentum E0 Z Z0
  let st := reached P hR hc hsmall clock ell G xF momentum env tape
  have hl := run_iterateThen_result (c P hR hc hsmall clock) (p P hR hc hsmall clock)
    (mainSlots P hR hc hsmall clock) (e P hR hc hsmall clock) (fun _ => [])
    (ClockRepeatedLayers.designated P (P.K+4)) (ClockRepeatedLayers.residual P (P.K+4))
    (ClockRepeatedLayers.auxiliary P hR hc hsmall clock (P.K+4))
    (finish P hR hc hsmall clock ell) G (⟨table P hR hc hsmall clock,xF,momentum⟩ : Inputs d _)
    (P.K+4) (oldRef P) (directRef P) (fun r => r) env tape
  have hf := run_finish P hR hc hsmall clock ell st.old st.direct st.saved G xF momentum st.env st.tape
  have hr := reached_retained P hR hc hsmall clock ell G xF momentum E0 Z Z0 tape
  change storedPoint st.env (st.saved (parentRef P)) = ClockPublicSetup.splitValues momentum E0 1 ∧
    ∀ i, storedPoint st.env (st.saved (designatedRef P i)) =
      activeValues P clock (ClockPublicSetup.splitValues momentum E0 1) Z i at hr
  dsimp only at hl hf ⊢
  change run (loop P hR hc hsmall clock ell) G _ env tape =
    ⟨(run (finish P hR hc hsmall clock ell st.old st.direct st.saved) G _ st.env st.tape).value,
      loopTrace P hR hc hsmall clock ell G xF momentum env tape⟩ at hl
  rw [hf] at hl
  simp only [pointResult,one_smul,hr.1,hr.2] at hl
  rw [normalized_correction P clock] at hl
  exact hl

/-- Every final auxiliary/residual tape runs the exact finalData program at
its stored center and retained input, not a replacement evaluator. -/
theorem run_finalChild {d : ℕ} {Δ : Ctx} (ell : ℕ) (i : Index P)
    (center active : Ref Δ .point) (G : Point d → Point d) (xF momentum : Point d) (env : Env d Δ)
    (tape : Tape d (designatedChild (pf P hR hc hsmall clock i) (ef P hR hc hsmall clock i)
      (finalSlot P hR hc hsmall clock i) center active (finalAuxiliary P hR hc hsmall clock ell i))) :
    let data := designatedTapeEquiv P hR hc hsmall clock ell i center active tape
    let source := run (pf P hR hc hsmall clock i) G
      ⟨(final P hR hc hsmall clock i).coefficient,storedPoint env center,storedPoint env active⟩ Env.empty
      (transformedSourceTape (pf P hR hc hsmall clock i) (ef P hR hc hsmall clock i)
        (finalRoot P hR hc hsmall clock i) data.1 data.2)
    run (designatedChild (pf P hR hc hsmall clock i) (ef P hR hc hsmall clock i)
      (finalSlot P hR hc hsmall clock i) center active (finalAuxiliary P hR hc hsmall clock ell i)) G
      ⟨table P hR hc hsmall clock,xF,momentum⟩ env tape =
      ⟨source.value,List.ofFn (fun j => Event.gaussian (finalAuxiliary P hR hc hsmall clock ell i j)) ++
        source.trace.filter keepNonGaussian⟩ :=
  run_designatedChild _ _ _ _ _ _ _ _ G ⟨table P hR hc hsmall clock,xF,momentum⟩ env
    (table_final P hR hc hsmall clock i) tape

private theorem run_lower_same {C C' d : ℕ} {Γ : Ctx} {τ : Ty}
    (κ : Fin C → Fin C') (p : Prog C Γ τ) (G : Point d → Point d)
    (input : Inputs d C') (env : Env d Γ) (center momentum : Ref Γ .point)
    (tape : Tape d (p.lower κ (fun r => r) center momentum)) :
    run (p.lower κ (fun r => r) center momentum) G input env tape =
      run p G ⟨input.coefficient ∘ κ,storedPoint env center,storedPoint env momentum⟩ env
        (restoreTape κ p (fun r => r) center momentum tape) := by
  calc
    _ = run (p.lower κ (fun r => r) center momentum) G input env
        (lowerTape κ p (fun r => r) center momentum
          (restoreTape κ p (fun r => r) center momentum tape)) :=
      congrArg (fun z => run (p.lower κ (fun r => r) center momentum) G input env z)
        (lowerTape_restoreTape κ p (fun r => r) center momentum tape).symm
    _ = _ := run_lower κ p G _ input (fun r => r) center momentum env env _
      (fun _ => rfl) (fun _ => rfl) rfl rfl

theorem run_splitRow {d : ℕ} (j : Fin 2) (G : Point d → Point d) (xF momentum E0 : Point d)
    (tape : Tape d (splitRow P hR hc hsmall clock j)) :
    run (splitRow P hR hc hsmall clock j) G ⟨table P hR hc hsmall clock,xF,momentum⟩
      (ClockPublicSetup.rawEnv xF momentum E0) tape =
      pointResult (ClockPublicSetup.splitValues momentum E0 j) [] := by
  unfold splitRow at tape ⊢
  rw [run_lower_same]
  have ht : table P hR hc hsmall clock ∘ oldSlot P hR hc hsmall clock =
      ClockPublicSetup.table P hR hc hsmall clock := funext (table_old P hR hc hsmall clock)
  simp only [ht]
  exact ClockPublicSetup.run_splitRow P hR hc hsmall clock j G xF momentum E0 _

theorem run_publicDirectRow {d : ℕ} (i : Index P) (G : Point d → Point d) (xF momentum E0 : Point d)
    (tape : Tape d (publicDirectRow P hR hc hsmall clock i)) :
    run (publicDirectRow P hR hc hsmall clock i) G ⟨table P hR hc hsmall clock,xF,momentum⟩
      (ClockPublicSetup.splitEnv xF momentum E0) tape =
      pointResult (b P clock xF (ClockPublicSetup.splitValues momentum E0 0) i) [] := by
  unfold publicDirectRow at tape ⊢
  rw [run_lower_same]
  have ht : table P hR hc hsmall clock ∘ oldSlot P hR hc hsmall clock =
      ClockPublicSetup.table P hR hc hsmall clock := funext (table_old P hR hc hsmall clock)
  simp only [ht,ClockPublicSetup.split_x,ClockPublicSetup.split_p]
  exact ClockPublicSetup.run_directRow P hR hc hsmall clock i G xF momentum E0 _

private theorem run_input_prefix {d C : ℕ} {τ : Ty} (next : Prog C ClockPublicSetup.rawCtx τ)
    (origin : Origin) (G : Point d → Point d) (input : Inputs d C) (E0 : Point d)
    (tail : Tape d next) :
    run (.step [] .center (.step [] .momentum (.step origin .gaussian next))) G input Env.empty
      (PUnit.unit,PUnit.unit,E0,tail) =
      let result := run next G input (ClockPublicSetup.rawEnv input.center input.momentum E0) tail
      (⟨result.value,Event.gaussian origin::result.trace⟩ : Result d τ) := rfl

private theorem run_public_skeleton {d C n : ℕ} {τ : Ty}
    (rows : Fin 2 → Prog C ClockPublicSetup.rawCtx .point)
    (directs : Fin n → Prog C ClockPublicSetup.splitCtx .point)
    (next : Prog C (replyCtx n ClockPublicSetup.splitCtx) τ)
    (origin : Origin) (G : Point d → Point d) (input : Inputs d C) (E0 : Point d)
    (values : Fin n → Point d) (rt : ∀ j, Tape d (rows j))
    (dt : ∀ i, Tape d (directs i)) (tail : Tape d next)
    (hr : ∀ j, run (rows j) G input (ClockPublicSetup.rawEnv input.center input.momentum E0) (rt j) =
      pointResult (ClockPublicSetup.splitValues input.momentum E0 j) [])
    (hd : ∀ i, run (directs i) G input (ClockPublicSetup.splitEnv input.center input.momentum E0) (dt i) =
      pointResult (values i) []) :
    run (.step [] .center (.step [] .momentum (.step origin .gaussian
      (.batch [] rows (.batch [] directs next))))) G input Env.empty
      (PUnit.unit,PUnit.unit,E0,rt,dt,tail) =
      let result := run next G input
        (Env.prepend values (ClockPublicSetup.splitEnv input.center input.momentum E0)) tail
      (⟨result.value,Event.gaussian origin::result.trace⟩ : Result d τ) := by
  have h1 := MeanExecutablePrefix.run_pureBatch rows (ClockPublicSetup.splitValues input.momentum E0)
    (.batch [] directs next) G input (ClockPublicSetup.rawEnv input.center input.momentum E0)
    (rt,dt,tail) hr
  have h2 := MeanExecutablePrefix.run_pureBatch directs values next G input
    (ClockPublicSetup.splitEnv input.center input.momentum E0) (dt,tail) hd
  change _ = run (.batch [] directs next) G input
    (ClockPublicSetup.splitEnv input.center input.momentum E0) (dt,tail) at h1
  rw [h2] at h1
  erw [run_input_prefix]
  exact congrArg (fun r : Result d τ => (⟨r.value,Event.gaussian origin::r.trace⟩ : Result d τ)) h1

/-- Every public prefix tape: reindexing changes no query, random value, or
stored input. The three initial instructions are literal center,momentum,E0. -/
theorem run_code_prefix {d : ℕ} (ell : ℕ) (G : Point d → Point d) (xF momentum : Point d)
    (tape : Tape d (code P hR hc hsmall clock ell)) :
    let E0 : Point d := tape.2.2.1
    let tail := run (assembled P hR hc hsmall clock ell) G
      ⟨table P hR hc hsmall clock,xF,momentum⟩
      (ClockPublicSetup.readyEnv P clock xF momentum E0) tape.2.2.2.2.2
    run (code P hR hc hsmall clock ell) G ⟨table P hR hc hsmall clock,xF,momentum⟩ Env.empty tape =
      ⟨tail.value,Event.gaussian (ClockPublicSetup.origin ell)::tail.trace⟩ := by
  rcases tape with ⟨⟨⟩,⟨⟩,E0,split,direct,tail⟩
  exact run_public_skeleton (splitRow P hR hc hsmall clock) (publicDirectRow P hR hc hsmall clock)
    (assembled P hR hc hsmall clock ell) (ClockPublicSetup.origin ell) G
    ⟨table P hR hc hsmall clock,xF,momentum⟩ E0
    (b P clock xF (ClockPublicSetup.splitValues momentum E0 0)) split direct tail
    (fun j => run_splitRow P hR hc hsmall clock j G xF momentum E0 (split j))
    (fun i => run_publicDirectRow P hR hc hsmall clock i G xF momentum E0 (direct i))

/-- One actual initialization, after the final designated inputs are stored. -/
theorem run_initialized {d : ℕ} (ell : ℕ) (G : Point d → Point d)
    (xF momentum E0 : Point d) (Z : Index P → Point d)
    (tape : Tape d (initialized P hR hc hsmall clock ell)) :
    let Z0 : Index P → Point d := fun i => (tape.1 i).1
    let tail := run (loop P hR hc hsmall clock ell) G ⟨table P hR hc hsmall clock,xF,momentum⟩
      (entryEnv P clock xF momentum E0 Z Z0) tape.2.2
    run (initialized P hR hc hsmall clock ell) G ⟨table P hR hc hsmall clock,xF,momentum⟩
      (assembledEnv P clock xF momentum E0 Z) tape =
      ⟨tail.value,List.ofFn (fun i => Event.gaussian (ClockInitialLayer.initialOrigin P ell i)) ++ tail.trace⟩ := by
  have hh := run_initialize
    (oldSlot P hR hc hsmall clock (ClockRepeatedLayers.rhoSlot P hR hc hsmall clock))
    (fun i => assemblySaved P (ClockPublicSetup.directRef P i)) [] (ClockInitialLayer.initialOrigin P ell)
    (loop P hR hc hsmall clock ell) G (⟨table P hR hc hsmall clock,xF,momentum⟩ : Inputs d _)
    (assembledEnv P clock xF momentum E0 Z) tape
  have ht : table P hR hc hsmall clock
      (oldSlot P hR hc hsmall clock (ClockRepeatedLayers.rhoSlot P hR hc hsmall clock)) = rhoC P :=
    (table_old P hR hc hsmall clock _).trans
      (ClockRepeatedLayers.table_rho P hR hc hsmall clock)
  have hd (i : Index P) : storedPoint (assembledEnv P clock xF momentum E0 Z)
      (assemblySaved P (ClockPublicSetup.directRef P i)) =
      b P clock xF (ClockPublicSetup.splitValues momentum E0 0) i := by
    simp only [assembledEnv,assemblySaved,storedPoint,prepend_shiftMany]
    exact ClockPublicSetup.ready_direct P clock xF momentum E0 i
  simp only [ht,hd,prefix_nil] at hh
  exact hh

/-- Complete source-facing every-tape Result. All supplied tape coordinates
survive in the typed child tapes; the trace is not an erased shape-only trace. -/
theorem run_code_every_tape {d : ℕ} (ell : ℕ) (G : Point d → Point d) (xF momentum : Point d)
    (tape : Tape d (code P hR hc hsmall clock ell)) :
    let E0 : Point d := tape.2.2.1
    let assemblyTape := tape.2.2.2.2.2
    let Z : Index P → Point d := fun i => (assemblyTape.1 i).1
    let initTape := assemblyTape.2.2
    let Z0 : Index P → Point d := fun i => (initTape.1 i).1
    let finalTape := initTape.2.2
    let env : Env d (entryCtx P) := entryEnv P clock xF momentum E0 Z Z0
    let Q := fun i => childPoint (finalChildren P hR hc hsmall clock ell G xF momentum env finalTape i)
    run (code P hR hc hsmall clock ell) G ⟨table P hR hc hsmall clock,xF,momentum⟩ Env.empty tape =
      pointResult ((∑ i, coefficient P clock i • ((width P clock i)⁻¹ • Q i)) +
        Conditional.GaussianAssembly.reserve (coefficient P clock) •
          reserveValue P clock (ClockPublicSetup.splitValues momentum E0 1) Z)
        (Event.gaussian (ClockPublicSetup.origin ell)::
          (List.ofFn (fun i => Event.gaussian (assemblyOrigin P ell i)) ++
            List.ofFn (fun i => Event.gaussian (ClockInitialLayer.initialOrigin P ell i)) ++
              loopTrace P hR hc hsmall clock ell G xF momentum env finalTape)) := by
  have hp := run_code_prefix P hR hc hsmall clock ell G xF momentum tape
  have ha := run_assembled P hR hc hsmall clock ell G xF momentum tape.2.2.1 tape.2.2.2.2.2
  have hi := run_initialized P hR hc hsmall clock ell G xF momentum tape.2.2.1
    (fun i => (tape.2.2.2.2.2.1 i).1) tape.2.2.2.2.2.2.2
  have hl := run_loop P hR hc hsmall clock ell G xF momentum tape.2.2.1
    (fun i => (tape.2.2.2.2.2.1 i).1) (fun i => (tape.2.2.2.2.2.2.2.1 i).1)
    tape.2.2.2.2.2.2.2.2.2
  dsimp only at hp ha hi hl ⊢
  rw [ha,hi,hl] at hp
  simpa only [pointResult,List.append_assoc] using hp

/-- All final children are paid, including a slot whose quadrature weight is zero. -/
theorem finish_count (ell : ℕ) (kind : EventKind) {Δ : Ctx}
    (old direct : Index P → Ref Δ .point) (saved : RefMap (entryCtx P) Δ) :
    syntaxCount kind (finish P hR hc hsmall clock ell old direct saved) =
      if kind = .gaussian then ∑ i, gf P hR hc hsmall clock i
      else ∑ i, syntaxCount kind (pf P hR hc hsmall clock i) := by
  simp only [finish,paidCorrection,syntaxCount,syntaxCount_designatedChild,
    syntaxCount_lower,RetainedMeanCorrection.syntaxCount_code,Nat.add_zero,Fin.sum_ofFn]
  cases kind <;> simp

theorem syntax_count (ell : ℕ) (kind : EventKind) :
    syntaxCount kind (code P hR hc hsmall clock ell) =
      (if kind = .gaussian then 1+2*N P else 0) +
      (P.K+4)*layerInventory kind (c P hR hc hsmall clock) (p P hR hc hsmall clock) +
      (if kind = .gaussian then ∑ i, gf P hR hc hsmall clock i
       else ∑ i, syntaxCount kind (pf P hR hc hsmall clock i)) := by
  unfold code
  simp only [syntaxCount,splitRow,publicDirectRow,syntaxCount_lower]
  have hs (j : Fin 2) : syntaxCount kind (ClockPublicSetup.splitRow P hR hc hsmall clock j) = 0 :=
    MeanGaussianSetup.syntaxCount_row _ _ _ _
  have hd (i : Index P) : syntaxCount kind (ClockPublicSetup.directRow P hR hc hsmall clock i) = 0 :=
    syntaxCount_affineRow _ _ _ _
  simp only [hs,hd,Fin.sum_ofFn,Finset.sum_const_zero,Nat.zero_add]
  unfold assembled
  rw [MeanGaussianSetup.syntaxCount_setup]
  unfold initialized
  rw [syntaxCount_initialize]
  unfold loop
  rw [syntaxCount_iterateThen _ _ _ _ _ _ _ _ _ _ _
    (fun old direct saved => finish_count P hR hc hsmall clock ell kind old direct saved)]
  cases kind <;> simp [instructionCount,Instr.eventKind]
  omega

theorem executed_count {d : ℕ} (ell : ℕ) (kind : EventKind) (G : Point d → Point d)
    (input : Inputs d (size P hR hc hsmall clock)) (tape : Tape d (code P hR hc hsmall clock ell)) :
    shapeCount kind ((run (code P hR hc hsmall clock ell) G input Env.empty tape).trace.map Event.erase) =
      (if kind = .gaussian then 1+2*N P else 0) +
      (P.K+4)*layerInventory kind (c P hR hc hsmall clock) (p P hR hc hsmall clock) +
      (if kind = .gaussian then ∑ i, gf P hR hc hsmall clock i
       else ∑ i, syntaxCount kind (pf P hR hc hsmall clock i)) := by
  rw [run_trace_shape,shapeCount_staticTrace,syntax_count]

/-- Final covariance identity is separate from mere constructor syntax and
requires the actual scheduled mass budget. It is not a tape-law statement. -/
theorem finalRoot_identity (hK : 10 ≤ P.K) (hC : 8 ≤ P.Csch)
    (hy : Oracle.CubicScheduleThreshold.threshold P ≤ P.y) (i : Index P) :
    (finalRoot P hR hc hsmall clock i).PosSemidef ∧
      finalRoot P hR hc hsmall clock i * (finalRoot P hR hc hsmall clock i).transpose =
        CovarianceSetup.childCovariance (rhoC P) (FinalMeanScheduledData.state P i clock).radius
          (final P hR hc hsmall clock i).shiftVector :=
  CovarianceSetup.child_root_identity _ (rhoC_pos P).le
    (FinalMeanScheduledData.root_positive P i clock).1 P.Ds_pos
    (FinalMeanScheduledData.final_queryShift_and_mass P hK hc hsmall hC hy i clock).2
    (ClockNoisyLayer.rhoC_le_radius P clock i)

/-- The sign bridge is an algebraic lemma, not a definitional identification
of our executable with a reference kernel. No child law enters this lemma. -/
theorem retained_sign_alignment {d m : ℕ} (D : RetainedLaw.Data (Fin d) m)
    (H0 : Point d) (Z Q : Fin m → Point d) :
    H0 + ∑ i, (-D.weight i) • (Q i - RetainedLaw.active D (H0,Z) i) =
      RetainedLaw.output D ((H0,Z),Q) := by
  have hi := RetainedLaw.innovation D ((H0,Z),Q)
  rw [← hi]
  abel

/-- Instantiation of the sign/normalization bridge at the actual clock weights.
Only the deterministic output map is identified. Its child kernels and their
laws are not identified with the compiled children by this statement. -/
theorem reference_output_alignment {d : ℕ} (D : RetainedLaw.Data (Fin d) (N P))
    (hweight : D.weight = weight P clock) (H0 : Point d) (Z Q : Index P → Point d) :
    H0 + ∑ i, correctionWeight P clock i •
      (Q i - width P clock i • activeValues P clock H0 Z i) =
      RetainedLaw.output D ((H0,Z), fun i => (width P clock i)⁻¹ • Q i) := by
  have ha : RetainedLaw.active D (H0,Z) = activeValues P clock H0 Z := by
    have hc : RetainedLaw.coefficient D = coefficient P clock := by
      funext i
      simp only [RetainedLaw.coefficient,coefficient,hweight]
    simp only [RetainedLaw.active,activeValues,hc]
  simp only [correctionWeight]
  simp_rw [normalize_increment _ _ (ne_of_gt (width_pos P clock _))]
  have hi := RetainedLaw.innovation D ((H0,Z), fun i => (width P clock i)⁻¹ • Q i)
  simp only [hweight,ha] at hi
  change H0 + (∑ i, (-weight P clock i) •
    ((width P clock i)⁻¹ • Q i - activeValues P clock H0 Z i)) = _
  rw [← hi]
  abel

/-- Explicit reserve reconstruction for the same H0 and raw Z. Not a draw. -/
theorem retained_reserve_reconstruction {d m : ℕ} (D : RetainedLaw.Data (Fin d) m)
    (H0 : Point d) (Z : Fin m → Point d) :
    RetainedLaw.recombine D (RetainedLaw.split D (H0,Z)) = H0 :=
  RetainedLaw.reconstruct D (H0,Z)

end AcceleratedLogConcave.Root.ClockRetainedFinalSplice
