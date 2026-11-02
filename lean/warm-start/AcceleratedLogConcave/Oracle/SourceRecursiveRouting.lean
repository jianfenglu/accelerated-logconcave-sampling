import AcceleratedLogConcave.Oracle.RecursiveMeanPublicTable
import AcceleratedLogConcave.Oracle.NonterminalMeanValue

/-! Exact routed coefficients for the source retained mean table. These
identities discharge the table premises of the existing Result/value theorems;
they do not assert a recursive child selection or a probabilistic tape law. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.SourceRecursiveRouting
open AffineLowering TapeLowering NoisyLayer RecursiveMeanPublicTable

 theorem correction_table (rho : ℝ) (layer : Fin L → ℝ) (final : Fin F → ℝ)
    (sigma : ℝ) (omega width : Fin m → ℝ) :
    table rho layer final sigma omega width ∘ correctionSlot =
      RetainedMeanCorrection.table sigma omega width := by
  funext j
  exact table_correction rho layer final sigma omega width j

 theorem main_table (rho : ℝ) (layer : Fin L → ℝ) (final : Fin F → ℝ)
    (sigma : ℝ) (omega width : Fin m → ℝ) :
    table rho layer final sigma omega width ∘ layerSlot = layer := by
  funext j
  exact table_layer rho layer final sigma omega width j

 theorem final_child_table (rho : ℝ) (layer : Fin L → ℝ)
    (cf : Fin m → ℕ) (pf : ∀ i, Program (cf i) .point)
    (r R Ds sigma : ℝ)
    (shift : ∀ i, Fin (tapeShape (pf i)).gaussianBlocks → ℝ)
    (coeff : ∀ i, Fin (cf i) → ℝ) (omega width : Fin m → ℝ) (i : Fin m) :
    table rho layer (sourceFinalTable cf pf r R Ds shift coeff) sigma omega width ∘
      (activeFinalSlot ∘ finalSlot cf pf i) =
      matrixTable (CovarianceSetup.childRoot (centerNoise r R Ds) (r*R) (shift i))
        (coeff i) := by
  funext j
  simp only [Function.comp_apply, table_final]
  exact finalTable_child cf pf _ coeff i j

 theorem main_child_table (rho : ℝ) (final : Fin F → ℝ)
    (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (A : CovarianceSetup.Mat n) (r R Ds rowBound sigma : ℝ)
    (radius : Fin n → ℝ)
    (shift : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (coeff : ∀ i, Fin (c i) → ℝ) (omega width : Fin m → ℝ) (i : Fin n) :
    table rho (sourceLayerTable c p A r R Ds rowBound radius shift coeff)
      final sigma omega width ∘ (layerSlot ∘ childSlot c p i) =
      matrixTable (CovarianceSetup.childRoot (centerNoise r R Ds) (radius i) (shift i))
        (coeff i) := by
  funext j
  simp only [Function.comp_apply, table_layer]
  exact layerTable_child c p A (CovarianceSetup.residualRoot A (centerNoise r R Ds) rowBound)
    (fun j => CovarianceSetup.childRoot (centerNoise r R Ds) (radius j) (shift j)) coeff i j

/-- The scalar width in the compiler table is precisely the reference child's
physical width, not a main-layer surrogate. -/
theorem finalWidth_eq (R sigma : ℝ) :
    finalWidth R sigma = R * Real.sqrt 3 * sigma / 4 := by
  unfold finalWidth finalNoise
  ring

/-- Specialize Mathy's full final Result theorem to the literal public table.
The correction routing premise is proved here; every child tape and trace is
still the one read by the interpreter. No trace equality is inferred from a
value-only theorem. -/
theorem run_paidCorrection_sourceTable (cf : Fin m → ℕ)
    (pf : ∀ i, Program (cf i) .point)
    (e : ∀ i, GaussianSlot (pf i) ≃ Fin (tapeShape (pf i)).gaussianBlocks)
    (rho : ℝ) (layer : Fin L → ℝ) (final : Fin F → ℝ)
    (sigma : ℝ) (omega width : Fin m → ℝ)
    (slots : ∀ i, Fin (childSize (pf i)) → Fin (1+(L+(F+(1+(m+m))))))
    (P : Ref Γ .point) (center designated : Fin m → Ref Γ .point)
    (outer : Origin)
    (auxiliary : ∀ i, Fin (tapeShape (pf i)).gaussianBlocks → Origin)
    (G : Point d → Point d) (hostCenter hostMomentum : Point d) (env : Env d Γ)
    (tape : Tape d (RetainedMeanFinalBatch.paidCorrection cf pf e slots correctionSlot
      P center designated outer auxiliary)) :
    let input : Inputs d (1+(L+(F+(1+(m+m))))) :=
      ⟨table rho layer final sigma omega width, hostCenter, hostMomentum⟩
    let children := fun i => run
      (RetainedMeanFinalBatch.designatedChild (pf i) (e i) (slots i)
        (center i) (designated i) (auxiliary i)) G input env (tape.1 i)
    run (RetainedMeanFinalBatch.paidCorrection cf pf e slots correctionSlot
      P center designated outer auxiliary) G input env tape =
      pointResult (sigma • storedPoint env P + ∑ i, omega i •
        (RetainedMeanFinalBatch.childPoint (children i) - width i • storedPoint env (designated i)))
        (((List.ofFn fun i => (children i).trace).flatten).map (Event.withPrefix outer)) := by
  exact RetainedMeanFinalBatch.run_paidCorrection cf pf e slots correctionSlot
    P center designated outer auxiliary sigma omega width G _ env
    (correction_table rho layer final sigma omega width) tape

end AcceleratedLogConcave.Oracle.SourceRecursiveRouting
