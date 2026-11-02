import AcceleratedLogConcave.Oracle.PrivateSamplingTapeProjections
import AcceleratedLogConcave.Oracle.PrivateSamplingNoiseBudget
import AcceleratedLogConcave.Oracle.RecursiveExecutable

/-! The literal private sampler in the first nonterminal precision band. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.PrivateSamplingFirstBandOutput
open Numerics.AffineGraph SourceExecutableTables TapeLowering NoisyLayer AffineLowering
open PrivateSamplingTapeProjections
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
theorem terminal_fresh_value {d C N : ℕ} {Γ : Ctx} (origin : Origin)
    (e : GaussianSlot (terminalMeanProgram origin) ≃ Fin N)
    (slots : Fin (N*N+3) → Fin C) (old : Ref Γ .point)
    (designated : Origin) (auxiliary : Fin N → Origin)
    (T : Fin N → Fin N → ℝ) (scale r σ : ℝ)
    (G : Point d → Point d) (input : Inputs d C) (env : Env d Γ)
    (ht : input.coefficient ∘ slots = matrixTable T (TerminalMeanShift.coefficients scale r σ))
    (ω : Tape d (freshChild (terminalMeanProgram origin) e slots old designated auxiliary)) :
    let data := freshChildTapeEquiv (terminalMeanProgram origin) e slots old designated auxiliary ω
    (run (freshChild (terminalMeanProgram origin) e slots old designated auxiliary)
      G input env ω).value =
      scale • G (scale • (storedPoint env old + r •
        transformedGaussian T data.2.1 (e (TerminalMeanShift.auxiliarySlot origin)))) + σ • data.1 := by
  have h := congrArg Result.value (run_freshChild (terminalMeanProgram origin) e slots old
    designated auxiliary T (TerminalMeanShift.coefficients scale r σ) G input env ht ω)
  dsimp only [transformedSourceTape] at h
  rw [TerminalMeanShift.run_joinTape] at h
  exact h

variable {m n d : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
  (r Ds scale : ℝ) (layers : ℕ)

abbrev main (i : Fin n) := RecursiveExecutable.terminal scale (S.radius r (e i))
  (RecursiveMeanPublicTable.mainWidth n r S.R Ds (r^2))
abbrev final (i : Fin n) := RecursiveExecutable.terminal scale (S.radius r (e i))
  (samplingFinalWidth S r)
abbrev executable := SamplingExecutable.build S e r Ds (main S e r Ds scale)
  (final S e r scale) layers
abbrev config := samplingConfig (main S e r Ds scale) (final S e r scale) layers

/-- The recursive supplier reduces to these exact children, including all widths. -/
theorem literal_private_eq {order nodesN anchorsN seedsN : ℕ}
    (M : MeanGeometry order) (nodes : Fin nodesN ≃ M.MeanNode)
    (anchors : Fin anchorsN ≃ M.Anchor) (seeds : Fin seedsN ≃ Fin order × M.Kernel)
    (δ t w q : ℝ) (ht : 0 < t) (htq : t ≤ 1/4)
    (_hq : 1/2 < q) (hband : q ≤ 1/2+t) :
    SamplingExecutable.build S e r Ds
      (fun i => RecursiveExecutable.meanCore M nodes anchors seeds S e Ds δ t w layers ht htq
        scale (S.radius r (e i)) (RecursiveMeanPublicTable.mainWidth n r S.R Ds (r^2)) (q-1/4))
      (fun i => RecursiveExecutable.meanCore M nodes anchors seeds S e Ds δ t w layers ht htq
        scale (S.radius r (e i)) (samplingFinalWidth S r) (q-1/4)) layers =
      executable S e r Ds scale layers := by
  have h : q-1/4 ≤ 1/2 := by linarith
  simp only [RecursiveExecutable.mean_terminal M nodes anchors seeds S e Ds δ t w ht htq layers
    _ _ _ _ h, executable]

abbrev input (x P : Point d) : Inputs d (executable S e r Ds scale layers).size :=
  ⟨(executable S e r Ds scale layers).coefficient, x, P⟩

def transformedAuxiliary (G : Point d → Point d) (x P : Point d)
    (ω : Tape d (executable S e r Ds scale layers).program) (i : Fin n) : Point d :=
  let cfg := config S e r Ds scale layers
  let data := finalData cfg G (input S e r Ds scale layers x P) ω i
  let T := CovarianceSetup.childRoot (samplingNoise S r Ds) (S.radius r (e i))
    (final S e r scale i).shiftVector
  transformedGaussian T data.2.1
    ((final S e r scale i).enumeration (TerminalMeanShift.auxiliarySlot [⟨.mean,.setup,0,0,0⟩]))

def gradientReply (G : Point d → Point d) (x P : Point d)
    (ω : Tape d (executable S e r Ds scale layers).program) (i : Fin n) : Point d :=
  let st := state (config S e r Ds scale layers) G (input S e r Ds scale layers x P) ω
  scale • G (scale • (storedPoint st.env (st.old i) +
    S.radius r (e i) • transformedAuxiliary S e r Ds scale layers G x P ω i))

theorem final_value_eq (G : Point d → Point d) (x P : Point d)
    (ω : Tape d (executable S e r Ds scale layers).program) (i : Fin n) :
    finalValue (config S e r Ds scale layers) G (input S e r Ds scale layers x P) ω i =
      gradientReply S e r Ds scale layers G x P ω i +
        samplingFinalWidth S r • coordinates (config S e r Ds scale layers) ω (.inr (.inl i)) := by
  let cfg := config S e r Ds scale layers
  let inp := input S e r Ds scale layers x P
  let st := state cfg G inp ω
  have htable : inp.coefficient ∘ cfg.finalSlots i =
      matrixTable (CovarianceSetup.childRoot (samplingNoise S r Ds) (S.radius r (e i))
        (final S e r scale i).shiftVector) (final S e r scale i).coefficient := by
    funext j
    exact samplingTable_final S e r Ds (main S e r Ds scale) (final S e r scale) i j
  rw [designated_eq (config S e r Ds scale layers) G (input S e r Ds scale layers x P) ω i]
  exact terminal_fresh_value [⟨.mean,.setup,0,0,0⟩] (cfg.finalEquiv i) (cfg.finalSlots i)
    (st.old i) (cfg.finalDesignated i) (cfg.finalAuxiliary i)
    (CovarianceSetup.childRoot (samplingNoise S r Ds) (S.radius r (e i))
      (final S e r scale i).shiftVector) scale (S.radius r (e i)) (samplingFinalWidth S r)
    G inp st.env htable (st.tape.1 i)

def noise (ω : Tape d (executable S e r Ds scale layers).program) : Point d :=
  let z := coordinates (config S e r Ds scale layers) ω
  (∑ i, (samplingFinalWeight S e r i * samplingFinalWidth S r) • z (.inr (.inl i))) +
    samplingBeta S e r • z (.inr (.inr (.inl ()))) +
    (S.τ/2) • z (.inr (.inr (.inr ())))

theorem output_eq (G : Point d → Point d) (x P : Point d)
    (ω : Tape d (executable S e r Ds scale layers).program) :
    (run (executable S e r Ds scale layers).program G (input S e r Ds scale layers x P)
      Env.empty ω).value =
      (samplingEnd S.τ)⁻¹ • coordinates (config S e r Ds scale layers) ω (.inl ()) +
      (∑ i, samplingFinalWeight S e r i • gradientReply S e r Ds scale layers G x P ω i) +
      noise S e r Ds scale layers ω := by
  have hinv : (input S e r Ds scale layers x P).coefficient
      (config S e r Ds scale layers).invEnd = (samplingEnd S.τ)⁻¹ := by
    change samplingTable S e r Ds (main S e r Ds scale) (final S e r scale)
      (scalarSlot _ _ (Fin.natAdd _ (Fin.natAdd _ (1 : Fin 4)))) = _
    simp [samplingTable_scalar, samplingScalarTable]
  have hrow (i : Fin n) : (input S e r Ds scale layers x P).coefficient
      ((config S e r Ds scale layers).rowWeight i) = samplingFinalWeight S e r i := by
    change samplingTable S e r Ds (main S e r Ds scale) (final S e r scale)
      (scalarSlot _ _ (Fin.natAdd _ (Fin.castAdd _ i))) = _
    simp [samplingTable_scalar, samplingScalarTable]
  have hbeta : (input S e r Ds scale layers x P).coefficient
      (config S e r Ds scale layers).beta = samplingBeta S e r := by
    change samplingTable S e r Ds (main S e r Ds scale) (final S e r scale)
      (scalarSlot _ _ (Fin.natAdd _ (Fin.natAdd _ (2 : Fin 4)))) = _
    simp [samplingTable_scalar, samplingScalarTable]
  have hreserve : (input S e r Ds scale layers x P).coefficient
      (config S e r Ds scale layers).reserve = S.τ/2 := by
    change samplingTable S e r Ds (main S e r Ds scale) (final S e r scale)
      (scalarSlot _ _ (Fin.natAdd _ (Fin.natAdd _ (3 : Fin 4)))) = _
    simp [samplingTable_scalar, samplingScalarTable]
  exact run_code_affine (config S e r Ds scale layers) G
    (input S e r Ds scale layers x P) ω ((samplingEnd S.τ)⁻¹) (samplingBeta S e r)
    (S.τ/2) (samplingFinalWidth S r) (samplingFinalWeight S e r)
    (gradientReply S e r Ds scale layers G x P ω) hinv hbeta hreserve hrow
    (final_value_eq S e r Ds scale layers G x P ω)

end AcceleratedLogConcave.Oracle.PrivateSamplingFirstBandOutput
