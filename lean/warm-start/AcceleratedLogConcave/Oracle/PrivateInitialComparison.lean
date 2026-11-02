import AcceleratedLogConcave.Oracle.PrivateSamplingFlowResidual
import AcceleratedLogConcave.Oracle.PrivateCompletedPrefixDraws

/-! The initial comparison vector and coarse position are literal distinct
Gaussian occurrences of the complete private tape. No assertion is made that
the entire mixed tape is Gaussian or independent of these coordinates. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.PrivateInitialComparison
open AffineLowering TapeLowering NoisyLayer RecursiveMeanProgram
  RecursiveMeanContinuation SourceMeanLayer PrivateSamplingProgram
  CanonicalTapeLaw CanonicalTapeMeasurability
variable {n C d : ℕ} {c cf : Fin n → ℕ}
  {p : ∀ i, Program (c i) .point} {pf : ∀ i, Program (cf i) .point}
  (cfg : Config n C c cf p pf)

abbrev Index (n : ℕ) := Unit ⊕ Fin n

def slot : Index n → GaussianSlot (code cfg)
  | .inl _ => .inr (.inl PUnit.unit)
  | .inr i => .inr (.inr (.inr (.inr (.inr (.inl ⟨i,.inl PUnit.unit⟩)))))

theorem slot_injective : Function.Injective (slot cfg) := by
  intro i j h
  cases i with
  | inl i => cases j with
    | inl j => exact congrArg Sum.inl (Subsingleton.elim _ _)
    | inr j => cases h
  | inr i => cases j with
    | inl j => cases h
    | inr j =>
      have h' := Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj
        (Sum.inr.inj (Sum.inr.inj h)))))
      exact congrArg Sum.inr (congrArg Sigma.fst h')

def coordinates (ω : Tape d (code cfg)) : Index n → Point d :=
  fun i => (splitTape (code cfg) ω).1 (slot cfg i)

@[simp] theorem position_eq (ω : Tape d (code cfg)) :
    coordinates cfg ω (.inl ()) = ω.2.1 := rfl

@[simp] theorem initial_eq (ω : Tape d (code cfg)) (i : Fin n) :
    coordinates cfg ω (.inr i) = (ω.2.2.2.2.2.1 i).1 := rfl

theorem coordinates_preserving (L : PrimitiveLaws d)
    (hL : L.pointDraw = stdGaussian (Point d)) :
    let : MeasurableSpace (Tape d (code cfg)) := tapeSpace d _
    MeasurePreserving (coordinates cfg) (tapeLaw L (code cfg))
      (Measure.pi (fun _ : Index n => stdGaussian (Point d))) := by
  let : MeasurableSpace (Tape d (code cfg)) := tapeSpace d _
  have hm : Measurable (fun z : GaussianSlot (code cfg) → Point d =>
      fun j => z (slot cfg j)) := by fun_prop
  refine ⟨hm.comp (measurable_splitTape d (code cfg)).fst, ?_⟩
  change Measure.map ((fun z j => z (slot cfg j)) ∘
    (fun ω => (splitTape (code cfg) ω).1)) _ = _
  rw [← Measure.map_map hm (measurable_splitTape d (code cfg)).fst,
    CanonicalTapeFactorization.map_gaussian_tapeLaw, hL]
  exact PrivateSamplingTapeProjections.pi_selection _ _ (slot_injective cfg)

/-- Joint initial benchmark law conditional on its correct coarse host ζ.
This retains all other tape coordinates in the source of the pushforward. -/
theorem joint_preserving (L : PrimitiveLaws d)
    (hL : L.pointDraw = stdGaussian (Point d)) :
    let : MeasurableSpace (Tape d (code cfg)) := tapeSpace d _
    MeasurePreserving (fun ω : Tape d (code cfg) =>
      ((show Point d from ω.2.1), fun i : Fin n => (show Point d from (ω.2.2.2.2.2.1 i).1)))
      (tapeLaw L (code cfg))
      ((stdGaussian (Point d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (Point d)))) := by
  let : MeasurableSpace (Tape d (code cfg)) := tapeSpace d _
  have hsum := measurePreserving_sumPiEquivProdPi
    (fun _ : Index n => stdGaussian (Point d))
  have heval := (measurePreserving_eval (fun _ : Unit => stdGaussian (Point d)) ()).prod
    (MeasurePreserving.id (Measure.pi (fun _ : Fin n => stdGaussian (Point d))))
  exact heval.comp (hsum.comp (coordinates_preserving cfg L hL))

section ActualPrefix
open Numerics.AffineGraph TailOccurrenceCut TailCut PrivateGeneralOccurrence
variable {m : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
  (r Ds : ℝ) (main final : Fin n → ExecutableData) (N k : ℕ) (hk : k<N)
local notation "cut" => (GeneralMainFocus.Focus.cut (privateFocus S e r Ds main final N k hk))
local notation "H" => Prefix d cut

/-- The same joint law on the actual consumed prefix. In particular k=0
supplies the finite chronological construction's base comparison vector. -/
theorem prefix_joint_preserving (L : PrimitiveLaws d)
    (hL : L.pointDraw = stdGaussian (Point d)) :
    let : MeasurableSpace H := prefixSpace d cut
    MeasurePreserving (fun h : H =>
      (PrivateCompletedPrefixDraws.zeta S e r Ds main final N k hk h,
       fun i => PrivateCompletedPrefixDraws.eta S e r Ds main final N k hk i h))
      (prefixLaw L cut)
      ((stdGaussian (Point d)).prod (Measure.pi (fun _ : Fin n => stdGaussian (Point d)))) := by
  let : MeasurableSpace H := prefixSpace d cut
  let : MeasurableSpace (Tape d (SamplingExecutable.build S e r Ds main final N).program) := tapeSpace d _
  let q := (RecursiveMeanContinuation.iterateThen (fun i => (main i).size) (fun i => (main i).program)
      (PrivateSamplingProgram.Config.mainSlots (SourceExecutableTables.samplingConfig main final N))
      (fun i => (main i).enumeration)
      (PrivateSamplingProgram.Config.layerOrigin (SourceExecutableTables.samplingConfig main final N))
      (PrivateSamplingProgram.Config.mainDesignated (SourceExecutableTables.samplingConfig main final N))
      (PrivateSamplingProgram.Config.mainResidual (SourceExecutableTables.samplingConfig main final N))
      (PrivateSamplingProgram.Config.mainAuxiliary (SourceExecutableTables.samplingConfig main final N))
      (PrivateSamplingExecutionSchedule.finisher main final N)
      ((privateFocus S e r Ds main final N k hk).remainingAfter+1)
      (privateFocus S e r Ds main final N k hk).old
      (privateFocus S e r Ds main final N k hk).direct
      (privateFocus S e r Ds main final N k hk).saved)
  let : MeasurableSpace (Tape d q) := tapeSpace d q
  have hsplit := measurePreserving_split L cut
  let := tapeLaw_probability L q
  have hpref := measurePreserving_fst.comp hsplit
  have hm := (PrivateCompletedPrefixDraws.measurable_zeta (d := d) S e r Ds main final N k hk).prodMk
    (measurable_pi_iff.mpr fun i => PrivateCompletedPrefixDraws.measurable_eta (d := d) S e r Ds main final N k hk i)
  refine ⟨hm, ?_⟩
  rw [← hpref.map_eq, Measure.map_map hm hpref.measurable]
  let : MeasurableSpace (Tape d (code (SourceExecutableTables.samplingConfig main final N))) := tapeSpace d _
  exact (joint_preserving (SourceExecutableTables.samplingConfig main final N) L hL).map_eq
end ActualPrefix

end AcceleratedLogConcave.Oracle.PrivateInitialComparison
