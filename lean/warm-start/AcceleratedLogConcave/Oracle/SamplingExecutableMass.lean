import AcceleratedLogConcave.Oracle.ExecutableShiftMass
import AcceleratedLogConcave.Oracle.SourceExecutableShift
import AcceleratedLogConcave.Oracle.SamplingExecutable
import AcceleratedLogConcave.Oracle.RecursiveExecutableDomain

/-! Exact squared Gaussian-slot mass of the actual finite sampling program.
Every executed mean occurrence contributes its own raw auxiliary mass; held-fixed
designated/residual coordinates remain in the tape with zero shift weight. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.SamplingExecutableMass
open AffineLowering TapeLowering NoisyLayer RecursiveMeanContinuation
open ExecutableShiftWeights ExecutableShiftMass SourceExecutableShift
open CovarianceSetup LayerShift ChildAbsorption
open scoped BigOperators

local instance centerEmpty : IsEmpty (InstrGaussianSlot (Instr.center (c := C) (Γ := Γ))) :=
  ⟨fun s => nomatch s⟩
local instance pureEmpty (a : Pure C Γ σ) : IsEmpty (InstrGaussianSlot (Instr.pure a)) :=
  ⟨fun s => nomatch s⟩

private theorem gaussianMass (origin : Origin) (next : Prog C (.point :: Γ) τ)
    (a : ℝ) (tail : GaussianSlot next → ℝ) :
    slotMass (.step origin .gaussian next) (Sum.elim (fun _ => a) tail) =
      a^2 + slotMass next tail := by
  erw [slotMass_step]
  change (∑ _s : PUnit, a^2) + slotMass next tail = _
  rw [Fintype.sum_unique]

private theorem emptyStepMass (origin : Origin) (instr : Instr C Γ σ)
    [IsEmpty (InstrGaussianSlot instr)] (next : Prog C (σ :: Γ) τ)
    (head : InstrGaussianSlot instr → ℝ) (tail : GaussianSlot next → ℝ) :
    slotMass (.step origin instr next) (Sum.elim head tail) =
      slotMass next tail := by
  erw [slotMass_step]
  change (∑ s : InstrGaussianSlot instr, (head s)^2) + slotMass next tail = _
  rw [Fintype.sum_empty,zero_add]

variable {c cf : Fin n → ℕ} {p : ∀ i, Program (c i) .point}
  {pf : ∀ i, Program (cf i) .point}

/-- Exact final batch mass, including a separate explicit reserve weight. -/
theorem final_mass (cfg : PrivateSamplingProgram.Config n C c cf p pf)
    (old : Fin n → Ref Γ .point) (direct : Ref Γ .point)
    (final : ∀ i, Fin (tapeShape (pf i)).gaussianBlocks → ℝ) (reserve : ℝ) :
    slotMass (PrivateSamplingProgram.finish cfg old direct)
      (samplingFinal cfg old direct final reserve) =
      (∑ i, shiftSq (final i)) + reserve^2 := by
  unfold PrivateSamplingProgram.finish PrivateSamplingFinal.code samplingFinal
  erw [slotMass_batch]
  change (∑ i, slotMass
    (freshChild (pf i) (cfg.finalEquiv i) (cfg.finalSlots i) (old i)
      (cfg.finalDesignated i) (cfg.finalAuxiliary i))
    (freshWeights (pf i) (cfg.finalEquiv i) (cfg.finalSlots i) (old i)
      (cfg.finalDesignated i) (cfg.finalAuxiliary i) (final i))) + _ = _
  have hc : (∑ i, slotMass
    (freshChild (pf i) (cfg.finalEquiv i) (cfg.finalSlots i) (old i)
      (cfg.finalDesignated i) (cfg.finalAuxiliary i))
    (freshWeights (pf i) (cfg.finalEquiv i) (cfg.finalSlots i) (old i)
      (cfg.finalDesignated i) (cfg.finalAuxiliary i) (final i))) = ∑ i, shiftSq (final i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact freshWeights_mass (pf i) (cfg.finalEquiv i) (cfg.finalSlots i) (old i)
      (cfg.finalDesignated i) (cfg.finalAuxiliary i) (final i)
  rw [hc]
  congr 1
  erw [gaussianMass,gaussianMass]
  rw [slotMass_zero]
  ring

/-- Initial noises contribute zero; all finite main and final occurrences pay
exactly once in this literal shift-mass identity. -/
theorem body_mass (cfg : PrivateSamplingProgram.Config n C c cf p pf)
    (direct : Fin n → Ref Γ .point) (outputDirect : Ref Γ .point)
    (main : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (final : ∀ i, Fin (tapeShape (pf i)).gaussianBlocks → ℝ) (reserve : ℝ) :
    slotMass (PrivateSamplingProgram.body cfg direct outputDirect)
      (samplingBody cfg direct outputDirect main final reserve) =
      (cfg.layers:ℝ) * (∑ i, shiftSq (main i)) + (∑ i, shiftSq (final i)) + reserve^2 := by
  unfold PrivateSamplingProgram.body samplingBody
  erw [initializeWeights_mass]
  erw [iterateWeights_mass _ _ _ _ _ _ _ _ _ _ _ _
    (fun old _ saved => final_mass cfg old (saved outputDirect) final reserve)]
  ring

/-- The actual closed sampling program's squared shift mass. -/
theorem code_mass (cfg : PrivateSamplingProgram.Config n C c cf p pf)
    (position : ℝ) (main : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (final : ∀ i, Fin (tapeShape (pf i)).gaussianBlocks → ℝ) (reserve : ℝ) :
    slotMass (PrivateSamplingProgram.code cfg) (sampling cfg position main final reserve) =
      position^2 + reserve^2 + (cfg.layers:ℝ) * (∑ i, shiftSq (main i)) +
        (∑ i, shiftSq (final i)) := by
  unfold PrivateSamplingProgram.code sampling
  erw [emptyStepMass,gaussianMass,emptyStepMass,emptyStepMass,batchZero_mass,body_mass]
  ring

section Source
open Numerics.AffineGraph RecursiveExecutableDomain
variable (S : SamplingGeometry m) (e : Fin n ≃ S.Node) (r Ds : ℝ)
  (main final : Fin n → ExecutableData) (layers : ℕ)

/-- Exact actual-source mass, using the calculated raw auxiliary vectors. -/
theorem weights_mass (reserve : ℝ) :
    slotMass (SamplingExecutable.build S e r Ds main final layers).program
      (SamplingExecutable.weights S e r Ds main final layers reserve) =
      (samplingEnd S.τ)^2 + reserve^2 +
        (layers:ℝ) * (∑ i, shiftSq (SamplingExecutable.raw S e r Ds main i)) +
          ∑ i, shiftSq (SamplingExecutable.raw S e r Ds final i) := by
  simpa only [SamplingExecutable.weights,SamplingExecutable.build,
    SourceExecutableTables.samplingConfig,neg_sq] using
    code_mass (SourceExecutableTables.samplingConfig main final layers)
      (-(samplingEnd S.τ)) (SamplingExecutable.raw S e r Ds main)
      (SamplingExecutable.raw S e r Ds final) reserve

/-- Norm accounting for actual source auxiliary transformations, using only the
proved source ratio bounds and actual child covariance admissibility. -/
theorem weights_mass_le (reserve : ℝ) (hr : 0 < r)
    (hm : ∀ i, Admissible (SourceExecutableTables.samplingNoise S r Ds)
      (S.radius r (e i)) Ds (main i).shiftVector)
    (hf : ∀ i, Admissible (SourceExecutableTables.samplingNoise S r Ds)
      (S.radius r (e i)) Ds (final i).shiftVector) :
    slotMass (SamplingExecutable.build S e r Ds main final layers).program
      (SamplingExecutable.weights S e r Ds main final layers reserve) ≤
      (samplingEnd S.τ)^2 + reserve^2 + 36 *
        ((layers:ℝ) * (∑ i, shiftSq (main i).shiftVector) +
          ∑ i, shiftSq (final i).shiftVector) := by
  have hb (children : Fin n → ExecutableData)
      (hc : ∀ i, Admissible (SourceExecutableTables.samplingNoise S r Ds)
        (S.radius r (e i)) Ds (children i).shiftVector) :
      (∑ i, shiftSq (SamplingExecutable.raw S e r Ds children i)) ≤
        36 * ∑ i, shiftSq (children i).shiftVector := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact (shiftBounds (hc i) (sampling_shift_ratio S r hr (e i))).1
  rw [weights_mass]
  have hm' := mul_le_mul_of_nonneg_left (hb main hm) (Nat.cast_nonneg layers : (0:ℝ) ≤ layers)
  have hf' := hb final hf
  nlinarith

/-- Ordinary sampling stores the exact mass of its actual published shift. -/
theorem build_mass :
    shiftSq (SamplingExecutable.build S e r Ds main final layers).shiftVector =
      (samplingEnd S.τ)^2 +
        (layers:ℝ) * (∑ i, shiftSq (SamplingExecutable.raw S e r Ds main i)) +
          ∑ i, shiftSq (SamplingExecutable.raw S e r Ds final i) := by
  rw [shiftVector_mass]
  change slotMass (SamplingExecutable.build S e r Ds main final layers).program
    (SamplingExecutable.weights S e r Ds main final layers 0) = _
  rw [weights_mass]
  ring

/-- The containing mean's explicit private reserve costs at most five local
squared units, in addition to the actual transformed child occurrences. -/
theorem private_weights_mass_le (M : MeanGeometry order) (hr : 0 < r)
    (hm : ∀ i, Admissible (SourceExecutableTables.samplingNoise S r Ds)
      (S.radius r (e i)) Ds (main i).shiftVector)
    (hf : ∀ i, Admissible (SourceExecutableTables.samplingNoise S r Ds)
      (S.radius r (e i)) Ds (final i).shiftVector) :
    slotMass (SamplingExecutable.build S e r Ds main final layers).program
      (SamplingExecutable.weights S e r Ds main final layers (-2*M.R/backwardEnd M.R)) ≤
      5 + 36 * ((layers:ℝ) * (∑ i, shiftSq (main i).shiftVector) +
        ∑ i, shiftSq (final i).shiftVector) := by
  have h := weights_mass_le S e r Ds main final layers (-2*M.R/backwardEnd M.R) hr hm hf
  have hl := private_local_shift_mass_le_five M S
  rw [neg_sq] at hl
  linarith

end Source

end AcceleratedLogConcave.Oracle.SamplingExecutableMass
