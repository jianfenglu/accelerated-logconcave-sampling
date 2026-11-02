import AcceleratedLogConcave.Oracle.CompletedPrefixDraws
import AcceleratedLogConcave.Oracle.PrivateGeneralOccurrence

/-! Concrete PRIVATE setup/completed-layer projections and conditional
benchmark assembly. Actual-flow reference identification remains separate. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.PrivateCompletedPrefixDraws
open CanonicalTapeLaw
open MeasureTheory Numerics Numerics.AffineGraph CovarianceSetup
open AffineLowering TapeLowering NoisyLayer SourceMeanLayer
open RecursiveMeanProgram RecursiveMeanContinuation PrivateSamplingProgram
open SourceExecutableTables PrivateSamplingExecutionSchedule
open TailOccurrenceCut TailOccurrenceCut.TailCut CanonicalTapeMeasurability
open PrivateGeneralOccurrence
open scoped BigOperators
variable {m n d : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
    (r Ds : ℝ) (main final : Fin n → ExecutableData) (N k : ℕ) (hk : k<N)
local notation "cfg" => samplingConfig main final N
local notation "c" => (fun i : Fin n => ExecutableData.size (main i))
local notation "p" => (fun i : Fin n => ExecutableData.program (main i))
local notation "en" => (fun i : Fin n => ExecutableData.enumeration (main i))
local notation "F" => finisher main final N
local notation "foc" => privateFocus S e r Ds main final N k hk
local notation "cut" => (GeneralMainFocus.Focus.cut foc)
local notation "H" => Prefix d cut
local notation "dir" => (fun i => RefMap.shiftMany n (RefMap.shiftMany n (batchRef i)))
local notation "saved" => (fun q => RefMap.shiftMany n (RefMap.shiftMany n q))

def zeta (h : H) : Point d := h.2.1
def eta (i : Fin n) (h : H) : Point d := (h.2.2.2.2.2.1 i).1

/-- Seven setup nodes are skipped; all query coordinates still lie strictly
inside the consumed-loop prefix, before the current selected child batch. -/
def past (j : ℕ) (hj : j<k) (h : H) : (Fin n → Point d) × (Fin n → Point d) :=
  CompletedPrefixDraws.completed c p (PrivateSamplingProgram.Config.mainSlots cfg) en (PrivateSamplingProgram.Config.layerOrigin cfg) (PrivateSamplingProgram.Config.mainDesignated cfg)
    (PrivateSamplingProgram.Config.mainResidual cfg) (PrivateSamplingProgram.Config.mainAuxiliary cfg) F N k hk batchRef dir saved j hj
    h.2.2.2.2.2.2.2

theorem measurable_zeta : @Measurable H _ (prefixSpace d cut) _ (zeta S e r Ds main final N k hk) :=
  measurable_snd.fst

theorem measurable_eta (i : Fin n) :
    @Measurable H _ (prefixSpace d cut) _ (eta S e r Ds main final N k hk i) :=
by
  let : MeasurableSpace H := prefixSpace d cut
  let : ∀ j : Fin n, MeasurableSpace (Tape d
      (residualDraw ((PrivateSamplingProgram.Config.initialOrigin cfg) j) :
        Prog (samplingSize main final) (replyCtx n [.point,.scalar,.point,.point]) .point)) :=
    fun j => tapeSpace d _
  exact ((measurable_pi_apply i).comp measurable_snd.snd.snd.snd.snd.fst).fst

theorem measurable_past (j : ℕ) (hj : j<k) :
    @Measurable H _ (prefixSpace d cut) _ (past S e r Ds main final N k hk j hj) :=
  (CompletedPrefixDraws.measurable_completed c p (PrivateSamplingProgram.Config.mainSlots cfg) en (PrivateSamplingProgram.Config.layerOrigin cfg) (PrivateSamplingProgram.Config.mainDesignated cfg)
    (PrivateSamplingProgram.Config.mainResidual cfg) (PrivateSamplingProgram.Config.mainAuxiliary cfg) F N k hk batchRef dir saved j hj).comp
    measurable_snd.snd.snd.snd.snd.snd.snd

theorem past_eq_actual (j : ℕ) (hj : j<k)
    (ω : FullTape (d := d) S e r Ds main final N) :
    past S e r Ds main final N k hk j hj (split cut ω).1 =
      ((fun i => designatedNoise S e r Ds main final N j i ω),
       (fun i => residualNoise S e r Ds main final N j i ω)) := by
  exact CompletedPrefixDraws.completed_eq_schedule c p (PrivateSamplingProgram.Config.mainSlots cfg) en (PrivateSamplingProgram.Config.layerOrigin cfg)
    (PrivateSamplingProgram.Config.mainDesignated cfg) (PrivateSamplingProgram.Config.mainResidual cfg) (PrivateSamplingProgram.Config.mainAuxiliary cfg) F N k hk batchRef dir saved
    j hj (bodyTape S e r Ds main final N ω).2.2

/-- Conditional deterministic reference interface. sigma is an explicit fixed
coefficient family, to be matched by the separate flow adapter. -/
def referenceY (Phi : Fin n → Point d → Point d) (sigma : Fin n → ℝ)
    (i : Fin n) (h : H) : Point d :=
  if h0 : k=0 then
    Phi i (zeta S e r Ds main final N k hk h) +
      samplingNoise S r Ds • eta S e r Ds main final N k hk i h
  else
    let draws := past S e r Ds main final N k hk (k-1) (by omega) h
    Phi i (zeta S e r Ds main final N k hk h) +
      (∑ j, samplingMatrix S e r i j • (sigma j • draws.1 j)) +
      ∑ j, residualRoot (samplingMatrix S e r) (samplingNoise S r Ds) (r^2) i j • draws.2 j

def referenceU (u : Fin n → Point d → Point d) (i : Fin n) (h : H) : Point d :=
  u i (zeta S e r Ds main final N k hk h)

set_option backward.isDefEq.respectTransparency false in
theorem measurable_referenceY (Phi : Fin n → Point d → Point d) (sigma : Fin n → ℝ)
    (i : Fin n) (hPhi : Measurable (Phi i)) :
    @Measurable H _ (prefixSpace d cut) _ (referenceY S e r Ds main final N k hk Phi sigma i) := by
  let : MeasurableSpace H := prefixSpace d cut
  have hp := hPhi.comp (measurable_zeta S e r Ds main final N k hk)
  by_cases h0 : k=0
  · have heq : referenceY S e r Ds main final N k hk Phi sigma i =
        (fun h : H => Phi i (zeta S e r Ds main final N k hk h) +
          samplingNoise S r Ds • eta S e r Ds main final N k hk i h) := by
      funext h
      simp only [referenceY, dite_eq_left h0]
    rw [heq]
    exact hp.add ((measurable_eta S e r Ds main final N k hk i).const_smul (samplingNoise S r Ds))
  · have hj : k-1<k := by omega
    have hd := measurable_past (d := d) S e r Ds main final N k hk (k-1) hj
    have heq : referenceY S e r Ds main final N k hk Phi sigma i =
        (fun h : H => Phi i (zeta S e r Ds main final N k hk h) +
          (∑ j, samplingMatrix S e r i j • (sigma j • (past S e r Ds main final N k hk (k-1) hj h).1 j)) +
          ∑ j, residualRoot (samplingMatrix S e r) (samplingNoise S r Ds) (r^2) i j •
            (past S e r Ds main final N k hk (k-1) hj h).2 j) := by
      funext h
      simp only [referenceY, dite_eq_right h0]
    rw [heq]
    exact
      (hp.add (Finset.measurable_sum Finset.univ (fun j _ => (((measurable_pi_apply j).comp hd.fst).const_smul (sigma j)).const_smul (samplingMatrix S e r i j)))).add
        (Finset.measurable_sum Finset.univ (fun j _ => ((measurable_pi_apply j).comp hd.snd).const_smul (residualRoot (samplingMatrix S e r) (samplingNoise S r Ds) (r^2) i j)))

theorem measurable_referenceU (u : Fin n → Point d → Point d) (i : Fin n)
    (hu : Measurable (u i)) :
    @Measurable H _ (prefixSpace d cut) _ (referenceU S e r Ds main final N k hk u i) :=
  hu.comp (measurable_zeta S e r Ds main final N k hk)

/-- Exact equality to the old raw-schedule observations at elapsed k-1. This
step does not require Phi's measurability or any Gaussian assumption. -/
theorem referenceY_eq_actual (Phi : Fin n → Point d → Point d) (sigma : Fin n → ℝ)
    (i : Fin n) (ω : FullTape (d := d) S e r Ds main final N) :
    referenceY S e r Ds main final N k hk Phi sigma i (split cut ω).1 =
    if k=0 then Phi i ω.2.1 + samplingNoise S r Ds •
      (show Point d from ((bodyTape S e r Ds main final N ω).1 i).1)
    else Phi i ω.2.1 +
      (∑ j, samplingMatrix S e r i j • (sigma j • designatedNoise S e r Ds main final N (k-1) j ω)) +
      ∑ j, residualRoot (samplingMatrix S e r) (samplingNoise S r Ds) (r^2) i j •
        residualNoise S e r Ds main final N (k-1) j ω := by
  by_cases h0 : k=0
  · simp only [referenceY, dite_eq_left h0, ite_eq_left h0]; rfl
  · simp only [referenceY, dite_eq_right h0, ite_eq_right h0]
    rw [past_eq_actual S e r Ds main final N k hk (k-1) (by omega) ω]
    rfl

theorem referenceU_eq_actual (u : Fin n → Point d → Point d) (i : Fin n)
    (ω : FullTape (d := d) S e r Ds main final N) :
    referenceU S e r Ds main final N k hk u i (split cut ω).1 = u i ω.2.1 := by
  rfl

/-- Supplies precisely the two reference hypotheses of the already written
canonical joint-law consumer. No assumption of prefix independence is added. -/
theorem reference_admissible (Phi u : Fin n → Point d → Point d) (sigma : Fin n → ℝ)
    (i : Fin n) (hPhi : Measurable (Phi i)) (hu : Measurable (u i)) :
    @Measurable H _ (prefixSpace d cut) _ (referenceY S e r Ds main final N k hk Phi sigma i) ∧
    @Measurable H _ (prefixSpace d cut) _ (referenceU S e r Ds main final N k hk u i) :=
  ⟨measurable_referenceY S e r Ds main final N k hk Phi sigma i hPhi,
   measurable_referenceU S e r Ds main final N k hk u i hu⟩

end AcceleratedLogConcave.Oracle.PrivateCompletedPrefixDraws
