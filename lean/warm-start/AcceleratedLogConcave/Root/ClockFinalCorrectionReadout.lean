import AcceleratedLogConcave.Root.ClockFinalAssemblyReadout

/-! Exact executed final correction on the original full Clock tape.
Raw child replies are explicitly centered by a supplied mathematical mean
row U; the reference contains that deterministic row as well as the actual
assembly reserve and returned Gaussian references. No accuracy is assumed. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace AcceleratedLogConcave.Root.ClockFinalCorrectionReadout
open Oracle Oracle.AffineLowering Oracle.TapeLowering Oracle.NoisyLayer Oracle.RetainedMeanFinalBatch
open Oracle.TailOccurrenceCut Oracle.TailOccurrenceCut.TailCut
open ClockChronologicalCoupling ClockNoisyLayer
variable (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (clock : ClockLaw.Clock) (label : ℕ) {d : ℕ}
local notation "host" => Host P hR hc hsmall clock label
local notation "cur" => terminalCursor P hR hc hsmall clock label
local notation "cut" => terminalCut P hR hc hsmall clock label

def output (G : Point d→Point d) (xF momentum : Point d) (sample : Tape d host) : Point d :=
  (run host G ⟨ClockRetainedFinalSplice.table P hR hc hsmall clock,xF,momentum⟩ Env.empty sample).value

/-- Every final reply uses its actual reached center, original Pi and full tape. -/
def finalReply (G : Point d→Point d) (xF momentum : Point d) (sample : Tape d host) (i : Index P) : Point d :=
  childPoint (run
    (designatedChild (ClockRetainedFinalSplice.pf P hR hc hsmall clock i)
      (ClockRetainedFinalSplice.ef P hR hc hsmall clock i)
      (ClockRetainedFinalSplice.finalSlot P hR hc hsmall clock i)
      ((cur).old i) ((cur).saved (ClockRetainedFinalSplice.designatedRef P i))
      (ClockRetainedFinalSplice.finalAuxiliary P hR hc hsmall clock label i)) G
    ⟨ClockRetainedFinalSplice.table P hR hc hsmall clock,xF,momentum⟩
    (envAt G ⟨ClockRetainedFinalSplice.table P hR hc hsmall clock,xF,momentum⟩ cut Env.empty (split cut sample).1)
    ((split cut sample).2.1 i))

/-- Same original split and raw Gaussian array; no reserve draw is adjoined. -/
def reserve (momentum : Point d) (sample : Tape d host) : Point d :=
  ClockRetainedFinalSplice.reserveValue P clock
    (ClockPublicSetup.splitValues momentum
      (ClockFinalAssemblyReadout.splitDraw P hR hc hsmall clock label sample) 1)
    (ClockFinalAssemblyReadout.assemblyRaw P hR hc hsmall clock label sample)

/-- The literal program's normalized final correction, on every original tape. -/
theorem output_eq_normalized_replies (G : Point d→Point d) (xF momentum : Point d) (sample : Tape d host) :
    output P hR hc hsmall clock label G xF momentum sample =
      (∑ i,ClockRetainedFinalSplice.coefficient P clock i •
        ((ClockRetainedFinalSplice.width P clock i)⁻¹ • finalReply P hR hc hsmall clock label G xF momentum sample i)) +
      Conditional.GaussianAssembly.reserve (ClockRetainedFinalSplice.coefficient P clock) •
        reserve P hR hc hsmall clock label momentum sample := by
  unfold output
  rw [run_split_value G ⟨ClockRetainedFinalSplice.table P hR hc hsmall clock,xF,momentum⟩ cut Env.empty sample]
  rw [ClockRetainedFinalSplice.run_finish P hR hc hsmall clock label (cur).old (cur).direct (cur).saved G xF momentum]
  simp only [pointResult,one_smul]
  change storedPoint (envAt G ⟨ClockRetainedFinalSplice.table P hR hc hsmall clock,xF,momentum⟩ cut Env.empty
      (split cut sample).1) ((cur).saved (ClockRetainedFinalSplice.parentRef P)) +
    (∑ i,ClockRetainedFinalSplice.correctionWeight P clock i •
      (finalReply P hR hc hsmall clock label G xF momentum sample i -
        ClockRetainedFinalSplice.width P clock i •
          storedPoint (envAt G ⟨ClockRetainedFinalSplice.table P hR hc hsmall clock,xF,momentum⟩ cut Env.empty
            (split cut sample).1) ((cur).saved (ClockRetainedFinalSplice.designatedRef P i)))) = _
  rw [ClockFinalAssemblyReadout.terminal_parent_split]
  simp_rw [ClockFinalAssemblyReadout.terminal_designated_assembled]
  exact ClockRetainedFinalSplice.normalized_correction P clock _ _ _

/-- A reference always includes its explicit mathematical mean row. -/
def referenceOutput (U Pref : Index P→Point d) (momentum : Point d) (sample : Tape d host) : Point d :=
  (∑ i,ClockRetainedFinalSplice.correctionWeight P clock i • U i) +
    (∑ i,ClockRetainedFinalSplice.coefficient P clock i • Pref i) +
    Conditional.GaussianAssembly.reserve (ClockRetainedFinalSplice.coefficient P clock) •
      reserve P hR hc hsmall clock label momentum sample

/-- Exact paid correction error. Q is the raw actual reply; U has not been
silently discarded or identified with a same-tape oracle value. -/
theorem output_sub_reference (G : Point d→Point d) (xF momentum : Point d)
    (sample : Tape d host) (U Pref : Index P→Point d) :
    output P hR hc hsmall clock label G xF momentum sample -
      referenceOutput P hR hc hsmall clock label U Pref momentum sample =
    ∑ i,ClockRetainedFinalSplice.correctionWeight P clock i •
      (finalReply P hR hc hsmall clock label G xF momentum sample i-U i-
        ClockRetainedFinalSplice.width P clock i • Pref i) := by
  rw [output_eq_normalized_replies]
  simp only [referenceOutput,smul_sub,Finset.sum_sub_distrib]
  have hterm : (∑ i,ClockRetainedFinalSplice.correctionWeight P clock i •
      finalReply P hR hc hsmall clock label G xF momentum sample i) =
      ∑ i,ClockRetainedFinalSplice.coefficient P clock i •
        ((ClockRetainedFinalSplice.width P clock i)⁻¹ • finalReply P hR hc hsmall clock label G xF momentum sample i) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [ClockRetainedFinalSplice.correctionWeight,div_eq_mul_inv,smul_smul]
  have hnoise : (∑ i,ClockRetainedFinalSplice.correctionWeight P clock i •
      (ClockRetainedFinalSplice.width P clock i • Pref i)) =
      ∑ i,ClockRetainedFinalSplice.coefficient P clock i • Pref i := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [ClockRetainedFinalSplice.correctionWeight,smul_smul,
      div_mul_cancel₀ _ (ne_of_gt (ClockRetainedFinalSplice.width_pos P clock i))]
  rw [hterm,hnoise]
  module

end AcceleratedLogConcave.Root.ClockFinalCorrectionReadout
