import AcceleratedLogConcave.Root.ClockChronologicalExecution
import AcceleratedLogConcave.Oracle.PrivateChronologicalCoupling

/-! Exact complete unread-suffix law of the actual finite retained Clock loop. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Root.ClockChronologicalPast
open Oracle Oracle.AffineLowering Oracle.TapeLowering Oracle.NoisyLayer
open Oracle.RecursiveMeanProgram Oracle.RecursiveMeanContinuation
open Oracle.TailOccurrenceCut Oracle.PrivateCausalLayer Oracle.PrivateCausalAdvance
open TailCut Oracle.CanonicalTapeMeasurability Oracle.CanonicalTapeLaw
open ClockChronologicalCoupling ClockNoisyLayer
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
variable (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (clock : ClockLaw.Clock) (label : ℕ) (hK : 10≤P.K) (hC : 8≤P.Csch)
  (hy : CubicScheduleThreshold.threshold P≤P.y)
  {d : ℕ} {V : Point d→ℝ} (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
  (hyMean : MeanSourceScalarAbsorption.threshold P≤P.y)

/-- All original source coordinates and the first k recorded returned vectors.
Keeping the complete original tape makes this useful for later child errors. -/
def past (k : ℕ) (hk : k≤(P.K+4))
    (z : History P d × Tape d (Host P hR hc hsmall clock label)) :=
  ((z.1.1,z.2), fun j : Fin k => z.1.2.1 ⟨j,lt_of_lt_of_le j.2 hk⟩)

theorem past_measurable (k : ℕ) (hk : k≤(P.K+4)) :
    Measurable (past (d := d) P hR hc hsmall clock label k hk) := by
  exact (measurable_fst.fst.prodMk measurable_snd).prodMk
    (Measurable.of_eval fun j => (measurable_pi_apply _).comp measurable_fst.snd.fst)

theorem past_record (s : Cursor P hR hc hsmall clock label) (hs : 0<s.remaining)
    (k : ℕ) (hk : k≤(P.K+4)) (j : Fin (P.K+4)) (hj : k≤j)
    (z : (History P d × Tape d (Host P hR hc hsmall clock label)) × (Index P → Point d)) :
    past P hR hc hsmall clock label k hk
      (record P hR hc hsmall clock label hK hC hy s hs j z) =
    past P hR hc hsmall clock label k hk z.1 := by
  apply Prod.ext
  · rfl
  · funext i
    apply Function.update_of_ne
    intro h
    have hv := congrArg Fin.val h
    change (i:ℕ) = (j:ℕ) at hv
    omega

theorem step_past (s : Cursor P hR hc hsmall clock label) (hs : 0<s.remaining)
    (k : ℕ) (hk : k≤(P.K+4)) (j : Fin (P.K+4)) (hj : k≤j) :
    (step P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs j).map
      (past P hR hc hsmall clock label k hk) =
    Kernel.deterministic (past P hR hc hsmall clock label k hk)
      (past_measurable P hR hc hsmall clock label k hk) := by
  rw [ClockChronologicalCoupling.step,← Kernel.map_comp_right _
    (record_measurable P hR hc hsmall clock label hK hC hy s hs j)
    (past_measurable P hR hc hsmall clock label k hk)]
  have he : past (d := d) P hR hc hsmall clock label k hk ∘
      record P hR hc hsmall clock label hK hC hy s hs j =
      past P hR hc hsmall clock label k hk ∘ Prod.fst := by
    funext z
    exact past_record P hR hc hsmall clock label hK hC hy s hs k hk j hj z
  rw [he,Kernel.map_comp_right _ measurable_fst (past_measurable P hR hc hsmall clock label k hk),
    ← Kernel.fst_eq,adjoin_original,Kernel.id_map]
/-- Later actual layers preserve all already recorded returned references
jointly with the full original seed. This is a kernel identity, before choosing
a probability law or an external center. -/
theorem iteration_past (k l : ℕ) (hk : k≤(P.K+4)) (hkl : k≤l) (hl : l≤(P.K+4)) :
    (iteration P hR hc hsmall clock label hK hC hy hV hlo hup hyMean l hl).map
      (past P hR hc hsmall clock label k hk) =
    (iteration P hR hc hsmall clock label hK hC hy hV hlo hup hyMean k hk).map
      (past P hR hc hsmall clock label k hk) := by
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l hkl ih =>
    rw [iteration,Kernel.map_comp,step_past P hR hc hsmall clock label hK hC hy hV hlo hup hyMean
      _ _ k hk ⟨l,by omega⟩ hkl,Kernel.deterministic_comp_eq_map]
    exact ih (by omega)
/-- Read any completed prefix of returned references from the final finite
loop law without changing its joint law with the complete original source. -/
theorem kernel_past (k : ℕ) (hk : k≤(P.K+4)) (μ : Measure ((Point d × Point d) × Tape d (Host P hR hc hsmall clock label))) :
    (kernel P hR hc hsmall clock label hK hC hy hV hlo hup hyMean ∘ₘ μ).map
      (past P hR hc hsmall clock label k hk) =
    (iteration P hR hc hsmall clock label hK hC hy hV hlo hup hyMean k hk ∘ₘ
      (μ.map (prepare P hR hc hsmall clock label))).map (past P hR hc hsmall clock label k hk) := by
  rw [kernel,← Measure.comp_assoc,Measure.deterministic_comp_eq_map,Measure.map_comp _ _ (past_measurable P hR hc hsmall clock label k hk),
    iteration_past P hR hc hsmall clock label hK hC hy hV hlo hup hyMean k (P.K+4) hk hk le_rfl,
    Measure.map_comp _ _ (past_measurable P hR hc hsmall clock label k hk)]

end AcceleratedLogConcave.Root.ClockChronologicalPast
