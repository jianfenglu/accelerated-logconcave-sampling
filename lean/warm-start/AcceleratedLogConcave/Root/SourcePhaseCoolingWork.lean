import AcceleratedLogConcave.Root.ClockFinitePhaseWork
import AcceleratedLogConcave.Root.CoolingPrescribedPayments

/-! Full deterministic query-plus-Gaussian accounting for the actual phase
and prescribed public cooling executions. No probabilistic exceptional set
or child cost premise is used. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
open scoped BigOperators NNReal
namespace AcceleratedLogConcave.Root.SourcePhaseCoolingWork
open Oracle Oracle.TapeLowering ClockFinitePhaseKernel ClockFinitePhaseWork
open ClockRetainedFinalSplice ClockRetainedTapeTransport
variable (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  {d : ℕ} (ell : ℕ)

/-- Both actual final Gaussian blocks are charged in addition to the complete
root trace; insertion of the uniform clock changes no Gaussian count. -/
theorem phase_gaussians (Γ : ℝ) (G : Point d → Point d)
    (a : (Point d × Point d) × Draw P hR hc hsmall (d:=d) ell) :
    (traceCounts (ClockFinitePhaseWork.execute P hR hc hsmall ell Γ G a).trace).gaussianBlocks =
      (traceCounts (rootRun P hR hc hsmall ell G a).trace).gaussianBlocks+2 := by
  have h := congrArg (fun t : List (Event d) => (traceCounts t).gaussianBlocks)
    (List.take_append_drop 1 (rootRun P hR hc hsmall ell G a).trace)
  simp [ClockFinitePhaseWork.execute,traceCounts,shapeCounts,shapeCount,Event.erase] at h ⊢
  omega

/-- Every original-gradient query and Gaussian block of the literal physical
phase is paid, including reheating and momentum refresh. -/
theorem phase_full_work_le (hK : 10≤P.K) (hC : 8≤P.Csch)
    (hy : CubicScheduleThreshold.threshold P≤P.y) (Γ : ℝ) (G : Point d → Point d)
    (a : (Point d × Point d) × Draw P hR hc hsmall (d:=d) ell) :
    (((traceCounts (ClockFinitePhaseWork.execute P hR hc hsmall ell Γ G a).trace).queries+
      (traceCounts (ClockFinitePhaseWork.execute P hR hc hsmall ell Γ G a).trace).gaussianBlocks:ℕ):ℝ)≤
        2*Real.exp (P.y/32)+2 := by
  rw [ClockFinitePhaseWork.execute_queries,phase_gaussians]
  have hb := ClockRetainedWork.executed_full_work_le P hc hsmall anchorClock hK hC hy ell G
    ⟨anchorTable P hR hc hsmall (ClockUniformDraw.clockOfUniform a.2.1.1.1) ell,
      (normalizedInput P a.1).1,a.1.2⟩ a.2.1.1.2
  change (((traceCounts (rootRun P hR hc hsmall ell G a).trace).queries+
    (traceCounts (rootRun P hR hc hsmall ell G a).trace).gaussianBlocks:ℕ):ℝ)≤_ at hb
  push_cast at hb ⊢
  linarith


section SourceSchedule
variable (hK : 10≤P.K) (hC : 8≤P.Csch)
  (hy : PrivateSourceScalarAbsorption.threshold P≤P.y)
local notation "baseHy" => PrivateSourceScalarAbsorption.base_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy
local notation "hRs" => CubicSchedulePayments.radius_guard P hK hc hsmall hC baseHy
local notation "Q" => CoolingPrescribedPayments.setup P hRs hc hsmall

/-- Complete phase-plus-public-cooling query/Gaussian work on every collection
of actual execution tapes. This includes every initialization, recursive child,
active final correction, reheating and momentum-refresh Gaussian. Entering
states may be adaptive; no distributional restriction is imposed. -/
theorem total_full_work_le (N L : ℕ) (labels : Fin N → ℕ)
    (Γ : ℝ) (G : Point d → Point d)
    (a : ∀ i, (Point d × Point d) × Draw P hRs hc hsmall (d:=d) (labels i))
    (v : Fin L → ℝ≥0) (x : Fin L → Point d)
    (ω : ∀ i, CoolingExecutable.FullTape Q d P.delta (v i) P.K) :
    (∑ i : Fin N, (((traceCounts (ClockFinitePhaseWork.execute P hRs hc hsmall (labels i) Γ G (a i)).trace).queries+
      (traceCounts (ClockFinitePhaseWork.execute P hRs hc hsmall (labels i) Γ G (a i)).trace).gaussianBlocks:ℕ):ℝ)) +
    (∑ i : Fin L, (((traceCounts (CoolingExecutable.execute Q P.delta (v i) P.K G (x i) (ω i)).trace).queries+
      (traceCounts (CoolingExecutable.execute Q P.delta (v i) P.K G (x i) (ω i)).trace).gaussianBlocks:ℕ):ℝ)) ≤
    (N:ℝ)*(2*Real.exp (P.y/32)+2)+
      (L:ℝ)*((CoolingExecutableWork.localGaussians Q:ℝ)+
        (CoolingExecutableWork.occurrences Q:ℝ)*Real.exp (P.y/64)) := by
  have hphase : (∑ i : Fin N, (((traceCounts (ClockFinitePhaseWork.execute P hRs hc hsmall (labels i) Γ G (a i)).trace).queries+
      (traceCounts (ClockFinitePhaseWork.execute P hRs hc hsmall (labels i) Γ G (a i)).trace).gaussianBlocks:ℕ):ℝ)) ≤
      (N:ℝ)*(2*Real.exp (P.y/32)+2) := by
    calc
      _ ≤ ∑ _i : Fin N, (2*Real.exp (P.y/32)+2) :=
        Finset.sum_le_sum (fun i _ => phase_full_work_le P hRs hc hsmall (labels i) hK hC baseHy Γ G (a i))
      _ = _ := by simp; ring
  exact add_le_add hphase (CoolingSourceWork.finite_full_work_paid P hK hc hsmall hC baseHy
    (CoolingPrescribedPayments.mesh P) (CoolingPrescribedPayments.nodes P) L P.delta v G x ω)
end SourceSchedule
end AcceleratedLogConcave.Root.SourcePhaseCoolingWork
