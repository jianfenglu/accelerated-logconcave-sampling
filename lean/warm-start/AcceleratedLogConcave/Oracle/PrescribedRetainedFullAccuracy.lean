import AcceleratedLogConcave.Oracle.PrescribedRetainedNonterminalAccuracy

/-! Actual finite precision induction on the already constructed retained
kernels. Every induction argument is a literal lower call, with its same full
canonical seed. The source curvature domain ell≤delta is explicit. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Oracle.PrescribedRetainedFullAccuracy
open Numerics Numerics.AffineGraph CubicExecutableWorkShift RecursiveCall TapeLowering CanonicalTapeMeasurability
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
open RecursiveRetainedAccuracy PrescribedRetainedQuantitativeInduction PrescribedRetainedChildPaths
variable (P : SourceSchedule) (hK : 10≤P.K) (hc : 0<P.csch) (hcsmall : P.csch<1/160)
  (hC : 8≤P.Csch) (hy : PrivateSourceScalarAbsorption.threshold P≤P.y)
  {d : ℕ} (ell r0 σ0 : ℝ) (hell : 0≤ell) (hr0 : 0<r0) (hσ0 : 0<σ0)
  (hrootRadius : ell*r0^2≤P.delta)
  {V : Point d → ℝ} (scale : ℝ) (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ (scaledPotential V scale)) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ (scaledPotential V scale)) z v v≤ell*‖v‖^2)
  (hyMean : MeanSourceScalarAbsorption.threshold P≤P.y)
  (hr1 : r0≤1) (hellδ : ell≤P.delta) (hrootRatio : ell*(r0/σ0)≤P.delta)

include hyMean hr1 hellδ hrootRatio in
/-- Actual retained accuracy at every reachable precision. The four recursive
arguments are exactly the lower joints used to construct the parent; no
current-call accuracy or arbitrary alternate coupling is assumed. -/
theorem accurate {p : State} {depth cost : ℕ}
    (hp : Path (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy))
      (PrescribedRecursiveStability.root P r0 σ0) p depth cost) :
    AccurateCall P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup hp := by
  classical
  by_cases hterminal : p.precision≤1/2
  · exact terminal_case P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius
      scale hV hlo hup hr1 hrootRatio hp hterminal
  · apply PrescribedRetainedNonterminalAccuracy.nonterminal_case P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius
      scale hV hlo hup hp (lt_of_not_ge hterminal) hyMean hr1 hellδ hrootRatio
    · intro i
      exact accurate (main_path (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius hp (lt_of_not_ge hterminal) i)
    · intro i
      exact accurate (final_path (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius hp (lt_of_not_ge hterminal) i)
    · intro i
      exact accurate (privateMain_path (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius hp (lt_of_not_ge hterminal) i)
    · intro i
      exact accurate (privateFinal_path (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius hp (lt_of_not_ge hterminal) i)
termination_by Precision.precisionRank P.t p.precision
decreasing_by
  all_goals
    apply Nat.lt_of_succ_le
    apply Precision.precisionRank_drop (P.t_pos hc) (lt_of_not_ge hterminal)
    first
    | exact le_rfl
    | dsimp only [endpoint]
      have ht := step_quarter P hc hcsmall
      linarith

include hyMean hr1 hellδ hrootRatio in
/-- The original source call inherits the same complete-seed physical error
bound at every center, with the literal root precision K and constant four. -/
theorem root_fiber :
    MeanStandaloneLowerErrorBound.Fiber (F := scaledPotential V scale) (gradient V)
      (data P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy) hc hcsmall scale r0 σ0 (P.K:ℝ))
      (reachableLaw P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup
        (RecursiveCall.Path.refl (C := source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy))
          (PrescribedRecursiveStability.root P r0 σ0))).joint
      r0 σ0 (4*σ0*P.delta^(P.K:ℝ)) := by
  let hp := RecursiveCall.Path.refl (C := source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy))
    (PrescribedRecursiveStability.root P r0 σ0)
  exact PrescribedRetainedStepAccuracy.call_fiber P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius
    scale hV hlo hup hp (accurate P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius
      scale hV hlo hup hyMean hr1 hellδ hrootRatio hp)

end AcceleratedLogConcave.Oracle.PrescribedRetainedFullAccuracy
