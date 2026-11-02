import AcceleratedLogConcave.Oracle.PrescribedRecursiveStability
import AcceleratedLogConcave.Oracle.TerminalSourceRetainedCoupling

/-! Quantitative actual terminal endpoints of prescribed recursive paths.
Radius, width, terminal size exponent and resolution payment are derived from
original root caps and the actual path. No terminal accuracy is assumed. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace AcceleratedLogConcave.Oracle.PrescribedTerminalAccuracy
open Numerics Numerics.AffineGraph RecursiveCall RecursiveSize Precision TapeLowering
open CubicExecutableWorkShift

/-- Actual path radii never exceed the original root radius, also on the last
edge into a terminal call. All positive intermediate domains follow from the path. -/
theorem radius_le_root {m n ns : ℕ} {C : Source m n ns} {root p : State} {depth cost : ℕ}
    (hp : Path C root p depth cost) (hm : 0<m) (hDs : 0<C.Ds) (hδ : 0<C.δ)
    (hr : 0<root.radius) (hσ : 0<root.width) : p.radius≤root.radius := by
  induction hp with
  | refl => exact le_rfl
  | @snoc parent child depth cost hp o he ih =>
    have hpos := hp.positive hm hDs hδ hr hσ
    have hrad := RecursiveCallAccounting.child_radii_mem C.M C.S parent.radius hpos.1.le
    rcases he with ⟨_,rfl⟩
    rcases o with (⟨k,i⟩ | i) | (⟨k,i⟩ | i)
    · exact (hrad.2.2 _).2.trans ih
    · exact (hrad.2.2 _).2.trans ih
    · exact (hrad.1 _).2.trans ih
    · exact hrad.2.1.2.trans ih

variable (P : SourceSchedule) (hK : 10≤P.K) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (hC : 8≤P.Csch) (hy : PrivateSourceScalarAbsorption.threshold P≤P.y)
local notation "baseHy" => PrivateSourceScalarAbsorption.base_threshold P hc (by linarith : P.csch≤1)
  (by linarith : 1≤P.Csch) hy
local notation "hR" => CubicSchedulePayments.radius_guard P hK hc hsmall hC baseHy
local notation "C" => source P hR
variable (ell r0 σ0 : ℝ) (hell : 0≤ell) (hr0 : 0<r0) (hr1 : r0≤1) (hσ0 : 0<σ0)
  (hrootRadius : ell*r0^2≤P.delta) (hrootRatio : ell*(r0/σ0)≤P.delta)

include hell hr0 hr1 hσ0 hrootRadius hrootRatio in
/-- Every native terminal guard is paid from original root and schedule
parameters. The exponent is the exact quarter-cost exponent, not a loose cap. -/
theorem terminal_guards {p : State} {depth cost : ℕ}
    (hp : Path C (PrescribedRecursiveStability.root P r0 σ0) p depth cost) :
    0<p.radius ∧ p.radius≤1 ∧ 0<p.width ∧
      (3/4:ℝ)<1-10*P.t*(cost:ℝ) ∧
      (ell*p.radius)/p.width≤(stepFactor P.m P.Bsize)^depth*P.delta^(1-10*P.t*(cost:ℝ)) ∧
      3*(stepFactor P.m P.Bsize)^depth*P.delta^((1:ℝ)/4)≤1 := by
  have hC1 : 1≤P.Csch := by linarith
  have hy0 := (CubicSchedulePayments.prerequisites P hK hc hsmall hC baseHy).1
  have hδ1 := P.delta_le_one hy0
  have hs := CubicSchedulePayments.actual_scalar_payments P hK hc hsmall hC baseHy
  have hm := P.m_ge_two hc hsmall hC1
  have hB := P.Bsize_ge_one hc hsmall hC1 hy0
  have hroot : SizeBound ell (C).δ 1 1
      (PrescribedRecursiveStability.root P r0 σ0).radius (PrescribedRecursiveStability.root P r0 σ0).width := by
    change ell*r0^2≤1*P.delta^1 ∧ ell*(r0/σ0)≤1*P.delta^1
    simpa only [Real.rpow_one,one_mul] using And.intro hrootRadius hrootRatio
  have hpos := hp.positive (by omega) P.Ds_pos P.delta_pos hr0 hσ0
  have hsize := hp.root_size_bound ell P.Bsize hroot (by omega) hell hr0 hσ0 P.Ds_pos
    P.delta_pos hδ1 (P.w_pos hc).le (P.w_lt_t hc hC1).le hB rfl le_rfl
    hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2
  have hcost := hp.cost_rank_le (P.t_pos hc).le
  have hcost' : (cost:ℝ)≤(precisionRank (1/4) (P.K:ℝ):ℝ) := by
    exact_mod_cast (show cost≤precisionRank (1/4) (P.K:ℝ) by simpa [PrescribedRecursiveStability.root] using Nat.le_add_right cost (precisionRank (1/4) p.precision) |>.trans hcost)
  have hpaidCost := (mul_le_mul_of_nonneg_left hcost' (by positivity [P.t_pos hc] : 0≤10*P.t)).trans_lt
    (P.rank_budget hc hsmall)
  have hrank := hp.depth_rank_le (P.t_pos hc) (step_quarter P hc hsmall)
  have hdepth : depth≤precisionRank P.t (P.K:ℝ) := by
    change depth+precisionRank P.t p.precision≤precisionRank P.t (P.K:ℝ) at hrank
    omega
  have hstep : 1≤stepFactor P.m P.Bsize := (by norm_num : (1:ℝ)≤3).trans
    (stepFactor_ge_three P.m P.Bsize (by linarith))
  have hS : (stepFactor P.m P.Bsize)^depth≤(stepFactor P.m P.Bsize)^(precisionRank P.t (P.K:ℝ)) :=
    pow_le_pow_right₀ hstep hdepth
  have hcoeff := resolution_coefficient_lower hm P.Bsize hB (precisionRank P.t (P.K:ℝ))
  have hQpos : 0<ScalarSchedulePayment.Q P := lt_of_lt_of_le (by norm_num) hcoeff.1
  have hres := rpow_resolution_mul_le_one P.delta_pos hQpos hs.2.2.2.2.1
  have hmR : (1:ℝ)≤P.m := by exact_mod_cast (show 1≤P.m by omega)
  have h3S : 3*(stepFactor P.m P.Bsize)^depth≤ScalarSchedulePayment.Q P := by
    apply (mul_le_mul_of_nonneg_left hS (by norm_num : (0:ℝ)≤3)).trans
    exact mul_le_mul_of_nonneg_right (by nlinarith [one_le_pow₀ hmR (n := 5)]) (pow_nonneg (by linarith : 0≤stepFactor P.m P.Bsize) _)
  have hpow : P.delta^((1:ℝ)/4)≤P.delta^((1:ℝ)/12) :=
    Real.rpow_le_rpow_of_exponent_ge P.delta_pos hδ1 (by norm_num)
  refine ⟨hpos.1,(radius_le_root hp (by omega) P.Ds_pos P.delta_pos hr0 hσ0).trans hr1,
    hpos.2,by linarith,?_,?_⟩
  · have hh := hsize.2
    change ell*(p.radius/p.width)≤(stepFactor P.m P.Bsize)^depth*P.delta^(1-10*P.t*(cost:ℝ)) at hh
    simpa only [mul_div_assoc] using hh
  · exact (mul_le_mul h3S hpow (Real.rpow_nonneg P.delta_pos.le _) hQpos.le).trans hres

/-- Literal origin of the actual terminal source constructor. -/
def terminalOrigin : Origin := [⟨.mean,.setup,0,0,0⟩]

/-- Cast the complete terminal tape to the actual executable carrier using
its proved terminal-branch equality. No tape coordinate is regenerated. -/
def terminalTape {d : ℕ} (a r σ : ℝ) (E : ExecutableData)
    (hE : E=RecursiveExecutable.terminal a r σ)
    (ω : Tape d (terminalMeanProgram terminalOrigin)) : Tape d E.program :=
  hE.symm ▸ ω

/-- The cast terminal execution has exactly the original Result and trace. -/
theorem terminal_run_eq {d : ℕ} (a r σ : ℝ) (E : ExecutableData)
    (hE : E=RecursiveExecutable.terminal a r σ) (oracle : Point d → Point d)
    (x P : Point d) (ω : Tape d (terminalMeanProgram terminalOrigin)) :
    run E.program oracle ⟨E.coefficient,x,P⟩ Env.empty (terminalTape a r σ E hE ω) =
      run (terminalMeanProgram terminalOrigin) oracle (terminalMeanInputs a r σ x P) Env.empty ω := by
  cases hE
  rfl

/-- Literal actual source branch equality, retaining the full canonical tape
and paid terminal trace rather than comparing only a marginal output. -/
theorem reachable_terminal_run {d : ℕ} {p : State} {depth cost : ℕ}
    (_hp : Path C (PrescribedRecursiveStability.root P r0 σ0) p depth cost)
    (hq : p.precision≤1/2) (a : ℝ) (oracle : Point d → Point d) (x P0 : Point d)
    (ω : Tape d (terminalMeanProgram terminalOrigin)) :
    let E := data P hR hc hsmall a p.radius p.width p.precision
    run E.program oracle ⟨E.coefficient,x,P0⟩ Env.empty
      (terminalTape a p.radius p.width E
        (data_terminal P hR hc hsmall a p.radius p.width p.precision hq) ω) =
      run (terminalMeanProgram terminalOrigin) oracle (terminalMeanInputs a p.radius p.width x P0) Env.empty ω :=
  terminal_run_eq a p.radius p.width _
    (data_terminal P hR hc hsmall a p.radius p.width p.precision hq) oracle x P0 ω

variable {d : ℕ} {V : Point d → ℝ} (scale : ℝ) (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ (scaledPotential V scale)) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ (scaledPotential V scale)) z v v≤ell*‖v‖^2)

include hV hell hlo hup in
/-- Finite L2 error at every actual terminal endpoint, on the canonical full
source joint retaining original P and every terminal tape coordinate. -/
theorem terminal_error_memLp {p : State} {depth cost : ℕ}
    (_hp : Path C (PrescribedRecursiveStability.root P r0 σ0) p depth cost) (x : Point d) :
    MemLp (TerminalSourceRetainedCoupling.error terminalOrigin (gradient V) scale p.radius p.width
      x (Gibbs.primitiveMean (scaledPotential V scale) x p.radius)) 2
      (TerminalSourceRetainedCoupling.joint terminalOrigin x) :=
  TerminalSourceRetainedCoupling.scaled_error_memLp_two hV hell hlo hup terminalOrigin p.radius p.width x

include hV hell hlo hup hr0 hr1 hσ0 hrootRadius hrootRatio in
/-- Actual reachable terminal accuracy; all size and resolution guards are
derived, and q may be the terminal precision overshoot of the last actual edge. -/
theorem terminal_square_error_le {p : State} {depth cost : ℕ}
    (hp : Path C (PrescribedRecursiveStability.root P r0 σ0) p depth cost)
    (hq : p.precision≤1/2) (x : Point d) :
    (∫ z,‖TerminalSourceRetainedCoupling.error terminalOrigin (gradient V) scale p.radius p.width x
      (Gibbs.primitiveMean (scaledPotential V scale) x p.radius) z‖^2
        ∂TerminalSourceRetainedCoupling.joint terminalOrigin x) ≤
      (p.width*P.delta^p.precision*Gibbs.primitiveScale (scaledPotential V scale) x)^2 := by
  have hg := terminal_guards P hK hc hsmall hC hy ell r0 σ0 hell hr0 hr1 hσ0 hrootRadius hrootRatio hp
  exact TerminalSourceRetainedCoupling.scaled_square_error_le hV hell hlo hup hg.1 hg.2.1
    P.delta_pos (P.delta_le_one (CubicSchedulePayments.prerequisites P hK hc hsmall hC baseHy).1)
    hg.2.2.1 (pow_nonneg (le_trans (by norm_num) (stepFactor_ge_three P.m P.Bsize
      (by have := P.Bsize_ge_one hc hsmall (by linarith) (CubicSchedulePayments.prerequisites P hK hc hsmall hC baseHy).1; linarith))) _)
    hq hg.2.2.2.1 hg.2.2.2.2.1 hg.2.2.2.2.2 terminalOrigin x

end AcceleratedLogConcave.Oracle.PrescribedTerminalAccuracy
