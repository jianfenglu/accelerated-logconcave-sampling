import AcceleratedLogConcave.Oracle.CubicExecutableWorkShift
import AcceleratedLogConcave.Oracle.RecursivePrivateAnchorStability
import AcceleratedLogConcave.Oracle.PrivateSourceScalarAbsorption

/-! Deterministic actual-source stability under the prescribed scalar schedule.
The existing occurrence-path induction is instantiated here. The only root
conditions are original radius/width scalar caps, not descendant stability or
probabilistic accuracy. The actual oracle may be gradient V at any public scale. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators NNReal
namespace AcceleratedLogConcave.Oracle.PrescribedRecursiveStability
open Numerics Numerics.AffineGraph RecursiveCall RecursiveSize FixedTapeStability Precision
open CubicExecutableWorkShift
variable (P : SourceSchedule) (hK : 10≤P.K) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (hC : 8≤P.Csch) (hy : PrivateSourceScalarAbsorption.threshold P≤P.y)
local notation "baseHy" => PrivateSourceScalarAbsorption.base_threshold P hc (by linarith : P.csch≤1)
  (by linarith : 1≤P.Csch) hy
local notation "hR" => CubicSchedulePayments.radius_guard P hK hc hsmall hC baseHy
local notation "C" => source P hR

def root (r σ : ℝ) : State := ⟨r,σ,(P.K:ℝ)⟩

variable {d : ℕ} (scale : ℝ) (G : Point d → Point d) (ell : ℝ≥0)
  (hG : LipschitzWith ell (fun x => scale • G (scale • x)))
  (r0 σ0 : ℝ) (hr0 : 0<r0) (hσ0 : 0<σ0)
  (hrootRadius : (ell:ℝ)*r0^2≤P.delta) (hrootRatio : (ell:ℝ)*(r0/σ0)≤P.delta)

include hG hr0 hσ0 hrootRadius hrootRatio in
/-- Every actual endpoint, including terminal overshoots, obeys 2ell
stability on every full raw tape and common original designated input. -/
theorem reachable_childStable {p : State} {depth cost : ℕ}
    (hp : Path C (root P r0 σ0) p depth cost) :
    let E := data P hR hc hsmall scale p.radius p.width p.precision
    ChildStable E.program E.coefficient G (2*(ell:ℝ)) := by
  have hC1 : 1≤P.Csch := by linarith
  have hy0 := (CubicSchedulePayments.prerequisites P hK hc hsmall hC baseHy).1
  have hs := CubicSchedulePayments.actual_scalar_payments P hK hc hsmall hC baseHy
  have hgeom : (C).M.R=(C).δ^(C).t ∧ (C).M.psi=(C).δ^(4*(C).t) ∧
      (C).M.backward=actualKernelInterval (C).M.R ((C).δ^(C).w)
        (C).M.R_pos (C).M.R_le_half (Real.rpow_pos_of_pos P.delta_pos (C).w) := by
    refine ⟨rfl,?_,rfl⟩
    change P.R^4=P.delta^(4*P.t)
    exact P.psi_eq_R_pow.symm
  have hroot : SizeBound ell (C).δ 1 1 (root P r0 σ0).radius (root P r0 σ0).width := by
    change (ell:ℝ)*r0^2≤1*P.delta^1 ∧ (ell:ℝ)*(r0/σ0)≤1*P.delta^1
    simpa only [Real.rpow_one,one_mul] using And.intro hrootRadius hrootRatio
  exact Path.certified_childStable C (anchors P hR) (seeds P hR) scale G ell hG
    (root P r0 σ0) P.Bsize hroot (P.m_ge_two hc hsmall hC1) hr0 hσ0
    P.Ds_pos P.delta_pos (P.delta_le_one hy0) (P.t_pos hc) (P.t_le hc hsmall)
    (P.w_pos hc).le (P.w_lt_t hc hC1).le (P.Bsize_ge_one hc hsmall hC1 hy0)
    hgeom.1 le_rfl hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2
    ((P.rank_budget hc hsmall).le.trans (by norm_num)) hs.2.2.2.2.1
    hgeom.2.1 hs.2.2.2.2.2.1.2.2.2 hgeom.2.2 hp

include hG hr0 hσ0 hrootRadius hrootRatio in
/-- One concrete child occurrence; the path retains its actual layer tag. -/
theorem occurrence_childStable {p : State} {depth cost : ℕ}
    (hp : Path C (root P r0 σ0) p depth cost) (hq : 1/2<p.precision)
    (o : Occurrence P.NP (ScalarSchedulePayment.n P hR) (ScalarSchedulePayment.ns P hR) P.m) :
    let child := (C).child p o
    let E := data P hR hc hsmall scale child.radius child.width child.precision
    ChildStable E.program E.coefficient G (2*(ell:ℝ)) :=
  reachable_childStable P hK hc hsmall hC hy scale G ell hG r0 σ0 hr0 hσ0 hrootRadius hrootRatio
    (hp.snoc o ⟨hq,rfl⟩)

include hG hr0 hσ0 hrootRadius hrootRatio in
/-- Exact source mean main programs, with their q-1/4 widths/radii. -/
theorem meanMain_childStable {p : State} {depth cost : ℕ}
    (hp : Path C (root P r0 σ0) p depth cost) (hq : 1/2<p.precision)
    (i : Fin (ScalarSchedulePayment.n P hR)) :
    let child := MeanMainBatchCoupling.recursiveMain (C).M (C).nodes (anchors P hR) (seeds P hR)
      (C).mesh (C).snodes P.Ds P.delta P.t P.w P.NP (P.t_pos hc) (step_quarter P hc hsmall)
      scale p.radius p.width p.precision i
    ChildStable child.program child.coefficient G (2*(ell:ℝ)) :=
  occurrence_childStable P hK hc hsmall hC hy scale G ell hG r0 σ0 hr0 hσ0 hrootRadius hrootRatio
    hp hq (Occurrence.meanMain ⟨0,P.NP_pos (by linarith)⟩ i)

include hG hr0 hσ0 hrootRadius hrootRatio in
/-- Exact active-final programs, at q-t and the physical final width. -/
theorem activeFinal_childStable {p : State} {depth cost : ℕ}
    (hp : Path C (root P r0 σ0) p depth cost) (hq : 1/2<p.precision) (i : Fin P.m) :
    let child := MeanMainBatchCoupling.recursiveFinal (C).M (C).nodes (anchors P hR) (seeds P hR)
      (C).mesh (C).snodes P.Ds P.delta P.t P.w P.NP (P.t_pos hc) (step_quarter P hc hsmall)
      scale p.radius p.width p.precision i
    ChildStable child.program child.coefficient G (2*(ell:ℝ)) :=
  occurrence_childStable P hK hc hsmall hC hy scale G ell hG r0 σ0 hr0 hσ0 hrootRadius hrootRatio
    hp hq (Occurrence.activeFinal i)

include hG hr0 hσ0 hrootRadius hrootRatio in
/-- Exact private main programs, including the q-1/4 terminal children. -/
theorem privateMain_childStable {p : State} {depth cost : ℕ}
    (hp : Path C (root P r0 σ0) p depth cost) (hq : 1/2<p.precision)
    (i : Fin (ScalarSchedulePayment.ns P hR)) :
    let child := PrivateRecursiveBatchBudget.main (C).M (C).nodes (anchors P hR) (seeds P hR)
      (C).mesh (C).snodes P.Ds P.delta P.t P.w P.NP (P.t_pos hc) (step_quarter P hc hsmall)
      scale p.radius p.precision i
    ChildStable child.program child.coefficient G (2*(ell:ℝ)) :=
  occurrence_childStable P hK hc hsmall hC hy scale G ell hG r0 σ0 hr0 hσ0 hrootRadius hrootRatio
    hp hq (Occurrence.samplingMain ⟨0,P.NP_pos (by linarith)⟩ i)

include hG hr0 hσ0 hrootRadius hrootRatio in
/-- Exact private final programs use q-1/4 and their distinct final width. -/
theorem privateFinal_childStable {p : State} {depth cost : ℕ}
    (hp : Path C (root P r0 σ0) p depth cost) (hq : 1/2<p.precision)
    (i : Fin (ScalarSchedulePayment.ns P hR)) :
    let child := PrivateRecursiveBatchBudget.final (C).M (C).nodes (anchors P hR) (seeds P hR)
      (C).mesh (C).snodes P.Ds P.delta P.t P.w P.NP (P.t_pos hc) (step_quarter P hc hsmall)
      scale p.radius p.precision i
    ChildStable child.program child.coefficient G (2*(ell:ℝ)) :=
  occurrence_childStable P hK hc hsmall hC hy scale G ell hG r0 σ0 hr0 hσ0 hrootRadius hrootRatio
    hp hq (Occurrence.samplingFinal i)

section OriginalOracle
variable {V : Point d → ℝ} (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ (scaledPotential V scale)) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ (scaledPotential V scale)) z v v≤(ell:ℝ)*‖v‖^2)

include hV hlo hup in
/-- The normalized oracle Lipschitz input follows from the original scaled
potential. Execution still calls gradient V at the public physical scale. -/
theorem normalized_gradient : LipschitzWith ell (fun x => scale • gradient V (scale • x)) := by
  have hF : ContDiff ℝ 2 (scaledPotential V scale) := by
    unfold scaledPotential
    fun_prop
  have hl := Gibbs.gradient_lipschitz_of_hessian_bounds hF ell.coe_nonneg hlo hup
  have he : gradient (scaledPotential V scale) = fun x => scale • gradient V (scale • x) :=
    funext (gradient_scaled_potential (hV.of_le (by norm_num)) scale)
  rwa [he] at hl

include hV hlo hup hr0 hσ0 hrootRadius hrootRatio in
/-- Original-parameter source stability; no desired child stability, lower
accuracy, normalized-oracle certificate or row certificate is an input. -/
theorem reachable_original_gradient {p : State} {depth cost : ℕ}
    (hp : Path C (root P r0 σ0) p depth cost) :
    let E := data P hR hc hsmall scale p.radius p.width p.precision
    ChildStable E.program E.coefficient (gradient V) (2*(ell:ℝ)) :=
  reachable_childStable P hK hc hsmall hC hy scale (gradient V) ell
    (normalized_gradient scale ell hV hlo hup) r0 σ0 hr0 hσ0 hrootRadius hrootRatio hp
include hV hlo hup hr0 in
/-- A concrete original root domain pays both size caps. Width dominates the
root radius; descendants may have smaller widths and are handled by actual paths. -/
theorem reachable_original_gradient_of_sizes
    (hellδ : (ell:ℝ)≤P.delta) (hr1 : r0≤1) (hwidth : r0≤σ0)
    {p : State} {depth cost : ℕ} (hp : Path C (root P r0 σ0) p depth cost) :
    let E := data P hR hc hsmall scale p.radius p.width p.precision
    ChildStable E.program E.coefficient (gradient V) (2*(ell:ℝ)) := by
  have hσ : 0<σ0 := hr0.trans_le hwidth
  have hrr : r0^2≤1 := by nlinarith
  have hratio : r0/σ0≤1 := (div_le_one₀ hσ).2 hwidth
  have hrad : (ell:ℝ)*r0^2≤P.delta :=
    (mul_le_mul_of_nonneg_left hrr ell.coe_nonneg).trans (by simpa using hellδ)
  have hrat : (ell:ℝ)*(r0/σ0)≤P.delta :=
    (mul_le_mul_of_nonneg_left hratio ell.coe_nonneg).trans (by simpa using hellδ)
  exact reachable_original_gradient P hK hc hsmall hC hy scale ell r0 σ0 hr0 hσ hrad hrat hV hlo hup hp

end OriginalOracle

end AcceleratedLogConcave.Oracle.PrescribedRecursiveStability
