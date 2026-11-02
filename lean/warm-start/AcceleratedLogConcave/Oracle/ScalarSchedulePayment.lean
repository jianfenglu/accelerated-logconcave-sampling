import AcceleratedLogConcave.Oracle.ScalarSchedulePaymentBounds
import AcceleratedLogConcave.Oracle.PrescribedSourceGeometry
import AcceleratedLogConcave.Oracle.RecursiveExecutableShiftBudget

/-! Actual prescribed producer counts discharge the scalar inventory premise.
No anchor/seed counts, actual shift theorem, work theorem, or root/oracle
certificate is supplied. Both explicit thresholds remain visible. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Oracle.ScalarSchedulePayment
open SourceSchedule SchedulePolynomialBounds Numerics.PrescribedMeshCardinality

/-- The actual producer's dimensions. hR is only its domain proof. -/
def n (P : SourceSchedule) (hR : P.R ≤ 1/2) : ℕ :=
  PrescribedSourceGeometry.meanCount P.m P.R P.h0 P.R_pos hR P.h0_pos

def ns (P : SourceSchedule) (hR : P.R ≤ 1/2) : ℕ :=
  PrescribedSourceGeometry.privateCount P.m P.R P.h0 P.R_pos hR P.h0_pos

def I (P : SourceSchedule) (hR : P.R ≤ 1/2) : ℕ := n P hR+ns P hR

def D (P : SourceSchedule) (hR : P.R ≤ 1/2) : ℝ :=
  RecursiveExecutable.sourceShiftBase P.NP (I P hR)

variable (P : SourceSchedule)

theorem count_scale (hc : 0 < P.csch) (hy : 0 ≤ P.y) :
    (meshBudget P.R P.h0)^2 = (1+P.t*P.y)^2*Real.exp (2*P.w*P.y) := by
  have he : P.h0^2 = (Real.exp (2*P.w*P.y))⁻¹ := by
    rw [P.h0_eq_exp, ← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (2:ℝ)*(-P.w*P.y) = -(2*P.w*P.y) by ring, Real.exp_neg]
  rw [meshBudget, SourceSchedule.R, P.abs_log_R hc hy, div_pow, he, div_inv_eq_mul]

set_option backward.isDefEq.respectTransparency false in
theorem actual_counts (hR : P.R ≤ 1/2) (hc : 0 < P.csch) (hsmall : P.csch < 1/160)
    (hC : 1 ≤ P.Csch) (hy : 0 ≤ P.y) (hgeom : Ygeom P ≤ P.y) :
    (n P hR:ℝ) ≤ 1280*(P.m:ℝ)^4*(1+P.t*P.y)^2*Real.exp (2*P.w*P.y) ∧
    (ns P hR:ℝ) ≤ 1280*(P.m:ℝ)^4*(1+P.t*P.y)^2*Real.exp (2*P.w*P.y) := by
  have hhalf := (geometry_caps P hc hsmall hC hy hgeom).2.2.2
  have hm := P.m_ge_two hc hsmall hC
  have hn := (PrescribedSourceGeometry.counts P.m P.R P.h0 P.R_pos hR P.h0_pos hm hhalf).1
  have hs := PrescribedMeshDimensions.sampling_card_le_common
    (PrescribedSourceGeometry.samplingGeometry P.m P.R P.h0 P.R_pos hR P.h0_pos)
    hm P.h0 P.h0_pos hhalf rfl
  change (n P hR:ℝ) ≤ 1280*(P.m:ℝ)^4*(meshBudget P.R P.h0)^2 at hn
  change (ns P hR:ℝ) ≤ 1280*(P.m:ℝ)^4*(meshBudget P.R P.h0)^2 at hs
  rw [count_scale P hc hy] at hn hs
  constructor <;> nlinarith [hn, hs]

theorem D_ge_one (hR : P.R ≤ 1/2) : 1 ≤ D P hR := by
  unfold D RecursiveExecutable.sourceShiftBase
  have hn : 0 ≤ (P.NP:ℝ) := Nat.cast_nonneg _
  have hi : 0 ≤ (I P hR:ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg hn hi]

/-- The actual inventory including its extra unit is charged, not guessed. -/
theorem actual_D_upper (hR : P.R ≤ 1/2) (hc : 0 < P.csch) (hsmall : P.csch < 1/160)
    (hC : 1 ≤ P.Csch) (hy : 0 ≤ P.y) (hgeom : Ygeom P ≤ P.y) :
    D P hR ≤ a P*(1+P.y)^2*Real.exp (2*P.w*P.y) := by
  let F := (P.m:ℝ)^4*(1+P.y)^2*Real.exp (2*P.w*P.y)
  have hm := m_ge_one P hc hsmall hC
  have ht := P.t_pos hc
  have hw := P.w_pos hc
  have hty := mul_le_mul_of_nonneg_right (t_le_one P (by linarith : P.csch ≤ 1)) hy
  have hE : 1280*(P.m:ℝ)^4*(1+P.t*P.y)^2*Real.exp (2*P.w*P.y) ≤ 1280*F := by
    have hsq : (1+P.t*P.y)^2 ≤ (1+P.y)^2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have hmul := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 1280*(P.m:ℝ)^4)
    have hmul2 := mul_le_mul_of_nonneg_right hmul (Real.exp_nonneg (2*P.w*P.y))
    simpa only [F, mul_assoc] using hmul2
  have hcns := actual_counts P hR hc hsmall hC hy hgeom
  have hn := hcns.1.trans hE
  have hs := hcns.2.trans hE
  have hF : 1 ≤ F := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hm) (one_le_pow₀ (by linarith : 1 ≤ 1+P.y)))
    (Real.one_le_exp_iff.mpr (by positivity))
  have hI : (I P hR:ℝ)+1 ≤ 2561*F := by unfold I; push_cast; linarith
  calc
    _ ≤ 100*((P.NP:ℝ)+2)*(2561*F) :=
      mul_le_mul_of_nonneg_left hI (by positivity)
    _ = _ := by dsimp [a, F]; ring

theorem actual_D_work (hR : P.R ≤ 1/2) (hc : 0 < P.csch) (hsmall : P.csch < 1/160)
    (hC : 1 ≤ P.Csch) (hy : 0 ≤ P.y) (hwork : Ywork P ≤ P.y) (hgeom : Ygeom P ≤ P.y) :
    (D P hR)^(G P) ≤ Real.exp (P.y/64) :=
  D_power_payment P hc hsmall hC hy hwork (D P hR) (D_ge_one P hR)
    (actual_D_upper P hR hc hsmall hC hy hgeom)

theorem actual_D_support (hR : P.R ≤ 1/2) (hc : 0 < P.csch) (hsmall : P.csch < 1/160)
    (hC : 1 ≤ P.Csch) (hy : 0 ≤ P.y) (hwork : Ywork P ≤ P.y) (hgeom : Ygeom P ≤ P.y) :
    (D P hR)^(P.Hs+2) ≤ P.Ds ∧ (D P hR)^(P.Hs+1) ≤ P.Ds :=
  D_support_payment P hc hsmall hC hy hwork (D P hR) (D_ge_one P hR)
    (actual_D_upper P hR hc hsmall hC hy hgeom)

set_option backward.isDefEq.respectTransparency false in
theorem actual_dimensions (hR : P.R ≤ 1/2) (hc : 0 < P.csch) (hsmall : P.csch < 1/160)
    (hC : 1 ≤ P.Csch) (hy : 0 ≤ P.y) (hgeom : Ygeom P ≤ P.y) :
    Real.sqrt (n P hR) ≤ P.Bsize*P.delta^(-P.w) ∧ Real.sqrt (ns P hR) ≤ P.Bsize*P.delta^(-P.w) := by
  have hhalf := (geometry_caps P hc hsmall hC hy hgeom).2.2.2
  have hB := (P.Bsize_eq_log hc hy).symm.le
  exact PrescribedSourceGeometry.source_dimensions P.m P.delta P.t P.w P.Ds P.NP
    (P.m_ge_two hc hsmall hC) P.delta_pos hR hhalf P.Bsize hB

/-- All requested scalar payments on the actual producer, with its domain
proof derived from Ygeom. No cardinality or mesh equality is an input. -/
theorem actual_payments (hc : 0 < P.csch) (hsmall : P.csch < 1/160) (hC : 1 ≤ P.Csch)
    (hy : 0 ≤ P.y) (hwork : Ywork P ≤ P.y) (hgeom : Ygeom P ≤ P.y) :
    let hR := (geometry_caps P hc hsmall hC hy hgeom).2.2.1.trans
      (geometry_caps P hc hsmall hC hy hgeom).2.2.2
    D P hR ≤ a P*(1+P.y)^2*Real.exp (2*P.w*P.y) ∧
    (D P hR)^(G P) ≤ Real.exp (P.y/64) ∧
    (D P hR)^(P.Hs+2) ≤ P.Ds ∧ (D P hR)^(P.Hs+1) ≤ P.Ds ∧
    P.delta ≤ (Q P)^(-12:ℝ) ∧
    (0 < P.delta ∧ P.delta ≤ P.R ∧ P.R ≤ P.h0 ∧ P.h0 ≤ 1/2) ∧
    Real.sqrt (n P hR) ≤ P.Bsize*P.delta^(-P.w) ∧ Real.sqrt (ns P hR) ≤ P.Bsize*P.delta^(-P.w) := by
  dsimp only
  refine ⟨actual_D_upper P _ hc hsmall hC hy hgeom, actual_D_work P _ hc hsmall hC hy hwork hgeom,
    (actual_D_support P _ hc hsmall hC hy hwork hgeom).1,
    (actual_D_support P _ hc hsmall hC hy hwork hgeom).2,
    resolution_payment P hc hsmall hC hy hwork, geometry_caps P hc hsmall hC hy hgeom,
    (actual_dimensions P _ hc hsmall hC hy hgeom).1, (actual_dimensions P _ hc hsmall hC hy hgeom).2⟩
end AcceleratedLogConcave.Oracle.ScalarSchedulePayment
