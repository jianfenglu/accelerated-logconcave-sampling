import AcceleratedLogConcave.Root.CoolingSourceRootGuards
import AcceleratedLogConcave.Root.SourcePhaseCoolingWork

/-! The literal public cooling inventory is absorbed by the existing source
work threshold. Every child and local Gaussian remains charged. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators NNReal
namespace AcceleratedLogConcave.Root.CoolingSourceWorkPayment
open Oracle Numerics Numerics.AffineGraph
variable (P : SourceSchedule) (hK : 10≤P.K) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (hC : 8≤P.Csch) (hy : PrivateSourceScalarAbsorption.threshold P≤P.y)
local notation "baseHy" => PrivateSourceScalarAbsorption.base_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy
local notation "hR" => CubicSchedulePayments.radius_guard P hK hc hsmall hC baseHy
local notation "S" => CoolingPrescribedPayments.geometry P hR
local notation "Q" => CoolingPrescribedPayments.setup P hR hc hsmall
local notation "nc" => Fintype.card ((CoolingPrescribedPayments.mesh P).Source P.m)
include hK hc hsmall hC hy

/-- The full literal local-plus-recursive occurrence multiplicity fits in
exactly the existing polynomial/exponential work envelope. -/
theorem inventory_envelope :
    (CoolingExecutableWork.localGaussians Q:ℝ)+(CoolingExecutableWork.occurrences Q:ℝ)≤
      ScalarSchedulePayment.a P*(1+P.y)^2*Real.exp (2*P.w*P.y) := by
  have hp := CubicSchedulePayments.prerequisites P hK hc hsmall hC baseHy
  have hy0 := hp.1
  have hm := P.m_ge_two hc hsmall (by linarith : 1≤P.Csch)
  have hm1 : (1:ℝ)≤P.m := by exact_mod_cast (show 1≤P.m by omega)
  have hhalf := (ScalarSchedulePayment.geometry_caps P hc hsmall (by linarith) hp.1 hp.2.2).2.2.2
  have hn := PrescribedMeshDimensions.sampling_card_le_common S hm P.h0 P.h0_pos hhalf rfl
  change (nc:ℝ)≤1280*(P.m:ℝ)^4*(PrescribedMeshCardinality.meshBudget P.R P.h0)^2 at hn
  rw [ScalarSchedulePayment.count_scale P hc hp.1] at hn
  let F := (P.m:ℝ)^4*(1+P.y)^2*Real.exp (2*P.w*P.y)
  have hty : P.t*P.y≤P.y := by
    have ht := P.t_le hc hsmall
    nlinarith only [mul_le_mul_of_nonneg_right ht hp.1,hp.1]
  have hsq : (1+P.t*P.y)^2≤(1+P.y)^2 := by
    apply pow_le_pow_left₀ (by positivity [P.t_pos hc]) (by linarith)
  have hn' : (nc:ℝ)≤1280*F := by
    have hb := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hsq (Real.exp_nonneg (2*P.w*P.y))) (show 0≤1280*(P.m:ℝ)^4 by positivity)
    exact hn.trans (hb.trans_eq (by dsimp [F]; ring))
  have hF : 1≤F := by
    apply one_le_mul_of_one_le_of_one_le
    · exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hm1) (one_le_pow₀ (by linarith : 1≤1+P.y))
    · exact Real.one_le_exp_iff.mpr (by positivity [P.w_pos hc])
  change ((3+2*nc+2*P.NP*nc:ℕ):ℝ)+(((P.NP+1)*nc:ℕ):ℝ)≤_
  push_cast
  have hnp : 0≤(P.NP:ℝ) := Nat.cast_nonneg _
  have hb := mul_le_mul_of_nonneg_left hn' (show 0≤3*((P.NP:ℝ)+1) by positivity)
  rw [show ScalarSchedulePayment.a P*(1+P.y)^2*Real.exp (2*P.w*P.y)=256100*((P.NP:ℝ)+2)*F by unfold ScalarSchedulePayment.a; dsimp [F]; ring]
  nlinarith [mul_nonneg hnp (by linarith : 0≤F)]

/-- All actual cooling occurrence multiplicities, with no dropped overhead. -/
theorem inventory_paid :
    (CoolingExecutableWork.localGaussians Q:ℝ)+(CoolingExecutableWork.occurrences Q:ℝ)≤Real.exp (P.y/64) := by
  let c := (CoolingExecutableWork.localGaussians Q:ℝ)+(CoolingExecutableWork.occurrences Q:ℝ)
  have hc1 : 1≤c := by
    dsimp only [c]
    norm_cast
    unfold CoolingExecutableWork.localGaussians
    omega
  have hp := CubicSchedulePayments.prerequisites P hK hc hsmall hC baseHy
  have hpaid := ScalarSchedulePayment.D_power_payment P hc hsmall (by linarith) hp.1 hp.2.1 c hc1
    (inventory_envelope P hK hc hsmall hC hy)
  have hpow : c≤c^(ScalarSchedulePayment.G P) := by
    simpa only [pow_one] using pow_le_pow_right₀ hc1 (ScalarSchedulePayment.G_pos P)
  exact hpow.trans hpaid


/-- The complete public source budget, including its exact local Gaussian
count, has the same exponential work payment as a finite root phase. -/
theorem budget_paid :
    (CoolingExecutableWork.localGaussians Q:ℝ)+
      (CoolingExecutableWork.occurrences Q:ℝ)*Real.exp (P.y/64)≤Real.exp (P.y/32) := by
  have hy0 := (CubicSchedulePayments.prerequisites P hK hc hsmall hC baseHy).1
  have hE : 1≤Real.exp (P.y/64) := Real.one_le_exp_iff.mpr (by positivity)
  have hlocal := mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg (CoolingExecutableWork.localGaussians Q))
  calc
    _ ≤ ((CoolingExecutableWork.localGaussians Q:ℝ)+(CoolingExecutableWork.occurrences Q:ℝ))*Real.exp (P.y/64) := by nlinarith
    _ ≤ Real.exp (P.y/64)*Real.exp (P.y/64) :=
      mul_le_mul_of_nonneg_right (inventory_paid P hK hc hsmall hC hy) (Real.exp_nonneg _)
    _ = Real.exp (P.y/32) := by rw [←Real.exp_add]; congr 1; ring

/-- Every executed public tau=1 block is charged on its complete tape. -/
theorem execute_work_paid {d : ℕ} (h : ℝ) (v : ℝ≥0) (G : Point d → Point d)
    (x : Point d) (ω : CoolingExecutable.FullTape Q d h v P.K) :
    (((Oracle.traceCounts (CoolingExecutable.execute Q h v P.K G x ω).trace).queries+
      (Oracle.traceCounts (CoolingExecutable.execute Q h v P.K G x ω).trace).gaussianBlocks:ℕ):ℝ)≤Real.exp (P.y/32) :=
  (CoolingSourceWork.executed_full_work_paid P hK hc hsmall hC baseHy
    (CoolingPrescribedPayments.mesh P) (CoolingPrescribedPayments.nodes P) h v G x ω).trans
    (budget_paid P hK hc hsmall hC hy)

/-- Complete executed phase-plus-cooling cost with every inventory absorbed.
The finite phase/cooling horizons remain explicit for the final schedule. -/
theorem total_work_paid {d : ℕ} (N L : ℕ) (labels : Fin N → ℕ)
    (Γ : ℝ) (G : Point d → Point d)
    (a : ∀ i, (Point d × Point d) × ClockFinitePhaseKernel.Draw P hR hc hsmall (d:=d) (labels i))
    (v : Fin L → ℝ≥0) (x : Fin L → Point d)
    (ω : ∀ i, CoolingExecutable.FullTape Q d P.delta (v i) P.K) :
    (∑ i : Fin N, (((Oracle.traceCounts (ClockFinitePhaseWork.execute P hR hc hsmall (labels i) Γ G (a i)).trace).queries+
      (Oracle.traceCounts (ClockFinitePhaseWork.execute P hR hc hsmall (labels i) Γ G (a i)).trace).gaussianBlocks:ℕ):ℝ)) +
    (∑ i : Fin L, (((Oracle.traceCounts (CoolingExecutable.execute Q P.delta (v i) P.K G (x i) (ω i)).trace).queries+
      (Oracle.traceCounts (CoolingExecutable.execute Q P.delta (v i) P.K G (x i) (ω i)).trace).gaussianBlocks:ℕ):ℝ)) ≤
      (4*(N:ℝ)+(L:ℝ))*Real.exp (P.y/32) := by
  have hb := SourcePhaseCoolingWork.total_full_work_le P hc hsmall hK hC hy N L labels Γ G a v x ω
  have hcold := mul_le_mul_of_nonneg_left (budget_paid P hK hc hsmall hC hy) (Nat.cast_nonneg L)
  have hy0 := (CubicSchedulePayments.prerequisites P hK hc hsmall hC baseHy).1
  have hE : 1≤Real.exp (P.y/32) := Real.one_le_exp_iff.mpr (by positivity)
  have hN := mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg N)
  exact hb.trans (by nlinarith)
end AcceleratedLogConcave.Root.CoolingSourceWorkPayment
