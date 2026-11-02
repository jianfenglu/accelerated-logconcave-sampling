import AcceleratedLogConcave.Root.ClockPhysicalRms

/-! Explicit scalar payment of the actual physical root RMS budget. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
open MeasureTheory
open scoped BigOperators
namespace AcceleratedLogConcave.Root.ClockPhysicalRmsPayment
open Oracle Oracle.TapeLowering Oracle.CanonicalTapeMeasurability ClockNoisyLayer
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
variable (P : SourceSchedule) (clock : ClockLaw.Clock) {d : ℕ}
local notation "rf" => ClockCollocation.rF P.delta
local notation "width" => ClockRetainedFinalSplice.width P clock
local notation "w" => ClockRetainedFinalSplice.weight P clock
local notation "pc" => ClockPhysicalReadout.physicalCoefficient P clock
local notation "B" => Real.sqrt (d:ℝ)*P.delta^P.K

private theorem weight_nonneg (i : Index P) : 0≤w i :=
  ClockSchedule.weight_nonneg _ _ clock i
private theorem weights_sum : ∑ i : Index P,w i=(clock:ℝ) :=
  ClockSchedule.sum_weight _ _ (ClockSchedule.sourceCells_pos P.delta_pos) (ClockSchedule.sourceOrder_pos P.K) clock
private theorem abs_coefficient (i : Index P) : |pc i|=ClockPublicSetup.s*rf*w i := by
  rw [ClockPhysicalReadout.physicalCoefficient_source,abs_neg,abs_mul,abs_mul,
    abs_of_nonneg (by norm_num [ClockPublicSetup.s]),abs_of_nonneg (rF_pos P).le,
    abs_of_nonneg (weight_nonneg P clock i)]
private theorem coefficient_sum : ∑ i : Index P,|pc i|=ClockPublicSetup.s*rf*(clock:ℝ) := by
  simp_rw [abs_coefficient]
  rw [← Finset.mul_sum,weights_sum]

private theorem child_payment_le (i : Index P) :
    Real.sqrt ((4*width i*P.delta^(P.K:ℝ))^2*(10*(d:ℝ)))≤4*width i*P.delta^P.K*(4*Real.sqrt (d:ℝ)) := by
  have hamp : 0≤4*width i*P.delta^(P.K:ℝ) := mul_nonneg
    (mul_nonneg (by norm_num) (ClockRetainedFinalSplice.width_pos P clock i).le) (Real.rpow_nonneg P.delta_pos.le _)
  have hs : Real.sqrt 10≤(4:ℝ) := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤10),Real.sqrt_nonneg 10]
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hamp,Real.sqrt_mul (by norm_num : (0:ℝ)≤10)]
  simpa only [Real.rpow_natCast] using mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg (d:ℝ))) hamp

private theorem weighted_child_payment_le :
    (∑ i : Index P,|pc i| * Real.sqrt ((4*width i*P.delta^(P.K:ℝ))^2*(10*(d:ℝ))))≤16*B := by
  have hs : 0≤B := mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg P.delta_pos.le _)
  have hn : 0≤ClockPublicSetup.noise := by unfold ClockPublicSetup.noise; positivity
  have hn1 : ClockPublicSetup.noise≤1 := by
    unfold ClockPublicSetup.noise
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤3),Real.sqrt_nonneg 3]
  calc
    _ ≤ ∑ i : Index P,|pc i| * (4*width i*P.delta^P.K*(4*Real.sqrt (d:ℝ))) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (child_payment_le P clock i) (abs_nonneg _)
    _ = 16*ClockPublicSetup.noise*(clock:ℝ)*B := by
      have he (i : Index P) : |pc i| * (4*width i*P.delta^P.K*(4*Real.sqrt (d:ℝ))) =
          (16*ClockPublicSetup.noise*B)*w i := by
        rw [abs_coefficient]
        calc
          _ = (16*B)*(ClockPublicSetup.s*rf*width i)*w i := by ring
          _ = _ := by rw [ClockPhysicalReadout.width_scale]; ring
      simp_rw [he]
      rw [← Finset.mul_sum,weights_sum]
      ring
    _ ≤ _ := by
      have hclock : (clock:ℝ)≤1 := clock.2.2.trans (by norm_num)
      have hproduct : ClockPublicSetup.noise*(clock:ℝ)≤1 :=
        (mul_le_mul hn1 hclock clock.2.1 (by norm_num)).trans_eq (one_mul _)
      nlinarith [mul_le_mul_of_nonneg_right hproduct hs]

/-- The true source child widths, weights and resolution give a universal cap. -/
theorem budget_le (hc : 0<P.csch) (hdelta : P.delta≤1/2)
    (hyQuad : ClockQuadratureResolution.threshold P.K≤P.y) :
    ClockPhysicalRms.budget (d := d) P clock≤32*Real.sqrt (d:ℝ)*P.delta^P.K := by
  have hB : 0≤B := mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg P.delta_pos.le _)
  have hmain := ClockMainRmsPayment.budget_le (d := d) P clock hc hdelta hyQuad
  have hmain0 := ClockMainRms.budget_nonneg (d := d) P clock
  have hcoef : (∑ i : Index P,|pc i|)≤ClockPublicSetup.s*rf := by
    rw [coefficient_sum]
    exact mul_le_of_le_one_right (mul_nonneg (show (0:ℝ)≤ClockPublicSetup.s by norm_num [ClockPublicSetup.s]) (rF_pos P).le)
      (clock.2.2.trans (by norm_num))
  have hterm : (∑ i : Index P,|pc i|)*(2*P.delta*ClockMainRms.budget (d := d) P clock)≤2*B := by
    have hbound := mul_le_mul hcoef (mul_le_mul_of_nonneg_left hmain (mul_nonneg (show (0:ℝ)≤2 by norm_num) P.delta_pos.le))
      (mul_nonneg (mul_nonneg (show (0:ℝ)≤2 by norm_num) P.delta_pos.le) hmain0)
      (mul_nonneg (show (0:ℝ)≤ClockPublicSetup.s by norm_num [ClockPublicSetup.s]) (rF_pos P).le)
    have heq : (ClockPublicSetup.s*rf)*(2*P.delta*(4*rf*Real.sqrt (d:ℝ)*P.delta^P.K))=8*P.delta^2*B := by
      have hr : rf^2=2*P.delta := Real.sq_sqrt (mul_pos (by norm_num) P.delta_pos).le
      calc
        _ = (8*ClockPublicSetup.s*P.delta*rf^2)*B := by ring
        _ = _ := by rw [hr]; unfold ClockPublicSetup.s; ring
    exact hbound.trans (heq.trans_le (mul_le_mul_of_nonneg_right (by nlinarith [P.delta_pos] : 8*P.delta^2≤2) hB))
  have hquad : ClockPublicSetup.s*ClockQuadraturePower.orderConstant P.K*Real.sqrt (d:ℝ)*P.delta^(P.K+6)≤B/2 := by
    have h := mul_le_mul_of_nonneg_left (ClockQuadratureResolution.endpoint_payment P hyQuad)
      (mul_nonneg (show (0:ℝ)≤ClockPublicSetup.s by norm_num [ClockPublicSetup.s]) (Real.sqrt_nonneg (d:ℝ)))
    dsimp only [ClockPublicSetup.s] at h ⊢
    nlinarith
  have hcTerm := weighted_child_payment_le (d := d) P clock
  unfold ClockPhysicalRms.budget
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib,← Finset.sum_mul]
  nlinarith

open MeasureTheory ProbabilityTheory
variable (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (label : ℕ) (hK : 10≤P.K) (hC : 8≤P.Csch)
  (hy : CubicScheduleThreshold.threshold P≤P.y)
  {V : Point d→ℝ} (hV : ContDiff ℝ 2 V) {m : ℝ} (hm : 0<m)
  (hlo : ∀ z v,m*‖v‖^2≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
  (hyMean : MeanSourceScalarAbsorption.threshold P≤P.y)

/-- Literal implemented/reference root error, with every supplier closed. -/
theorem source_error_bound (hyQuad : ClockQuadratureResolution.threshold P.K≤P.y) :
    ∃ h : MemLp (ClockPhysicalRms.actualError P hR hc hsmall clock label hK hC hy hV hm hlo hup) 2
        (ClockFinalRms.law P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean),
      ‖h.toLp (ClockPhysicalRms.actualError P hR hc hsmall clock label hK hC hy hV hm hlo hup)‖≤
        32*Real.sqrt (d:ℝ)*P.delta^P.K ∧
      (∫ z,‖ClockPhysicalRms.actualError P hR hc hsmall clock label hK hC hy hV hm hlo hup z‖^2
        ∂ClockFinalRms.law P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean)≤
        (32*Real.sqrt (d:ℝ)*P.delta^P.K)^2 := by
  obtain ⟨h,hb,_⟩ := ClockPhysicalRms.actual_error_bound P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean
  have hnorm := hb.trans (budget_le (d := d) P clock hc (FinalMeanScheduledData.delta_half P hK hc hsmall hC hy) hyQuad)
  refine ⟨h,hnorm,?_⟩
  have hs := (sq_le_sq₀ (norm_nonneg (h.toLp _)) (show 0≤32*Real.sqrt (d:ℝ)*P.delta^P.K from mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (pow_nonneg P.delta_pos.le _))).2 hnorm
  exact (Analysis.DominatedLp.norm_sq_toLp h).symm.le.trans hs

end AcceleratedLogConcave.Root.ClockPhysicalRmsPayment
