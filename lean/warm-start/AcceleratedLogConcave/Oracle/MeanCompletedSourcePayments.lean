import AcceleratedLogConcave.Oracle.MeanCompletedSourceRms
import AcceleratedLogConcave.Oracle.MeanPrescribedRecursiveBudget

/-! Numerical payment of the actual completed-source RMS budget. Square-root
node moments are compared through the literal finite child row and forcing
sum, before the prescribed recursive scalar payment is applied. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace AcceleratedLogConcave.Oracle.MeanCompletedSourcePayments
open Numerics Numerics.MeanFlowLp Numerics.MeanCollocationLp Numerics.AffineGraph

/-- Positivity makes the actual maximum row norm monotone in each child
payment. No moment maximum or independence is substituted. -/
theorem childRowBudget_mono {n : ℕ} (A : Fin n → Fin n → ℝ)
    (ε ε' : ℕ → Fin n → ℝ) (k : ℕ)
    (h0 : ∀ i,0≤ε k i) (hle : ∀ i,ε k i≤ε' k i) :
    SharedLayerRms.childRowBudget A ε k≤SharedLayerRms.childRowBudget A ε' k := by
  unfold SharedLayerRms.childRowBudget
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
  intro i
  rw [Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (h0 j))]
  calc
    _ ≤ ∑ j,|A i j| * ε' k j := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hle j) (abs_nonneg _)
    _ ≤ |∑ j,|A i j| * ε' k j| := le_abs_self _
    _ ≤ _ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (fun l => ∑ j,|A l j| * ε' k j) i

variable {D m n : ℕ} (d : MeanFlowLp.Data (Fin D) m) (nodes : Fin n ≃ d.G.MeanNode)
local notation "B" => Gibbs.primitiveScale d.F d.x

/-- Payment monotonicity through the same finite executed source recurrence. -/
theorem sourceMainBudget_mono (h₀ : ℝ) (N : ℕ) (κ : ℝ≥0) (aRow Eprivate : ℝ)
    (ha : 0≤aRow) (ε ε' : ℕ → Fin n → ℝ)
    (h0 : ∀ k i,0≤ε k i) (hle : ∀ k i,ε k i≤ε' k i) :
    MeanSourceSharpRms.sourceMainBudget d nodes h₀ N κ aRow Eprivate ε≤
      MeanSourceSharpRms.sourceMainBudget d nodes h₀ N κ aRow Eprivate ε' := by
  unfold MeanSourceSharpRms.sourceMainBudget
  apply add_le_add_right
  unfold Collocation.forcingSum
  apply Finset.sum_le_sum
  intro k hk
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (mul_nonneg κ.coe_nonneg ha) _)
  apply add_le_add_right
  apply childRowBudget_mono _ _ _ k
  · intro i
    unfold SourceMeanExecutionRms.finiteBudget
    split_ifs <;> first | exact h0 k i | exact le_rfl
  · intro i
    unfold SourceMeanExecutionRms.finiteBudget
    split_ifs <;> first | exact hle k i | exact le_rfl

/-- The main payment retains the actual original-data moment bound; its
square root is paid without dividing by a lower amplitude or source scale. -/
theorem mainPayment_le (h₀ : ℝ) (amplitude : ℕ → Fin n → ℝ) (k : ℕ) (i : Fin n)
    (ha : 0≤amplitude k i)
    (hscale : MeanAllNodeMoments.scaleSquareBudget d h₀≤(64*B)^2) :
    MeanCompletedSourceRms.mainPayment d h₀ amplitude k i≤amplitude k i*(64*B) := by
  unfold MeanCompletedSourceRms.mainPayment
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg ha (mul_nonneg (by norm_num) (Gibbs.primitiveScale_nonneg _ _)),?_⟩
  exact (mul_le_mul_of_nonneg_left hscale (sq_nonneg _)).trans_eq (by ring)

/-- Exact final square-root normalization at any nonnegative lower amplitude. -/
theorem finalPayment_eq (amplitude : Fin m → ℝ) (i : Fin m) (ha : 0≤amplitude i) :
    MeanCompletedSourceRms.finalPayment d amplitude i=
      amplitude i*Real.sqrt (MeanBenchmarkMoments.finalScaleSquareBudget d) := by
  unfold MeanCompletedSourceRms.finalPayment
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq ha]

/-- The actual RMS budget is bounded by the same finite recurrence with a
larger main payment. Final moments stay in their exact physical normalization. -/
theorem outputBudget_le (h₀ : ℝ) (N : ℕ) (κ κf : ℝ≥0) (aRow Eprivate : ℝ)
    (ha : 0≤aRow) (amplitude : ℕ → Fin n → ℝ) (amplitudeFinal : Fin m → ℝ)
    (ε : ℕ → Fin n → ℝ)
    (hle : ∀ k i,MeanCompletedSourceRms.mainPayment d h₀ amplitude k i≤ε k i)
    (haf : ∀ i,0≤amplitudeFinal i) :
    MeanCompletedSourceRms.outputBudget d nodes N h₀ κ κf aRow Eprivate amplitude amplitudeFinal≤
      (∑ i : Fin m,|GaussLegendre.weight m i|)*((κf:ℝ)*MeanSourceSharpRms.sourceMainBudget d nodes h₀ N κ aRow Eprivate ε)+
        (∑ i : Fin m,|GaussLegendre.weight m i| * (amplitudeFinal i*Real.sqrt (MeanBenchmarkMoments.finalScaleSquareBudget d)))+
        MeanOriginalBounds.quadratureBudget d := by
  have hm := sourceMainBudget_mono d nodes h₀ N κ aRow Eprivate ha
    (MeanCompletedSourceRms.mainPayment d h₀ amplitude) ε (fun _ _ => Real.sqrt_nonneg _) hle
  unfold MeanCompletedSourceRms.outputBudget
  apply add_le_add_left
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm κf.coe_nonneg)
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  · apply Finset.sum_le_sum
    intro i _
    rw [finalPayment_eq d amplitudeFinal i (haf i)]

section Prescribed
open CubicExecutableWorkShift RecursiveCall ScalarSchedulePayment
variable (P : SourceSchedule) (hK : 10≤P.K) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (hC : 8≤P.Csch) (hy : MeanSourceScalarAbsorption.threshold P≤P.y)
local notation "privateHy" => MeanSourceScalarAbsorption.private_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy
local notation "hR" => MeanPrescribedRecursiveBudget.radiusGuard P hK hc hsmall hC hy
local notation "C" => source P hR
variable {F : Point D → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0≤ell)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ F) z v v≤ell*‖v‖^2)
  (x : Point D) {r0 σ0 : ℝ} (hr0 : 0<r0) (hr1 : r0≤1) (hσ0 : 0<σ0)
  (hellδ : ell≤P.delta) (hrootRatio : ell*(r0/σ0)≤P.delta)
  {p : State} {depth cost : ℕ}

include hrootRatio in
/-- The exact square-root payments in the actual completed-source RMS
bound satisfy recursive constant four on every original reachable call.
All moment, row, transient and original analytic payments are derived. -/
theorem source_output_budget_le
    (hp : Path (source P (MeanPrescribedRecursiveBudget.radiusGuard P hK hc hsmall hC hy))
      (PrescribedRecursiveStability.root P r0 σ0) p depth cost) :
    let hroot := MeanPrescribedRecursiveBudget.root_radius P hell hr0 hr1 hellδ
    let datum := PrescribedMeanNumericalData.reachableDatum P hF hell hlo hup x hK hc hsmall hC privateHy hr0 hσ0 hroot hp
    let κ := PrivateSourceScalarAbsorption.twiceNonneg ell hell
    let aRow := SourceMeanExecutable.rowBound (m := P.m) p.radius p.width P.delta P.t P.w
    let sigmaM := CovarianceSetup.sigma (ScalarSchedulePayment.n P hR) (RecursiveMeanPublicTable.centerNoise p.radius P.R P.Ds) aRow
    let amain := fun (_ : ℕ) (_ : Fin (ScalarSchedulePayment.n P hR)) => 4*sigmaM*P.delta^(p.precision-1/4)
    let afinal := fun (_ : Fin P.m) => 4*RecursiveMeanPublicTable.finalWidth P.R p.width*P.delta^(p.precision-P.t)
    let Eprivate := 3*P.R*P.delta^(p.precision-1/4)*Gibbs.primitiveScale F x
    MeanCompletedSourceRms.outputBudget datum (C).nodes P.NP P.h0 κ κ aRow Eprivate amain afinal≤
      4*p.width*P.delta^p.precision*Gibbs.primitiveScale F x := by
  dsimp only
  let hroot := MeanPrescribedRecursiveBudget.root_radius P hell hr0 hr1 hellδ
  let datum := PrescribedMeanNumericalData.reachableDatum P hF hell hlo hup x hK hc hsmall hC privateHy hr0 hσ0 hroot hp
  let κ := PrivateSourceScalarAbsorption.twiceNonneg ell hell
  let aRow := SourceMeanExecutable.rowBound (m := P.m) p.radius p.width P.delta P.t P.w
  let sigmaM := CovarianceSetup.sigma (ScalarSchedulePayment.n P hR) (RecursiveMeanPublicTable.centerNoise p.radius P.R P.Ds) aRow
  let amain := fun (_ : ℕ) (_ : Fin (ScalarSchedulePayment.n P hR)) => 4*sigmaM*P.delta^(p.precision-1/4)
  let afinal := fun (_ : Fin P.m) => 4*RecursiveMeanPublicTable.finalWidth P.R p.width*P.delta^(p.precision-P.t)
  let Eprivate := 3*P.R*P.delta^(p.precision-1/4)*Gibbs.primitiveScale F x
  let ε := fun (_ : ℕ) (_ : Fin (ScalarSchedulePayment.n P hR)) => 256*sigmaM*P.delta^(p.precision-1/4)*Gibbs.primitiveScale F x
  have hm := P.m_ge_two hc hsmall (by linarith : 1≤P.Csch)
  have hpos := hp.positive (by omega : 0<P.m) P.Ds_pos P.delta_pos hr0 hσ0
  have ha : 0<aRow := MeanRecursiveChronologicalCoupling.row_pos P.delta P.t P.w p.radius p.width hpos.1 hpos.2 P.delta_pos
  have hρ := RecursiveExecutableDomain.center_noise_pos (C).M p.radius P.Ds hpos.1 P.Ds_pos
  have hσM : 0≤sigmaM := (CovarianceSetup.sigma_pos (RecursiveExecutableDomain.mean_inventory_pos (C).M (C).nodes) hρ ha).le
  have hB : 0≤Gibbs.primitiveScale F x := Gibbs.primitiveScale_nonneg _ _
  have hd : P.delta≤1 := (PrivateSourceScalarAbsorption.delta_le_hundredth P hK hc
    (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) privateHy).trans (by norm_num)
  have hrp := PrescribedTerminalAccuracy.radius_le_root hp (by omega) P.Ds_pos P.delta_pos hr0 hσ0
  change p.radius≤r0 at hrp
  have hrp1 : p.radius≤1 := hrp.trans hr1
  have hslope : ell*p.radius≤1 := by
    have h := mul_le_mul_of_nonneg_left hrp1 hell
    linarith
  have hrootSlope : ell*r0≤1 := by
    have h := mul_le_mul_of_nonneg_left hr1 hell
    linarith
  have hmesh := PrescribedMeanNumericalData.reachable_mesh P hF hell hlo hup x hK hc hsmall hC privateHy hr0 hσ0 hroot hp
  have hhalf := PrescribedMeanNumericalData.reachable_contraction P hF hell hlo hup x hK hc hsmall hC privateHy hr0 hσ0 hroot hrootRatio hp
  have hresScale := MeanPrescribedOriginalPayments.reachable_residual_scale P hK hc hsmall hC hy hF hell hlo hup x
    hr0 hσ0 hroot hrootRatio hrootSlope hp
  have hscale := MeanSourceScaleMoments.main_scale_square_le datum P.h0 hrp1 hslope hmesh hhalf hresScale
  have hpayment (k : ℕ) (i : Fin (ScalarSchedulePayment.n P hR)) : MeanCompletedSourceRms.mainPayment datum P.h0 amain k i≤ε k i := by
    have h := mainPayment_le datum P.h0 amain k i (by dsimp [amain]; positivity [P.delta_pos]) hscale
    refine h.trans_eq ?_
    change (4*sigmaM*P.delta^(p.precision-1/4))*(64*Gibbs.primitiveScale F x)=
      256*sigmaM*P.delta^(p.precision-1/4)*Gibbs.primitiveScale F x
    ring
  have haf (i : Fin P.m) : 0≤afinal i := by
    dsimp [afinal]
    unfold RecursiveMeanPublicTable.finalWidth RecursiveMeanPublicTable.finalNoise
    positivity [P.R_pos,P.delta_pos,hpos.2]
  have hmono := outputBudget_le datum (C).nodes P.h0 P.NP κ κ aRow Eprivate ha.le amain afinal ε hpayment haf
  exact hmono.trans (MeanPrescribedRecursiveBudget.source_budget_le P hK hc hsmall hC hy hF hell hlo hup x
    hr0 hr1 hσ0 hellδ hrootRatio hp)

end Prescribed
end AcceleratedLogConcave.Oracle.MeanCompletedSourcePayments
