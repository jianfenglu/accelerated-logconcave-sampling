import AcceleratedLogConcave.Numerics.SourceUniformOutput

/-! The initial direct-vector payment after applying the actual contraction.
This removes the inverse-mesh row mass from the output estimate without
asserting the stronger physical displacement statement of C.6. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Numerics.SourceContractedOutput
open MeanFlowLp MeanResidualBridge MeanCollocationLp AffineGraph
open SmoothQuantitativeAssembly SmoothQuadraturePayments SourceNumericalData
variable {D m : ℕ}

/-- The actual direct-vector seed payment contains only the original gradient
and Gaussian second moment. -/
theorem seed_payment (d : Data (Fin D) m) :
    d.ell*directBudget d+meanBudget d ≤
      17*d.ell*d.r*Real.sqrt (D:ℝ)+(11:ℝ)/2*‖gradient d.F d.x‖ := by
  have he : d.ell*directBudget d+meanBudget d =
      17*d.ell*d.r*Real.sqrt (D:ℝ)+(1+9*d.ell*d.r^2)*‖gradient d.F d.x‖ := by
    simp only [directBudget, meanBudget, radiusBudget, seedBudget,
      finrank_euclideanSpace, Fintype.card_fin]
    ring
  rw [he]
  have h := mul_le_mul_of_nonneg_right d.hsmall (norm_nonneg (gradient d.F d.x))
  nlinarith

theorem output_bound (P : Inputs (Fin D) m) (hm : 2 ≤ m)
    (hδone : P.δ ≤ 1) (hhhalf : P.δ^P.w ≤ 1/2)
    (hwt : P.w ≤ P.t) (ht : P.t ≤ (1:ℝ)/60)
    {b S : ℝ} (hb : (1:ℝ)/2 ≤ b) (hS : 1 ≤ S)
    (hsizeR : P.ell*P.r^2 ≤ S*P.δ^b)
    (hsizeS : P.ell*P.r/P.sigma ≤ S*P.δ^b)
    (hres : P.δ ≤ (520*(m:ℝ)^5*S)^(-12:ℝ))
    (hvelocity : VelocityBounds (data P)) (hangle : AngleBounds (data P)) (N : ℕ) :
    ‖output (data P) N - terminalTarget (data P)‖ ≤
      (P.ell*directBudget (data P)+meanBudget (data P))*P.δ^(((N:ℝ)+1)/3) +
      4*P.ell*P.r*Real.sqrt (D:ℝ)*SmoothInventoryDimension.A m*
        P.δ^(SmoothRowPayments.exponent m P.w P.t) +
      (2*centerCoefficient (data P)/(m.factorial:ℝ))*P.δ^((m:ℝ)/3) := by
  let d := data P
  let M := P.ell*directBudget d+meanBudget d
  let R := P.r*Real.sqrt (D:ℝ)*SmoothInventoryDimension.A m*
    P.δ^(SmoothRowPayments.exponent m P.w P.t)
  let p := (P.δ^((1:ℝ)/3)/2)^N
  have hmesh := data_meshConditions P hm hδone hhhalf
  have hq := SmoothInitialError.contraction_le_resolution d (P.δ^P.w) hmesh
    P.hδ hδone P.hw.le hwt ht hb hS rfl rfl hsizeR hsizeS hres
  have hδ0 := P.hδ.le
  have hthird : P.δ^((1:ℝ)/3) ≤ 1 := Real.rpow_le_one hδ0 hδone (by norm_num)
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := by
    apply pow_le_one₀ (by positivity)
    linarith
  have hpN : p ≤ P.δ^((N:ℝ)/3) := by
    have he : (P.δ^((1:ℝ)/3))^N = P.δ^((N:ℝ)/3) := by
      rw [SmoothStepPayments.step_power P.hδ]
      congr 1
      ring
    rw [← he]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [Real.rpow_nonneg hδ0 ((1:ℝ)/3)]
  have hM : 0 ≤ M := by
    dsimp [M, directBudget, meanBudget, radiusBudget, seedBudget, d]
    have := P.hell
    have := P.hr.le
    positivity
  have hR0 : 0 ≤ R := by
    dsimp [R]
    have := P.hr.le
    have := SmoothInventoryDimension.A_nonneg m
    positivity
  have hq0 := contraction_nonneg d (P.δ^P.w) hmesh
  have hqM := mul_le_mul_of_nonneg_right hq hM
  have hqMp := mul_le_mul_of_nonneg_left hqM hp0
  have hpM := mul_le_mul_of_nonneg_right hpN
    (mul_nonneg (Real.rpow_nonneg hδ0 ((1:ℝ)/3)) hM)
  have hpower : P.δ^((N:ℝ)/3)*P.δ^((1:ℝ)/3) = P.δ^(((N:ℝ)+1)/3) := by
    rw [← Real.rpow_add P.hδ]
    congr 1
    ring
  have hinit : p*(2*contraction d (P.δ^P.w)*M) ≤ M*P.δ^(((N:ℝ)+1)/3) := by
    calc
      _ ≤ p*(P.δ^((1:ℝ)/3)*M) := by nlinarith
      _ ≤ P.δ^((N:ℝ)/3)*(P.δ^((1:ℝ)/3)*M) := hpM
      _ = _ := by rw [← mul_assoc, hpower]; ring
  have herr := mul_le_mul_of_nonneg_right hp1 (mul_nonneg P.hell hR0)
  have ho := SourceUniformOutput.output_bound P hm hδone hhhalf hwt ht hb hS
    hsizeS hres hvelocity hangle hsizeR N
  apply ho.trans
  change P.ell*(p*(2*(rowMass d (P.δ^P.w)*M+R))+2*R)+_ ≤ _
  have heq : P.ell*rowMass d (P.δ^P.w) = contraction d (P.δ^P.w) := rfl
  calc
    _ = p*(2*contraction d (P.δ^P.w)*M)+(2*p*P.ell*R+2*P.ell*R)+
        (2*centerCoefficient d/(m.factorial:ℝ))*P.δ^((m:ℝ)/3) := by rw [← heq]; ring
    _ ≤ M*P.δ^(((N:ℝ)+1)/3)+4*P.ell*R+
        (2*centerCoefficient d/(m.factorial:ℝ))*P.δ^((m:ℝ)/3) := by nlinarith
    _ = _ := by dsimp [M,R]; ring

end AcceleratedLogConcave.Numerics.SourceContractedOutput
