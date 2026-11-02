import AcceleratedLogConcave.Root.OuterRootOutputQuadrature
import AcceleratedLogConcave.Numerics.SmoothConditionalOrder

/-! Scalar payment by the actual public root inventory. Constants retain their
order dependence; the bound does not silently assert a universal smallness
threshold or the final warm-start accuracy. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Root.ClockQuadraturePower
open Numerics.ConditionalSmoothing

/-- The prescribed ceil mesh and order supply exactly K+4 powers of h. -/
theorem inverse_cells_power {h : ℝ} (hh : 0 < h) (K : ℕ) :
    ((ClockSchedule.sourceCells h : ℝ)⁻¹)^(ClockSchedule.sourceOrder K) ≤ h^(K+4) := by
  have hc : h^(-1/128:ℝ) ≤ (ClockSchedule.sourceCells h:ℝ) := Nat.le_ceil _
  have hi : (ClockSchedule.sourceCells h:ℝ)⁻¹ ≤ h^(1/128:ℝ) := by
    calc
      _ ≤ (h^(-1/128:ℝ))⁻¹ := inv_anti₀ (Real.rpow_pos_of_pos hh _) hc
      _ = _ := by rw [← Real.rpow_neg hh.le]; congr 1; norm_num
  have H := pow_le_pow_left₀ (inv_nonneg.mpr (Nat.cast_nonneg _)) hi
    (ClockSchedule.sourceOrder K)
  refine H.trans_eq ?_
  rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le]
  have he : (1/128:ℝ) * (ClockSchedule.sourceOrder K:ℝ) = (K+4:ℕ) := by
    simp only [ClockSchedule.sourceOrder, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    ring
  rw [he, Real.rpow_natCast]

/-- Explicit order constant; dimension appears only as its square root. -/
def orderConstant (K : ℕ) : ℝ :=
  4 * conditionalOrderEnvelope (ClockSchedule.sourceOrder K) *
    (4/3)^(ClockSchedule.sourceOrder K) /
      (ClockSchedule.sourceOrder K).factorial

theorem orderConstant_nonneg (K : ℕ) : 0 ≤ orderConstant K := by
  unfold orderConstant
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    (conditionalOrderEnvelope_nonneg _)) (by positivity)) (by positivity)

/-- The whole prescribed row budget has its actual h power. No sampling,
conditional-error or smoothness hypothesis is used in this scalar calculation. -/
theorem rowBudget_le {h : ℝ} (hh : 0 < h) (K D : ℕ) (clock : ClockLaw.Clock) :
    let n := ClockSchedule.sourceOrder K - 1
    (ClockSchedule.sourceCells h : ℝ) *
      (2*((clock:ℝ)/(ClockSchedule.sourceCells h:ℝ))^(n+2)*
        ((2*h^2)*materialOrderFactor D n / (3/4)^(n+1)) /
          ((n+1).factorial:ℝ)) ≤
      orderConstant K * Real.sqrt (D:ℝ) * h^(K+6) := by
  dsimp only
  let M := ClockSchedule.sourceOrder K
  let J : ℝ := ClockSchedule.sourceCells h
  have hM : 0 < M := ClockSchedule.sourceOrder_pos K
  have hJ : 0 < J := Nat.cast_pos.mpr (ClockSchedule.sourceCells_pos hh)
  have hn : M-1+1=M := by omega
  have hn2 : M-1+2=M+1 := by omega
  change J * (2*((clock:ℝ)/J)^(M-1+2)*
    ((2*h^2)*materialOrderFactor D (M-1) / (3/4)^(M-1+1)) /
      ((M-1+1).factorial:ℝ)) ≤ _
  rw [hn,hn2]
  have hg : J*((clock:ℝ)/J)^(M+1) ≤ (J⁻¹)^M := by
    calc
      _ ≤ J*(1/J)^(M+1) := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (div_nonneg clock.2.1 hJ.le)
          (div_le_div_of_nonneg_right (clock.2.2.trans (by norm_num)) hJ.le) _) hJ.le
      _ = _ := by rw [one_div, pow_succ]; field_simp
  have hm := materialOrderFactor_le D (M-1)
  rw [hn] at hm
  have hc : 0 ≤ 4*h^2*materialOrderFactor D (M-1)/(3/4)^M/(M.factorial:ℝ) := by
    exact div_nonneg (div_nonneg
      (mul_nonneg (by positivity) (materialOrderFactor_nonneg _ _)) (by positivity))
      (by positivity)
  calc
    _ = (J*((clock:ℝ)/J)^(M+1)) *
        (4*h^2*materialOrderFactor D (M-1)/(3/4)^M/(M.factorial:ℝ)) := by ring
    _ ≤ (J⁻¹)^M * (4*h^2*materialOrderFactor D (M-1)/(3/4)^M/(M.factorial:ℝ)) :=
      mul_le_mul_of_nonneg_right hg hc
    _ ≤ h^(K+4) * (4*h^2*materialOrderFactor D (M-1)/(3/4)^M/(M.factorial:ℝ)) :=
      mul_le_mul_of_nonneg_right (inverse_cells_power hh K) hc
    _ ≤ h^(K+4) * (4*h^2*(Real.sqrt (D:ℝ)*conditionalOrderEnvelope M)/(3/4)^M/(M.factorial:ℝ)) := by
      gcongr
    _ = orderConstant K * Real.sqrt (D:ℝ) * h^(K+6) := by
      unfold orderConstant
      change _ = 4*conditionalOrderEnvelope M*(4/3)^M/(M.factorial:ℝ)*_ * _
      rw [show K+6=K+4+2 by omega, pow_add]
      have hp : ((3/4:ℝ)^M)⁻¹ = (4/3:ℝ)^M := by rw [← inv_pow]; norm_num
      rw [div_eq_mul_inv _ ((3/4:ℝ)^M), hp]
      ring

/-- Prescribed original-data endpoint quadrature, with explicit order constant,
dimension and h rate. This is a reference defect, not executed-child accuracy. -/
theorem source_endpoint_error {ι : Type*} [Fintype ι]
    {V : EuclideanSpace ℝ ι → ℝ} (hV : ContDiff ℝ 2 V)
    {m h : ℝ} (hm : 0 < m) (hh : 0 < h)
    (hlo : ∀ z v, m * ‖v‖^2 ≤ fderiv ℝ (fderiv ℝ V) z v v)
    (hup : ∀ z v, fderiv ℝ (fderiv ℝ V) z v v ≤ ‖v‖^2)
    (hsmall : h ≤ 1/2) (K : ℕ) (clock : ClockLaw.Clock) :
    let F := OuterRootFlowIdentification.family hV hm hh hlo hup
    let d := OuterRootOriginalData.data hV hh
      (OuterRootFlowIdentification.lower_nonneg hm hlo) hup
    ‖(OuterRootStrongJetLp.jetLp F d (Real.sqrt h)⁻¹ 0 (clock:ℝ) -
        OuterRootStrongJetLp.jetLp F d (Real.sqrt h)⁻¹ 0 0) -
      ∑ j : ClockCollocation.MainIndex h K,
        ClockSchedule.weight (ClockSchedule.sourceCells h) (ClockSchedule.sourceOrder K) clock j •
          OuterRootStrongJetLp.jetLp F d (Real.sqrt h)⁻¹ 1 (ClockCollocation.u h K clock j)‖ ≤
      orderConstant K * Real.sqrt (Fintype.card ι:ℝ) * h^(K+6) :=
  (OuterRootOutputQuadrature.source_endpoint_defect hV hm hh hlo hup hsmall K clock).trans
    (rowBudget_le hh K (Fintype.card ι) clock)

end AcceleratedLogConcave.Root.ClockQuadraturePower
