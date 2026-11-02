import AcceleratedLogConcave.Root.ClockQuadraturePower

/-! Prescribed partial-row quadrature for every actual root main node on the
original Gaussian-start common seed. No derivative or defect budget is assumed. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory
open scoped BigOperators
namespace AcceleratedLogConcave.Root.OuterRootMainQuadrature
open OuterRootFlowIdentification OuterRootStrongJetLp
variable {ι : Type*} [Fintype ι]
  {V : EuclideanSpace ℝ ι → ℝ} (hV : ContDiff ℝ 2 V)
  {m h : ℝ} (hm : 0<m) (hh : 0<h)
  (hlo : ∀ z v,m*‖v‖^2≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
  (hsmall : h≤1/2) (K : ℕ) (clock : ClockLaw.Clock)

include hsmall in
/-- Full order dependence and precision power for every prescribed partial row. -/
theorem source_partial_defect (a : ℝ) (ha : a∈Icc (0:ℝ) 1) :
    let F := family hV hm hh hlo hup
    let data := OuterRootOriginalData.data hV hh (lower_nonneg hm hlo) hup
    ‖(jetLp F data (Real.sqrt h)⁻¹ 0 ((clock:ℝ)*a)-jetLp F data (Real.sqrt h)⁻¹ 0 0)-
      ∑ j : ClockCollocation.MainIndex h K,ClockCollocation.W h hh K clock a j •
        jetLp F data (Real.sqrt h)⁻¹ 1 (ClockCollocation.u h K clock j)‖≤
      ClockQuadraturePower.orderConstant K*Real.sqrt (Fintype.card ι:ℝ)*h^(K+6) := by
  have H := ClockQuadratureRows.source_prescribedRow hV hm hh hlo hup hsmall K clock a ha
  dsimp only at H ⊢
  rw [OuterRootOutputQuadrature.integral_jet_one _ _ _
    (by exact ⟨le_rfl,by norm_num [OuterRootOriginalData.data]⟩)
    (by change (clock:ℝ)*a∈Icc (0:ℝ) (1/2)
        exact ⟨mul_nonneg clock.2.1 ha.1,
          (mul_le_mul_of_nonneg_left ha.2 clock.2.1).trans (by simpa using clock.2.2)⟩)] at H
  exact H.trans (ClockQuadraturePower.rowBudget_le hh K (Fintype.card ι) clock)

include hsmall in
/-- The row's physical center factor is exactly rF times the prescribed node
clock. This is the common-seed main-center residual contribution. -/
theorem source_main_center_defect (i : ClockCollocation.MainIndex h K) :
    let F := family hV hm hh hlo hup
    let data := OuterRootOriginalData.data hV hh (lower_nonneg hm hlo) hup
    ‖(ClockCollocation.rF h*ClockCollocation.u h K clock i) •
      ((jetLp F data (Real.sqrt h)⁻¹ 0 (ClockCollocation.u h K clock i)-
        jetLp F data (Real.sqrt h)⁻¹ 0 0)-
        ∑ j : ClockCollocation.MainIndex h K,ClockCollocation.W h hh K clock (ClockCollocation.v h K i) j •
          jetLp F data (Real.sqrt h)⁻¹ 1 (ClockCollocation.u h K clock j))‖≤
      (ClockCollocation.rF h/2)*ClockQuadraturePower.orderConstant K*
        Real.sqrt (Fintype.card ι:ℝ)*h^(K+6) := by
  have hv : ClockCollocation.v h K i∈Icc (0:ℝ) 1 := by
    have H := ClockSchedule.unitNode_mem_Ioo _ _ (ClockSchedule.sourceCells_pos hh) i
    exact ⟨H.1.le,H.2.le⟩
  have H := source_partial_defect hV hm hh hlo hup hsmall K clock (ClockCollocation.v h K i) hv
  have hu := ClockCollocation.u_mem hh K clock i
  have hr : 0≤ClockCollocation.rF h := Real.sqrt_nonneg _
  dsimp only at H ⊢
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hr hu.1)]
  have hb : 0≤ClockQuadraturePower.orderConstant K*Real.sqrt (Fintype.card ι:ℝ)*h^(K+6) :=
    mul_nonneg (mul_nonneg (ClockQuadraturePower.orderConstant_nonneg K) (Real.sqrt_nonneg _))
      (pow_nonneg hh.le _)
  calc
    _ ≤ (ClockCollocation.rF h*ClockCollocation.u h K clock i)*
        (ClockQuadraturePower.orderConstant K*Real.sqrt (Fintype.card ι:ℝ)*h^(K+6)) :=
      mul_le_mul_of_nonneg_left H (mul_nonneg hr hu.1)
    _ ≤ (ClockCollocation.rF h*(1/2))*
        (ClockQuadraturePower.orderConstant K*Real.sqrt (Fintype.card ι:ℝ)*h^(K+6)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hu.2.trans clock.2.2) hr) hb
    _ = _ := by ring

end AcceleratedLogConcave.Root.OuterRootMainQuadrature
