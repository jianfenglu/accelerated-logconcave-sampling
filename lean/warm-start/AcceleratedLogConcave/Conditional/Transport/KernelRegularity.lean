import AcceleratedLogConcave.Conditional.Transport.JointFlowExtension
import AcceleratedLogConcave.Conditional.Transport.CompactIntegral
import AcceleratedLogConcave.Conditional.SteinKernel

/-! Spatial smoothness of the actual transported Stein integral. -/
set_option maxHeartbeats 600000
noncomputable section
open Set Metric Function MeasureTheory Filter
open scoped Topology ContDiff NNReal
namespace AcceleratedLogConcave.Conditional.Transport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private def endpointSpatialDerivative (S : (ℝ × ℝ) × E → E)
    (p : (ℝ × ℝ) × E) : E →L[ℝ] E :=
  (fderiv ℝ S p).comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ) E)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma endpointSpatialDerivative_smooth {S : (ℝ × ℝ) × E → E}
    (hS : ContDiff ℝ ∞ S) : ContDiff ℝ ∞ (endpointSpatialDerivative S) :=
  (hS.fderiv_right (by simp)).clm_comp contDiff_const

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma endpointSpatialDerivative_eq {S : (ℝ × ℝ) × E → E}
    (hS : ContDiff ℝ ∞ S) (p : ℝ × ℝ) (y : E) :
    endpointSpatialDerivative S (p,y) = fderiv ℝ (fun w => S (p,w)) y := by
  symm
  exact ((hS.differentiable (by simp) (p,y)).hasFDerivAt.comp y
    ((hasFDerivAt_const (𝕜 := ℝ) p y).prodMk (hasFDerivAt_id y))).fderiv

/-- Near each spatial input, a single smooth representative realizes the
actual Stein integrand throughout the closed probability-time interval. -/
theorem exists_smooth_transportedSteinIntegrand_extension {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {ell : ℝ} (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (hsmall : r^2*ell ≤ 1/2) :
    ∀ z : E, ∃ C : ℝ × E → E →L[ℝ] E, ContDiff ℝ ∞ C ∧
      ∀ ρ ∈ Icc 0 b, ∀ y ∈ ball z 1,
        C (ρ,y) = transportedSteinIntegrand hF hell hlo hup x hr hb hb1 ρ y := by
  intro z
  obtain ⟨Sb,hSb,hbeq⟩ := exists_smooth_convexProbabilityFlow_extension hF hell hlo hup x hr hb hb1 hsmall z
  let Y : ℝ × E → E := fun p => Sb (((b,p.1),p.2))
  have hY : ContDiff ℝ ∞ Y :=
    hSb.comp ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd)
  have hYeq (ρ : ℝ) (hρ : ρ ∈ Icc 0 b) (y : E) (hy : y ∈ ball z 1) :
      Y (ρ,y) = backwardProbabilityTransport hF hell hlo hup x hr hb hb1 ρ y := by
    rw [backwardProbabilityTransport_eq_flow,projIcc_of_mem hb hρ]
    exact hbeq ⟨b,hb,le_rfl⟩ ⟨ρ,hρ⟩ y hy
  have hYz : Continuous (fun ρ : ℝ => Y (ρ,z)) :=
    hY.continuous.comp (continuous_id.prodMk continuous_const)
  obtain ⟨A,hA⟩ := isCompact_Icc.exists_bound_of_continuousOn hYz.continuousOn
  let R := |A|+Real.exp 1+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hYmem (ρ : ℝ) (hρ : ρ ∈ Icc 0 b) (y : E) (hy : y ∈ ball z 1) :
      Y (ρ,y) ∈ ball (0:E) R := by
    have hy0 : z ∈ ball z 1 := mem_ball_self (by norm_num)
    have hd := (lipschitzWith_convexProbabilityFlow_exp_one hF hell hlo hup x hr hb hb1
      hsmall ⟨b,hb,le_rfl⟩ ⟨ρ,hρ⟩).dist_le_mul y z
    have hBy : Y (ρ,y) = convexProbabilityFlow hF hell hlo hup x hr hb (by norm_num) hb1
        ⟨b,hb,le_rfl⟩ y ρ := hbeq ⟨b,hb,le_rfl⟩ ⟨ρ,hρ⟩ y hy
    have hBz : Y (ρ,z) = convexProbabilityFlow hF hell hlo hup x hr hb (by norm_num) hb1
        ⟨b,hb,le_rfl⟩ z ρ := hbeq ⟨b,hb,le_rfl⟩ ⟨ρ,hρ⟩ z hy0
    rw [← hBy,← hBz] at hd
    simp only [dist_eq_norm] at hd
    have hy' : ‖y-z‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using hy
    have hdiff : ‖Y (ρ,y)-Y (ρ,z)‖ ≤ Real.exp 1 :=
      hd.trans ((mul_le_mul_of_nonneg_left hy'.le (Real.exp_pos 1).le).trans_eq (by ring))
    have hn := norm_add_le (Y (ρ,y)-Y (ρ,z)) (Y (ρ,z))
    rw [sub_add_cancel] at hn
    have hz := hA ρ hρ
    simp only [mem_ball_zero_iff]
    dsimp [R]
    linarith [le_abs_self A]
  obtain ⟨Sf,hSf,hfeq⟩ := exists_smooth_convexProbabilityFlow_extension_ball hF hell hlo hup x hr hb hb1 hsmall (0:E) hR
  let B : ℝ × E → E →L[ℝ] E := fun p => endpointSpatialDerivative Sf ((p.1,b),Y p)
  have hB : ContDiff ℝ ∞ B :=
    (endpointSpatialDerivative_smooth hSf).comp ((contDiff_fst.prodMk contDiff_const).prodMk hY)
  have hBeq (ρ : ℝ) (hρ : ρ ∈ Icc 0 b) (y : E) (hy : y ∈ ball z 1) :
      B (ρ,y) = transportedJacobian hF hell hlo hup x hr hb hb1 ρ y := by
    have hevent : (fun w => Sf ((ρ,b),w)) =ᶠ[𝓝 (Y (ρ,y))]
        (forwardProbabilityTransport hF hell hlo hup x hr hb hb1 ρ) := by
      filter_upwards [isOpen_ball.mem_nhds (hYmem ρ hρ y hy)] with w hw
      have hh := hfeq ⟨ρ,hρ⟩ ⟨b,hb,le_rfl⟩ w hw
      simpa only [forwardProbabilityTransport,projIcc_of_mem hb hρ,
        convexProbabilityFlowHomeomorph_apply] using hh
    change endpointSpatialDerivative Sf ((ρ,b),Y (ρ,y)) = _
    rw [endpointSpatialDerivative_eq hSf,hevent.fderiv_eq]
    rw [hYeq ρ hρ y hy]
    rfl
  obtain ⟨ψ,hψ,hψrange,hψeq⟩ := exists_smooth_timeClamp hb (by norm_num) hb1
  have hC : ContDiff ℝ ∞ (fun p : ℝ × E => (ψ p.1,Y p)) :=
    (hψ.comp contDiff_fst).prodMk hY
  have hUs := (contDiffOn_firstScaledJet hF hlo hup x r).comp_contDiff hC
    (fun p => hψrange p.1)
  let U : ℝ × E → E →L[ℝ] E := fun p => firstScaledJet F x r (ψ p.1) (Y p)
  have hU : ContDiff ℝ ∞ U := hUs
  let C : ℝ × E → E →L[ℝ] E := fun p => (B p).comp (U p)
  have hCs : ContDiff ℝ ∞ C := hB.clm_comp hU
  have hCeq (ρ : ℝ) (hρ : ρ ∈ Icc 0 b) (y : E) (hy : y ∈ ball z 1) :
      C (ρ,y) = transportedSteinIntegrand hF hell hlo hup x hr hb hb1 ρ y := by
    change (B (ρ,y)).comp (firstScaledJet F x r (ψ ρ) (Y (ρ,y))) = _
    rw [hBeq ρ hρ y hy,hψeq hρ,hYeq ρ hρ y hy]
    rfl
  exact ⟨C,hCs,hCeq⟩

/-- All spatial derivatives of the actual Stein integral exist and are
continuous. Uniform smooth representatives give compact-time domination,
including the zero endpoint. -/
theorem contDiff_infty_transportedSteinKernelTranspose {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {ell : ℝ} (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (hsmall : r^2*ell ≤ 1/2) :
    ContDiff ℝ ∞ (transportedSteinKernelTranspose hF hell hlo hup x hr hb hb1) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  obtain ⟨C,hCs,hCeq⟩ := exists_smooth_transportedSteinIntegrand_extension
    hF hell hlo hup x hr hb hb1 hsmall z
  have hI : ContDiff ℝ ∞ (fun y : E => ∫ ρ in 0..b, C (ρ,y)) :=
    contDiff_infty_intervalIntegral hCs hb
  apply hI.contDiffAt.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds z (by norm_num : (0:ℝ) < 1)] with y hy
  unfold transportedSteinKernelTranspose
  apply intervalIntegral.integral_congr_uIoo
  intro ρ hρ
  have hρ' : ρ ∈ Ioo 0 b := by simpa only [uIoo_of_le hb] using hρ
  exact (hCeq ρ ⟨hρ'.1.le,hρ'.2.le⟩ y hy).symm

end AcceleratedLogConcave.Conditional.Transport
