import AcceleratedLogConcave.Conditional.Transport.JointFlowExtension
import AcceleratedLogConcave.Conditional.Stein.Transport

/-

-/
noncomputable section
open Set Metric Function MeasureTheory Filter
open scoped Topology ContDiff NNReal
namespace AcceleratedLogConcave.Conditional.Transport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
private def variationEndpointDerivative (S : (ℝ × ℝ) × E → E)
    (p : (ℝ × ℝ) × E) : E →L[ℝ] E :=
  (fderiv ℝ S p).comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ) E)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma variationEndpointDerivative_smooth {S : (ℝ × ℝ) × E → E}
    (hS : ContDiff ℝ ∞ S) : ContDiff ℝ ∞ (variationEndpointDerivative S) :=
  (hS.fderiv_right (by simp)).clm_comp contDiff_const

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma variationEndpointDerivative_eq {S : (ℝ × ℝ) × E → E}
    (hS : ContDiff ℝ ∞ S) (p : ℝ × ℝ) (y : E) :
    variationEndpointDerivative S (p,y) = fderiv ℝ (fun w => S (p,w)) y := by
  symm
  exact ((hS.differentiable (by simp) (p,y)).hasFDerivAt.comp y
    ((hasFDerivAt_const (𝕜 := ℝ) p y).prodMk (hasFDerivAt_id y))).fderiv

/-- A smooth representative of the actual transported Jacobian on a spatial
neighborhood and the entire closed time slab, needed to interchange derivatives. -/
theorem exists_smooth_transportedJacobian_extension {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {ell : ℝ} (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖^2)
    (x : E) {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (hsmall : r^2*ell ≤ 1/2) :
    ∀ z : E, ∃ B : ℝ × E → E →L[ℝ] E, ContDiff ℝ ∞ B ∧
      ∀ ρ ∈ Icc 0 b, ∀ y ∈ ball z 1,
        B (ρ,y) = transportedJacobian hF hell hlo hup x hr hb hb1 ρ y := by
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
  let B : ℝ × E → E →L[ℝ] E := fun p => variationEndpointDerivative Sf ((p.1,b),Y p)
  have hB : ContDiff ℝ ∞ B :=
    (variationEndpointDerivative_smooth hSf).comp ((contDiff_fst.prodMk contDiff_const).prodMk hY)
  have hBeq (ρ : ℝ) (hρ : ρ ∈ Icc 0 b) (y : E) (hy : y ∈ ball z 1) :
      B (ρ,y) = transportedJacobian hF hell hlo hup x hr hb hb1 ρ y := by
    have hevent : (fun w => Sf ((ρ,b),w)) =ᶠ[𝓝 (Y (ρ,y))]
        (forwardProbabilityTransport hF hell hlo hup x hr hb hb1 ρ) := by
      filter_upwards [isOpen_ball.mem_nhds (hYmem ρ hρ y hy)] with w hw
      have hh := hfeq ⟨ρ,hρ⟩ ⟨b,hb,le_rfl⟩ w hw
      simpa only [forwardProbabilityTransport,projIcc_of_mem hb hρ,
        convexProbabilityFlowHomeomorph_apply] using hh
    change variationEndpointDerivative Sf ((ρ,b),Y (ρ,y)) = _
    rw [variationEndpointDerivative_eq hSf,hevent.fderiv_eq]
    rw [hYeq ρ hρ y hy]
    rfl
  exact ⟨B,hB,hBeq⟩

/-- Actual spatial smoothness of the transported Jacobian on the closed slab. -/
theorem contDiff_infty_transportedJacobian_spatial {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {ell : ℝ} (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell*‖a‖^2)
    (x : E) {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (hsmall : r^2*ell ≤ 1/2) {ρ : ℝ} (hρ : ρ ∈ Icc 0 b) :
    ContDiff ℝ ∞ (transportedJacobian hF hell hlo hup x hr hb hb1 ρ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  obtain ⟨B,hB,hBeq⟩ := exists_smooth_transportedJacobian_extension
    hF hell hlo hup x hr hb hb1 hsmall z
  have hs : ContDiff ℝ ∞ (fun y : E => B (ρ,y)) :=
    hB.comp (contDiff_const.prodMk contDiff_id)
  apply hs.contDiffAt.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds z (by norm_num : (0:ℝ)<1)] with y hy
  exact (hBeq ρ hρ y hy).symm
end AcceleratedLogConcave.Conditional.Transport
