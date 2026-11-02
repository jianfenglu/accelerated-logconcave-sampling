import AcceleratedLogConcave.Conditional.TiltCalculus
import AcceleratedLogConcave.Conditional.Flow.MeanIBP
import AcceleratedLogConcave.Conditional.FirstJet
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The actual first scaled jet is the excess observable-weighted flux. -/
noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace ContDiff

namespace AcceleratedLogConcave.Conditional
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The row current associated to an output direction. -/
def firstScaledJetRow (F : E → ℝ) (x u : E) (r ρ : ℝ) (y : E) : E :=
  (firstScaledJet F x r ρ y).adjoint u

theorem firstScaledJet_pairing_eq_covariance
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ}
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x u v : E) (r : ℝ) {ρ : ℝ} (hρlo : -1 < ρ) (hρhi : ρ < 1) (y : E) :
    inner ℝ u (firstScaledJet F x r ρ y v) = (conditionalVariance ρ)⁻¹ *
      cov[fun z => inner ℝ u (primitiveObservable F x r z), fun z => inner ℝ z v;
        conditionalLaw F x r ρ y] := by
  let B := primitivePotential F x r
  let g := primitiveObservable F x r
  let t := conditionalVariance ρ
  let A := ‖gradient F 0‖ + |ell| * ‖x‖
  let C := |ell| * |r|
  have ht : 0 < t := conditionalVariance_pos hρlo hρhi
  have hB := contDiff_primitivePotential hF x r
  have hBlo : ∀ z a, (0 : ℝ) * ‖a‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ B) z a a := by
    simpa [B] using primitivePotential_hessian_nonneg hF hlo x r
  have hg : Continuous g := continuous_primitiveObservable hF x r
  have hbound : ∀ z, ‖g z‖ ≤ A + C * ‖z‖ := norm_primitiveObservable_le_affine hF hlo hup x r
  have hgi (c : E) : Integrable g (Gibbs.heatPosterior B t c) := by
    let := Gibbs.heatPosterior_isProbabilityMeasure hB (m := 0) le_rfl ht hBlo c
    exact (Gibbs.memLp_two_heatPosterior_of_affine_bound hB (m := 0) le_rfl ht hBlo
      c hg A C hbound).integrable (by norm_num)
  let N (c : E) := ∫ z, g z ∂Gibbs.heatPosterior B t c
  let gw (z : E) := inner ℝ u (g z)
  have hgw : Continuous gw := (innerSL ℝ u).continuous.comp hg
  have hbw (z : E) : ‖gw z‖ ≤ A * ‖u‖ + (C * ‖u‖) * ‖z‖ := by
    exact (norm_inner_le_norm u (g z)).trans
      ((mul_le_mul_of_nonneg_left (hbound z) (norm_nonneg u)).trans_eq (by ring))
  have heq (c : E) : (∫ z, gw z ∂Gibbs.heatPosterior B t c) = inner ℝ u (N c) :=
    (innerSL ℝ u).integral_comp_comm (hgi c)
  have hN := Gibbs.contDiff_one_integral_heatPosterior hB (m := 0) le_rfl ht hBlo hg A C hbound
  have hlin := (innerSL ℝ u).hasFDerivAt.comp (ρ • y)
    (hN.differentiable (by norm_num) (ρ • y)).hasFDerivAt
  have hscalar : fderiv ℝ (fun c => ∫ z, gw z ∂Gibbs.heatPosterior B t c) (ρ • y) v =
      inner ℝ u (fderiv ℝ N (ρ • y) v) := by
    rw [show (fun c => ∫ z, gw z ∂Gibbs.heatPosterior B t c) =
      (innerSL ℝ u) ∘ N from funext heq, hlin.fderiv]
    rfl
  rw [← fderiv_centerMean_eq_firstScaledJet hF hlo hup x r hρlo hρhi y]
  change inner ℝ u (fderiv ℝ N (ρ • y) v) = _
  rw [← hscalar, Gibbs.fderiv_integral_heatPosterior_eq_covariance
    hB (m := 0) le_rfl ht hBlo hgw (A * ‖u‖) (C * ‖u‖) hbw]
  rfl

/-- The row vector has the positive covariance-current pairing. -/
theorem firstScaledJetRow_inner_eq_covariance
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ}
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x u v : E) (r : ℝ) {ρ : ℝ} (hρlo : -1 < ρ) (hρhi : ρ < 1) (y : E) :
    inner ℝ (firstScaledJetRow F x u r ρ y) v = (conditionalVariance ρ)⁻¹ *
      cov[fun z => inner ℝ u (primitiveObservable F x r z), fun z => inner ℝ z v;
        conditionalLaw F x r ρ y] := by
  rw [firstScaledJetRow, ContinuousLinearMap.adjoint_inner_left]
  exact firstScaledJet_pairing_eq_covariance hF hlo hup x u v r hρlo hρhi y

/-- The actual conditional flux splits into mean transport and its first-jet
current for every scalar space-time linear test. -/
theorem integral_weighted_conditional_spaceTime_velocity
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ}
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x u : E) (r : ℝ) {ρ : ℝ} (hρlo : -1 < ρ) (hρhi : ρ < 1)
    (y : E) (A : (ℝ × E) →L[ℝ] ℝ) :
    (∫ z, inner ℝ u (primitiveObservable F x r z) *
      A (1, (conditionalVariance ρ)⁻¹ • (z - ρ • y)) ∂conditionalLaw F x r ρ y) =
      inner ℝ u (conditionalMean F x r ρ y) * A (1, probabilityVelocity F x r ρ y) +
      A (0, firstScaledJetRow F x u r ρ y) := by
  let μ := conditionalLaw F x r ρ y
  let := conditionalLaw_isProbabilityMeasure hF hlo x r hρlo hρhi y
  let w (z : E) := inner ℝ u (primitiveObservable F x r z)
  let v : E := (toDual ℝ E).symm (A.comp (ContinuousLinearMap.inr ℝ ℝ E))
  let Z (z : E) := inner ℝ z v
  let V (z : E) := A (1, (conditionalVariance ρ)⁻¹ • (z - ρ • y))
  have hv (z : E) : A (0, z) = inner ℝ z v := by
    simpa only [v, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      real_inner_comm] using
      (toDual_symm_apply (x := z) (y := A.comp (ContinuousLinearMap.inr ℝ ℝ E))).symm
  have hV (z : E) : V z = A (1, 0) + (conditionalVariance ρ)⁻¹ * (Z z - ρ * Z y) := by
    calc
      _ = A (1, 0) + A (0, (conditionalVariance ρ)⁻¹ • (z - ρ • y)) := by
        rw [← map_add]
        simp only [V, Prod.mk_add_mk, add_zero, zero_add]
      _ = _ := by
        rw [hv, inner_smul_left, inner_sub_left, inner_smul_left]
        simp only [conj_trivial]
        rfl
  have hB := contDiff_primitivePotential hF x r
  have ht := conditionalVariance_pos hρlo hρhi
  have hBlo : ∀ z a, (0 : ℝ) * ‖a‖ ^ 2 ≤
      fderiv ℝ (fderiv ℝ (primitivePotential F x r)) z a a := by
    simpa using primitivePotential_hessian_nonneg hF hlo x r
  have hfg : MemLp (primitiveObservable F x r) 2 μ :=
    Gibbs.memLp_two_heatPosterior_of_affine_bound hB (m := 0) le_rfl ht hBlo (ρ • y)
      (continuous_primitiveObservable hF x r) (‖gradient F 0‖ + |ell| * ‖x‖)
      (|ell| * |r|) (norm_primitiveObservable_le_affine hF hlo hup x r)
  have hw : MemLp w 2 μ := hfg.const_inner u
  have hZ : MemLp Z 2 μ := Gibbs.memLp_two_position_heatPosterior hB (m := 0)
    le_rfl ht hBlo (ρ • y) v
  have hpart : Integrable (fun z => (conditionalVariance ρ)⁻¹ * (Z z - ρ * Z y)) μ :=
    ((hZ.integrable (by norm_num)).sub (integrable_const _)).const_mul _
  have hVmem : MemLp V 2 μ := by
    rw [show V = (fun z => A (1, 0) + (conditionalVariance ρ)⁻¹ * (Z z - ρ * Z y)) from funext hV]
    have hscaled : MemLp (fun z : E => (conditionalVariance ρ)⁻¹ * (Z z - ρ * Z y)) 2 μ :=
      (hZ.sub (memLp_const (ρ * Z y))).const_mul (conditionalVariance ρ)⁻¹
    have hsum := (memLp_const (A (1, (0 : E))) (μ := μ) (p := 2)).add hscaled
    simpa only [Pi.add_apply] using! hsum
  have hcov : cov[w, V; μ] = (conditionalVariance ρ)⁻¹ * cov[w, Z; μ] := by
    rw [show V = (fun z => A (1, 0) + (conditionalVariance ρ)⁻¹ * (Z z - ρ * Z y)) from funext hV,
      covariance_const_add_right hpart, covariance_const_mul_right,
      covariance_sub_const_right (hZ.integrable (by norm_num))]
  have hmeanw : (∫ z, w z ∂μ) = inner ℝ u (conditionalMean F x r ρ y) :=
    (innerSL ℝ u).integral_comp_comm (hfg.integrable (by norm_num))
  have hmeanV : (∫ z, V z ∂μ) = A (1, probabilityVelocity F x r ρ y) :=
    integral_conditional_spaceTime_velocity hF hlo hup x r hρlo hρhi y A
  have hcurrent : A (0, firstScaledJetRow F x u r ρ y) =
      (conditionalVariance ρ)⁻¹ * cov[w, Z; μ] := by
    rw [hv]
    exact firstScaledJetRow_inner_eq_covariance hF hlo hup x u v r hρlo hρhi y
  have hcovsub := covariance_eq_sub hw hVmem
  change cov[w, V; μ] = (∫ z, w z * V z ∂μ) - (∫ z, w z ∂μ) * (∫ z, V z ∂μ) at hcovsub
  change (∫ z, w z * V z ∂μ) = _
  rw [hcov] at hcovsub
  rw [hmeanw, hmeanV] at hcovsub
  rw [hcurrent]
  linarith

/-- Smoothness of the actual covariance current under the source's nonzero scale. -/
theorem contDiff_firstScaledJetRow
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ}
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x u : E) {r : ℝ} (hr : r ≠ 0) {ρ : ℝ} (hρlo : -1 < ρ) (hρhi : ρ < 1) :
    ContDiff ℝ 1 (firstScaledJetRow F x u r ρ) := by
  have hT : ContDiff ℝ ∞ (fun y => firstScaledJet F x r ρ y) :=
    contDiffOn_univ.mp ((contDiffOn_firstScaledJet hF hlo hup x r).comp
      (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ _ => ⟨hρlo, hρhi⟩))
  have heq : firstScaledJetRow F x u r ρ = fun y => firstScaledJet F x r ρ y u := by
    funext y
    rw [firstScaledJetRow, (firstScaledJet_symmetric hF hlo hup x hr hρlo hρhi y).clm_adjoint_eq]
  rw [heq]
  exact (hT.clm_apply contDiff_const).of_le (by norm_num)

end AcceleratedLogConcave.Conditional
