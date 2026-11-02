import AcceleratedLogConcave.Root.CoolingPreReserveCoupling
import AcceleratedLogConcave.Root.CoolingSourceConditionalAccuracy
import AcceleratedLogConcave.Channels.CoolingDecoderLaw
import AcceleratedLogConcave.Gibbs.SmoothedPrimitiveScaleMoment

/-! Actual public cooling KL. The pre-reserve coupling is the readout of the
constructed complete source kernel; the implementation is the literal native
public program with its original final reserve. All child accuracy and scale
moments come from the original source data. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open MeasureTheory ProbabilityTheory InformationTheory
open scoped BigOperators NNReal ENNReal
namespace AcceleratedLogConcave.Root.CoolingSourceLocalKL
open Oracle Numerics Numerics.AffineGraph TapeLowering
open CanonicalTapeLaw CanonicalTapeMeasurability SourceExecutableTables
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p

private theorem cost_of_map {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → Point d × Point d) (g : Ω → Point d) (hf : Measurable f)
    (he : ∀ z,(f z).1-(f z).2 = -g z) (hg : MemLp g 2 μ) :
    (∫⁻ uv,ENNReal.ofReal (2*‖uv.1-uv.2‖^2) ∂μ.map f) =
      ENNReal.ofReal (2*∫ z,‖g z‖^2 ∂μ) := by
  rw [lintegral_map (by fun_prop) hf]
  simp_rw [he,norm_neg]
  rw [← ofReal_integral_eq_lintegral_ofReal ((hg.integrable_norm_pow (by norm_num)).const_mul 2)
    (Filter.Eventually.of_forall fun _ => by positivity),integral_const_mul]

variable (P : SourceSchedule) (hK : 10≤P.K) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (hC : 8≤P.Csch) (hy : MeanSourceScalarAbsorption.threshold P≤P.y)
local notation "hyPrivate" => MeanSourceScalarAbsorption.private_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy
local notation "baseHy" => PrivateSourceScalarAbsorption.base_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hyPrivate
local notation "hR" => CubicSchedulePayments.radius_guard P hK hc hsmall hC baseHy
local notation "S" => CoolingPrescribedPayments.geometry P hR
local notation "e" => CoolingPrescribedPayments.nodes P
local notation "Q" => CoolingPrescribedPayments.setup P hR hc hsmall
variable (v : ℝ≥0) (hv : 0<v) (hvUpper : (v:ℝ)≤2*P.delta^2)
  {d : ℕ} {V : Point d → ℝ} (hV : ContDiff ℝ 2 V) {m : ℝ} (hm : 0<m)
  (hlo : ∀ z w,m*‖w‖^2≤fderiv ℝ (fderiv ℝ V) z w w)
  (hup : ∀ z w,fderiv ℝ (fderiv ℝ V) z w w≤‖w‖^2)
local notation "r" => CoolingExecutable.radius P.delta v
local notation "F" => scaledPotential V (Real.sqrt P.delta)
local notation "Host" => (CoolingExecutable.data Q P.delta v P.K).program
local notation "Seed" => (Point d × Tape d Host) × Point d

include hV in
private theorem scaled_contDiff : ContDiff ℝ 2 (scaledPotential V (Real.sqrt P.delta)) := by
  unfold scaledPotential
  fun_prop
include hV in
private theorem oracle_measurable : Measurable (gradient V) :=
  ((InnerProductSpace.toDual ℝ (Point d)).symm.continuous.comp
    (hV.continuous_fderiv (by norm_num))).measurable
local notation "hF" => scaled_contDiff P hV
local notation "hG" => oracle_measurable hV

include hV hm hlo in
/-- The lower convexity input is derived from the original positive Hessian. -/
theorem scaled_hessian_nonneg :
    ∀ z w,0≤fderiv ℝ (fderiv ℝ (scaledPotential V (Real.sqrt P.delta))) z w w := by
  unfold scaledPotential
  have hzero : ∀ z w,0≤fderiv ℝ (fderiv ℝ V) z w w := fun z w =>
    (mul_nonneg hm.le (sq_nonneg _)).trans (hlo z w)
  simpa only [zero_add] using
    Gibbs.primitive_affine_hessian_nonneg hV hzero (0 : Point d) (Real.sqrt P.delta)

include hV hup in
/-- The analytic normalized curvature is exactly delta while execution
continues to query the original gradient. -/
theorem scaled_hessian_upper :
    ∀ z w,fderiv ℝ (fderiv ℝ (scaledPotential V (Real.sqrt P.delta))) z w w≤P.delta*‖w‖^2 := by
  unfold scaledPotential
  have hu : ∀ z w,fderiv ℝ (fderiv ℝ V) z w w≤(1:ℝ)*‖w‖^2 := by simpa only [one_mul] using hup
  simpa only [zero_add,Real.sq_sqrt P.delta_pos.le,mul_one] using
    Gibbs.primitive_affine_hessian_upper hV hu (0 : Point d) (Real.sqrt P.delta)
local notation "hzero" => scaled_hessian_nonneg P hV hm hlo
local notation "hupper" => scaled_hessian_upper P hV hup
local notation "hp" => CoolingSourceConditionalAccuracy.physical P hK hc hsmall hC hy v hvUpper P.delta_pos.le le_rfl

/-- The concrete pre-reserve readout of the same original public source. -/
def coupling : Kernel (Point d) (Point d × Point d) :=
  CoolingPreReserveCoupling.kernel P hK hc hsmall hC hyPrivate P.delta v P.delta_pos hv
    (scaled_contDiff P hV) P.delta_pos.le (scaled_hessian_nonneg P hV hm hlo)
    (scaled_hessian_upper P hV hup) (gradient V) (oracle_measurable hV)
    (CoolingSourceConditionalAccuracy.physical P hK hc hsmall hC hy v hvUpper P.delta_pos.le le_rfl)

instance coupling_markov : IsMarkovKernel (coupling P hK hc hsmall hC hy v hv hvUpper hV hm hlo hup) := by
  unfold coupling
  infer_instance

/-- Exact primitive reference marginal in the original physical coordinates. -/
theorem coupling_fst (x : Point d) :
    ((coupling P hK hc hsmall hC hy v hv hvUpper hV hm hlo hup) x).map Prod.fst =
      Channels.forward (Gibbs.primitiveLaw V x (Real.sqrt (v:ℝ))) (3/4) := by
  calc
    _ = Channels.forward (Conditional.baseLaw F ((Real.sqrt P.delta)⁻¹ • x) r) (3/4) :=
      CoolingPreReserveCoupling.kernel_fst P hK hc hsmall hC hyPrivate P.delta v P.delta_pos hv
        hF P.delta_pos.le hzero hupper (gradient V) hG hp x
    _ = _ := by
      congr 1
      exact Channels.primitiveLaw_oracle_coordinates V P.delta P.delta_pos v x

theorem coupling_snd (x : Point d) :
    ((coupling P hK hc hsmall hC hy v hv hvUpper hV hm hlo hup) x).map Prod.snd =
      CoolingExecutable.preKernel Q P.delta v P.K (gradient V) x :=
  CoolingPreReserveCoupling.kernel_snd P hK hc hsmall hC hyPrivate P.delta v P.delta_pos hv
    hF P.delta_pos.le hzero hupper (gradient V) hG hp x

/-- The existing decoder comparison now applies to the literal public
execution, using the constructed concrete pre-reserve coupling. -/
theorem pointwise_KL_cost (x : Point d) :
    klDiv (Channels.equalWidthBridge V hV.continuous.measurable v x)
      (CoolingExecutable.originalGradientKernel Q P.delta v P.K V x) ≤
      ∫⁻ uv,ENNReal.ofReal (2*‖uv.1-uv.2‖^2)
        ∂(coupling P hK hc hsmall hC hy v hv hvUpper hV hm hlo hup) x := by
  have hI := Gibbs.integrable_exp_neg_of_hessian_lower hV hm hlo
  let _ := CoolingExecutable.preKernel_markov Q P.delta v P.K hG
  have he := Channels.cooling_localKL_pointwise_of_preCoupling hV.continuous.measurable hI v hv
    (CoolingExecutable.preKernel Q P.delta v P.K (gradient V))
    (coupling P hK hc hsmall hC hy v hv hvUpper hV hm hlo hup)
    (coupling_fst P hK hc hsmall hC hy v hv hvUpper hV hm hlo hup)
    (coupling_snd P hK hc hsmall hC hy v hv hvUpper hV hm hlo hup) x
  rw [← CoolingReserveLaw.kernel_eq_reservedDecoder Q P.delta v P.K hG] at he
  exact he

/-- The pre-reserve cost is the proved literal public error, with the
unchanged full source law and the original inverse input scaling. -/
theorem pointwise_cost_le (x : Point d) :
    (∫⁻ uv,ENNReal.ofReal (2*‖uv.1-uv.2‖^2)
      ∂(coupling P hK hc hsmall hC hy v hv hvUpper hV hm hlo hup) x)≤
      ENNReal.ofReal (18*(P.delta^P.K)^2*(Gibbs.primitiveScale F ((Real.sqrt P.delta)⁻¹ • x))^2) := by
  let μ := (CoolingSourceRetainedCoupling.kernel P hK hc hsmall hC hyPrivate P.delta v P.delta_pos hv
    hF P.delta_pos.le hzero hupper (gradient V) hG hp) ((Real.sqrt P.delta)⁻¹ • x)
  let f : Seed → Point d × Point d := fun z =>
    (CoolingPreReserveCoupling.reference P hK hc hsmall hC hyPrivate P.delta v z,
      CoolingExecutable.preReserve Q P.delta v P.K (gradient V) x z.1.2)
  let err := CoolingSourceRetainedAccuracy.error (G := gradient V) P hK hc hsmall hC hyPrivate
    P.delta v ((Real.sqrt P.delta)⁻¹ • x)
  obtain ⟨hmem,hbound⟩ := CoolingSourceConditionalAccuracy.square_error_bound P hK hc hsmall hC hy v hv hvUpper
    hV P.delta_pos.le le_rfl hzero hupper ((Real.sqrt P.delta)⁻¹ • x)
  have hf : Measurable f :=
    (CoolingPreReserveCoupling.readout_measurable P hK hc hsmall hC hyPrivate P.delta v (gradient V) hG).comp
      measurable_prodMk_left
  have he (z : Seed) : (f z).1-(f z).2 = -err z :=
    CoolingPreReserveCoupling.difference_eq_error P hK hc hsmall hC hyPrivate P.delta v (gradient V) x z
  have hcst := cost_of_map μ f err hf he hmem
  have hmap : (coupling P hK hc hsmall hC hy v hv hvUpper hV hm hlo hup) x = μ.map f :=
    CoolingPreReserveCoupling.kernel_apply P hK hc hsmall hC hyPrivate P.delta v P.delta_pos hv
      hF P.delta_pos.le hzero hupper (gradient V) hG hp x
  calc
    _ = ∫⁻ uv,ENNReal.ofReal (2*‖uv.1-uv.2‖^2) ∂μ.map f :=
      congrArg (fun ν : Measure (Point d × Point d) => ∫⁻ uv,ENNReal.ofReal (2*‖uv.1-uv.2‖^2) ∂ν) hmap
    _ = ENNReal.ofReal (2*∫ z,‖err z‖^2 ∂μ) := hcst
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ 2*(3*P.delta^(P.K:ℝ)*Gibbs.primitiveScale F ((Real.sqrt P.delta)⁻¹ • x))^2 :=
          mul_le_mul_of_nonneg_left hbound (by norm_num)
        _ = _ := by rw [Real.rpow_natCast]; ring

include hv hvUpper hm hlo hup

/-- Pointwise KL compares the exact posterior midpoint kernel to the literal
public original-gradient program, with every error payment supplied. -/
theorem pointwise_KL_le (x : Point d) :
    klDiv (Channels.equalWidthBridge V hV.continuous.measurable v x)
      (CoolingExecutable.originalGradientKernel Q P.delta v P.K V x) ≤
      ENNReal.ofReal (18*(P.delta^P.K)^2*(Gibbs.primitiveScale F ((Real.sqrt P.delta)⁻¹ • x))^2) :=
  (pointwise_KL_cost P hK hc hsmall hC hy v hv hvUpper hV hm hlo hup x).trans
    (pointwise_cost_le P hK hc hsmall hC hy v hv hvUpper hV hm hlo hup x)

/-- Original-data averaged local cooling KL, with no supplied coupling,
implementation law, error, derivative, or stationary moment certificate. -/
theorem averaged_KL_le :
    (∫⁻ x,klDiv (Channels.equalWidthBridge V hV.continuous.measurable v x)
      (CoolingExecutable.originalGradientKernel Q P.delta v P.K V x)
      ∂Channels.forward (volume.tilted (fun z => -V z)) v)≤
      ENNReal.ofReal (180*(d:ℝ)*P.delta^(2*P.K)) := by
  have hd := PrivateSourceScalarAbsorption.delta_le_hundredth P hK hc (by linarith) (by linarith) hyPrivate
  have hv1 : (v:ℝ)≤1 := by nlinarith [mul_le_mul_of_nonneg_right hd P.delta_pos.le]
  obtain ⟨hint,hbound⟩ := Gibbs.SmoothedPrimitiveScaleMoment.primitiveScale_square hV hm hlo hup
    P.delta P.delta_pos (hd.trans (by norm_num)) v hv1
  have hc0 : 0≤18*(P.delta^P.K)^2 := by positivity
  calc
    _ ≤ ∫⁻ x,ENNReal.ofReal (18*(P.delta^P.K)^2*(Gibbs.primitiveScale F ((Real.sqrt P.delta)⁻¹ • x))^2)
        ∂Channels.forward (volume.tilted (fun z => -V z)) v :=
      lintegral_mono (pointwise_KL_le P hK hc hsmall hC hy v hv hvUpper hV hm hlo hup)
    _ = ENNReal.ofReal ((18*(P.delta^P.K)^2)*
        ∫ x,(Gibbs.primitiveScale F ((Real.sqrt P.delta)⁻¹ • x))^2
          ∂Channels.forward (volume.tilted (fun z => -V z)) v) := by
      rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)
        (Filter.Eventually.of_forall fun _ => by positivity),integral_const_mul]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ (18*(P.delta^P.K)^2)*(10*(d:ℝ)) := mul_le_mul_of_nonneg_left hbound hc0
        _ = _ := by rw [← pow_mul,Nat.mul_comm P.K 2]; ring

end AcceleratedLogConcave.Root.CoolingSourceLocalKL
