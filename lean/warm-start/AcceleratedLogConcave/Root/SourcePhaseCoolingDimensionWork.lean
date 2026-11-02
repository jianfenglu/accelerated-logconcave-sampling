import AcceleratedLogConcave.Root.CoolingSourceWorkPayment
import AcceleratedLogConcave.Root.CoolingDyadicHorizon
import AcceleratedLogConcave.Kinetic.SourceDimensionPhaseCount
import AcceleratedLogConcave.Oracle.MeanSourceScalarAbsorption
import AcceleratedLogConcave.Numerics.SourceNumericalAccuracy

/-! Complete actual phase-plus-dyadic-cooling work at the dimension schedule.
The public threshold and the two execution counts are constructed explicitly.
This is deterministic accounting, with no sampler-correctness conclusion. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators NNReal
namespace AcceleratedLogConcave.Root.SourcePhaseCoolingDimensionWork
open Oracle Numerics Numerics.AffineGraph Kinetic

/-- Resolution for the same full mean/private/public source schedule. -/
def dimensionBound (K : ℕ) (c C e : ℝ) : ℕ :=
  SourceNumericalAccuracy.dimensionThreshold e
    (MeanSourceScalarAbsorption.threshold (SourceWorkResolution.schedule K c C 0))

theorem dimension_ge_one {K D : ℕ} {c C e : ℝ}
    (hD : dimensionBound K c C e≤D) : (1:ℝ)≤D := by
  have h := (Nat.le_ceil (max 1 (Real.exp
    (MeanSourceScalarAbsorption.threshold (SourceWorkResolution.schedule K c C 0)/e)))).trans
      (show (dimensionBound K c C e:ℝ)≤D by exact_mod_cast hD)
  exact (le_max_left _ _).trans h

theorem schedule_threshold {K D : ℕ} {c C e : ℝ} (he : 0<e)
    (hD : dimensionBound K c C e≤D) :
    let P := SourceWorkResolution.schedule K c C (e*Real.log (D:ℝ))
    MeanSourceScalarAbsorption.threshold P≤P.y :=
  SourceNumericalAccuracy.resolution_of_dimension he hD

def coolingConstant (ε e : ℝ) : ℝ :=
  1+(Real.log (8/ε^2)+1/e)/Real.log 2

def workConstant (θ Cw ε e : ℝ) : ℝ :=
  4*sourceDimensionPhaseConstant θ (Cw+1) ε e+coolingConstant ε e

theorem coolingConstant_pos {ε e : ℝ} (he : 0<e) (hε : 0<ε) (hε4 : ε<1/4) :
    0<coolingConstant ε e := by
  have ha : 1≤8/ε^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
    nlinarith
  have hl := Real.log_nonneg ha
  have htwo := Real.log_pos (by norm_num : (1:ℝ)<2)
  unfold coolingConstant
  positivity

/-- The actual bias-paid count includes the zero-dimensional case and is
bounded by a dimension-independent coefficient times D^e. -/
theorem cooling_horizon_le {d D : ℕ} {ε e : ℝ} (hd : d≤D) (hD : (1:ℝ)≤D)
    (he : 0<e) (hε : 0<ε) (hε4 : ε<1/4) :
    (CoolingDyadicHorizon.count d ε:ℝ)≤coolingConstant ε e*(D:ℝ)^e := by
  have hDp : (0:ℝ)<D := by linarith
  have ha : 1≤8/ε^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
    nlinarith
  have hap : 0<8/ε^2 := by positivity
  have htwo : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hl : 0≤Real.log (8/ε^2) := Real.log_nonneg ha
  have hm : max 1 (8*(d:ℝ)/ε^2)≤(8/ε^2)*(D:ℝ) := by
    apply max_le
    · exact one_le_mul_of_one_le_of_one_le ha hD
    · have hcast : (d:ℝ)≤D := by exact_mod_cast hd
      calc
        _ = (8/ε^2)*(d:ℝ) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hcast hap.le
  have hlog := Real.log_le_log
    (lt_of_lt_of_le zero_lt_one (le_max_left 1 (8*(d:ℝ)/ε^2))) hm
  rw [Real.log_mul hap.ne' hDp.ne'] at hlog
  have hpow : 1≤(D:ℝ)^e := Real.one_le_rpow hD he.le
  have hlogD := log_dimension_le_rpow_div hD he
  have hratio : (Real.log (8/ε^2)+Real.log (D:ℝ))/Real.log 2≤
      (Real.log (8/ε^2)*(D:ℝ)^e+(D:ℝ)^e/e)/Real.log 2 := by
    apply div_le_div_of_nonneg_right _ htwo.le
    nlinarith [mul_le_mul_of_nonneg_left hpow hl]
  calc
    _ ≤ 1+Real.log (max 1 (8*(d:ℝ)/ε^2))/Real.log 2 := CoolingDyadicHorizon.count_le d ε
    _ ≤ 1+(Real.log (8/ε^2)+Real.log (D:ℝ))/Real.log 2 := by gcongr
    _ ≤ 1+(Real.log (8/ε^2)*(D:ℝ)^e+(D:ℝ)^e/e)/Real.log 2 := by linarith
    _ ≤ (D:ℝ)^e+(Real.log (8/ε^2)*(D:ℝ)^e+(D:ℝ)^e/e)/Real.log 2 :=
      add_le_add hpow le_rfl
    _ = coolingConstant ε e*(D:ℝ)^e := by unfold coolingConstant; ring

/-- The chosen phase horizon pays the common extra dimension factor in the
warmness logarithm, including d=0 through max 1 d. -/
theorem common_warm_budget_le {d D : ℕ} {Cw : ℝ} (hd : d≤D) (hD : (1:ℝ)≤D) :
    (D:ℝ)^Cw*max 1 (d:ℝ)≤(D:ℝ)^(Cw+1) := by
  have hDp : (0:ℝ)<D := by linarith
  have hm : max 1 (d:ℝ)≤D := max_le hD (by exact_mod_cast hd)
  calc
    _ ≤ (D:ℝ)^Cw*(D:ℝ) := mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hDp.le _)
    _ = _ := by rw [Real.rpow_add hDp,Real.rpow_one]

theorem common_warm_exponent_le {d D : ℕ} {Cw ε : ℝ} (hd : d≤D) (hD : (1:ℝ)≤D)
    (hε : 0<ε) :
    warmMixingExponent ((D:ℝ)^Cw*max 1 (d:ℝ)) ε≤
      warmMixingExponent ((D:ℝ)^(Cw+1)) ε := by
  have hDp : (0:ℝ)<D := by linarith
  have hm : 0<max 1 (d:ℝ) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  unfold warmMixingExponent
  apply Real.log_le_log (by positivity)
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (common_warm_budget_le hd hD) (by norm_num : (0:ℝ)≤5)) (by positivity)

/-- Both prescribed counts, with the complete per-block exponential payment. -/
theorem complete_budget_le {d D : ℕ} {θ κ Cw ε e η : ℝ}
    (hd : d≤D) (hD : (1:ℝ)≤D) (hθ : 0<θ) (hκ : 1≤κ) (he : 0<e)
    (hCw : 0≤Cw) (hε : 0<ε) (hε4 : ε<1/4) (heη : e≤η/3) :
    (4*(referenceHorizon (sourceRate θ κ ((D:ℝ)^(-e)))
      (warmMixingExponent ((D:ℝ)^(Cw+1)) ε):ℕ)+(CoolingDyadicHorizon.count d ε:ℝ))*
      Real.exp ((e*Real.log (D:ℝ))/32)≤
        workConstant θ Cw ε e*Real.sqrt κ*(D:ℝ)^η := by
  have hDp : (0:ℝ)<D := by linarith
  have hphase := source_dimension_horizon_le hθ hκ hD he (by linarith : 0≤Cw+1) hε hε4
  have hcool := cooling_horizon_le hd hD he hε hε4
  have hroot : 1≤Real.sqrt κ := by
    apply (Real.le_sqrt (by norm_num) (by linarith : 0≤κ)).mpr
    simpa using hκ
  have hpow : (D:ℝ)^e≤(D:ℝ)^(2*e) := Real.rpow_le_rpow_of_exponent_le hD (by linarith)
  have hc0 := (coolingConstant_pos he hε hε4).le
  have hpc0 := (sourceDimensionPhaseConstant_pos hθ (by linarith : 0≤Cw+1) he hε hε4).le
  have hc : (CoolingDyadicHorizon.count d ε:ℝ)≤
      coolingConstant ε e*Real.sqrt κ*(D:ℝ)^(2*e) := by
    calc
      _ ≤ coolingConstant ε e*(D:ℝ)^e := hcool
      _ ≤ coolingConstant ε e*(D:ℝ)^(2*e) := mul_le_mul_of_nonneg_left hpow hc0
      _ ≤ _ := by nlinarith [mul_nonneg hc0 (Real.rpow_nonneg hDp.le (2*e))]
  have hn : (4*(referenceHorizon (sourceRate θ κ ((D:ℝ)^(-e)))
      (warmMixingExponent ((D:ℝ)^(Cw+1)) ε):ℕ)+(CoolingDyadicHorizon.count d ε:ℝ))≤
      workConstant θ Cw ε e*Real.sqrt κ*(D:ℝ)^(2*e) := by
    unfold workConstant
    nlinarith [hphase]
  have hexp : Real.exp ((e*Real.log (D:ℝ))/32)≤(D:ℝ)^e := by
    calc
      _ = (D:ℝ)^(e/32) := by rw [Real.rpow_def_of_pos hDp]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hD (by linarith)
  have hconst : 0≤workConstant θ Cw ε e := by unfold workConstant; positivity
  calc
    _ ≤ (workConstant θ Cw ε e*Real.sqrt κ*(D:ℝ)^(2*e))*Real.exp ((e*Real.log (D:ℝ))/32) :=
      mul_le_mul_of_nonneg_right hn (Real.exp_nonneg _)
    _ ≤ (workConstant θ Cw ε e*Real.sqrt κ*(D:ℝ)^(2*e))*(D:ℝ)^e :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = workConstant θ Cw ε e*Real.sqrt κ*(D:ℝ)^(3*e) := by
      rw [mul_assoc,← Real.rpow_add hDp]; congr 2; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hD (by linarith)) (by positivity)
/-- The complete literal execution list, including all original-gradient
queries and Gaussian blocks. Entering states, clock labels and whole tapes may
be adaptive; the bound holds on every such list. No work payment or horizon
bound is supplied as an assumption. -/
theorem executed_work_le (K D d : ℕ) (c C θ κ Cw ε e η : ℝ)
    (hK : 10≤K) (hc : 0<c) (hsmall : c<1/160) (hC : 8≤C)
    (hDim : dimensionBound K c C e≤D) (hd : d≤D)
    (hθ : 0<θ) (hκ : 1≤κ) (he : 0<e) (hCw : 0≤Cw)
    (hε : 0<ε) (hε4 : ε<1/4) (heη : e≤η/3) :
    let P := SourceWorkResolution.schedule K c C (e*Real.log (D:ℝ))
    let hyMean := schedule_threshold he hDim
    let hyPrivate := MeanSourceScalarAbsorption.private_threshold P hc (by linarith : c≤1)
      (by linarith : 1≤C) hyMean
    let hyBase := PrivateSourceScalarAbsorption.base_threshold P hc (by linarith : c≤1)
      (by linarith : 1≤C) hyPrivate
    let hR := CubicSchedulePayments.radius_guard P hK hc hsmall hC hyBase
    let N := referenceHorizon (sourceRate θ κ P.delta)
      (warmMixingExponent ((D:ℝ)^(Cw+1)) ε)
    let L := CoolingDyadicHorizon.count d ε
    ∀ (labels : Fin N→ℕ) (G : Point d→Point d)
      (a : ∀ i,(Point d × Point d) × ClockFinitePhaseKernel.Draw P hR hc hsmall (d:=d) (labels i))
      (x : Fin L→Point d)
      (ω : ∀ i : Fin L,CoolingExecutable.FullTape (CoolingPrescribedPayments.setup P hR hc hsmall)
        d P.delta (CoolingDyadicReference.variance P.delta (i:ℕ)) P.K),
      (∑ i : Fin N, (((traceCounts (ClockFinitePhaseWork.execute P hR hc hsmall (labels i)
        (ClockFinitePhaseKernel.sourceGamma P κ) G (a i)).trace).queries+
        (traceCounts (ClockFinitePhaseWork.execute P hR hc hsmall (labels i)
          (ClockFinitePhaseKernel.sourceGamma P κ) G (a i)).trace).gaussianBlocks:ℕ):ℝ))+
      (∑ i : Fin L, (((traceCounts (CoolingExecutable.execute (CoolingPrescribedPayments.setup P hR hc hsmall)
        P.delta (CoolingDyadicReference.variance P.delta (i:ℕ)) P.K G (x i) (ω i)).trace).queries+
        (traceCounts (CoolingExecutable.execute (CoolingPrescribedPayments.setup P hR hc hsmall)
          P.delta (CoolingDyadicReference.variance P.delta (i:ℕ)) P.K G (x i) (ω i)).trace).gaussianBlocks:ℕ):ℝ))≤
      workConstant θ Cw ε e*Real.sqrt κ*(D:ℝ)^η := by
  dsimp only
  intro labels G a x ω
  let P := SourceWorkResolution.schedule K c C (e*Real.log (D:ℝ))
  have hyMean := schedule_threshold he hDim
  have hyPrivate := MeanSourceScalarAbsorption.private_threshold P hc (by linarith : c≤1)
    (by linarith : 1≤C) hyMean
  have hb := CoolingSourceWorkPayment.total_work_paid P hK hc hsmall hC hyPrivate
    _ _ labels (ClockFinitePhaseKernel.sourceGamma P κ) G a
    (fun i => CoolingDyadicReference.variance P.delta (i:ℕ)) x ω
  have hD := dimension_ge_one hDim
  have hp : P.delta=(D:ℝ)^(-e) := SourceNumericalAccuracy.delta_dimension
    (show 0<D by exact_mod_cast (lt_of_lt_of_le zero_lt_one hD))
  refine hb.trans ?_
  change (4*(referenceHorizon (sourceRate θ κ P.delta)
    (warmMixingExponent ((D:ℝ)^(Cw+1)) ε):ℝ)+(CoolingDyadicHorizon.count d ε:ℝ))*
    Real.exp ((e*Real.log (D:ℝ))/32)≤_
  rw [hp]
  have hs := complete_budget_le hd hD hθ hκ he hCw hε hε4 heη
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using hs
end AcceleratedLogConcave.Root.SourcePhaseCoolingDimensionWork
