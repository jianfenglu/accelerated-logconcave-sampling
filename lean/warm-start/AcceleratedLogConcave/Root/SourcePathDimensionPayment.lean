import AcceleratedLogConcave.Root.SourcePhaseCoolingDimensionWork
import AcceleratedLogConcave.Schedule.DyadicReturnedLaw

/-! Explicit scalar payment for the actual source path-comparison expression.
The phase/cooling counts are prescribed. The condition-number cap is the
manuscript cap, and all constants are fixed before the dimension. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
namespace AcceleratedLogConcave.Root.SourcePathDimensionPayment
open Kinetic SourcePhaseCoolingDimensionWork

def constant (θ Cw ε e C : ℝ) : ℝ :=
  (C/2)*(2*sourceDimensionPhaseConstant θ (Cw+1) ε e+coolingConstant ε e)

theorem inverse_rate_le {D : ℕ} {κ e : ℝ} (hD : (1:ℝ)≤D) (hκ : 1≤κ) (he : 0<e) :
    (Schedule.Dyadic.sourceRate κ ((D:ℝ)^(-e)))⁻¹≤2*Real.sqrt κ*(D:ℝ)^e := by
  have hDp : (0:ℝ)<D := by linarith
  have hh : 0<(D:ℝ)^(-e) := Real.rpow_pos_of_pos hDp _
  have hh1 : (D:ℝ)^(-e)≤1 := Real.rpow_le_one_of_one_le_of_nonpos hD (by linarith)
  have hr : Real.sqrt (κ+2*((D:ℝ)^(-e))^2)≤2*Real.sqrt κ := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · rw [mul_pow,Real.sq_sqrt (by linarith : 0≤κ)]
      nlinarith
  unfold Schedule.Dyadic.sourceRate
  rw [inv_div]
  calc
    _ ≤ 2*Real.sqrt κ/((D:ℝ)^(-e)) := div_le_div_of_nonneg_right hr hh.le
    _ = _ := by rw [div_eq_mul_inv,← Real.rpow_neg hDp.le,neg_neg]

theorem horizon_payment {d D : ℕ} {θ κ Cw ε e : ℝ}
    (hd : d≤D) (hD : (1:ℝ)≤D) (hθ : 0<θ) (hκ : 1≤κ)
    (hcap : κ≤(D:ℝ)^(100:ℕ)) (he : 0<e) (hCw : 0≤Cw)
    (hε : 0<ε) (hε4 : ε<1/4) :
    (referenceHorizon (sourceRate θ κ ((D:ℝ)^(-e)))
      (warmMixingExponent ((D:ℝ)^(Cw+1)) ε):ℝ)/
      Schedule.Dyadic.sourceRate κ ((D:ℝ)^(-e)) + (CoolingDyadicHorizon.count d ε:ℝ) ≤
    (2*sourceDimensionPhaseConstant θ (Cw+1) ε e+coolingConstant ε e)*(D:ℝ)^(100+3*e) := by
  have hDp : (0:ℝ)<D := by linarith
  have hA := (sourceDimensionPhaseConstant_pos hθ (by linarith : 0≤Cw+1) he hε hε4).le
  have hB := (coolingConstant_pos he hε hε4).le
  have hn := source_dimension_horizon_le hθ hκ hD he (by linarith : 0≤Cw+1) hε hε4
  have hi := inverse_rate_le hD hκ he
  have hprod := mul_le_mul hn hi (inv_nonneg.mpr (Schedule.Dyadic.sourceRate_pos hκ (Real.rpow_pos_of_pos hDp _)).le)
    (show 0≤sourceDimensionPhaseConstant θ (Cw+1) ε e*Real.sqrt κ*(D:ℝ)^(2*e) by positivity)
  have hphase : (referenceHorizon (sourceRate θ κ ((D:ℝ)^(-e)))
      (warmMixingExponent ((D:ℝ)^(Cw+1)) ε):ℝ)/
      Schedule.Dyadic.sourceRate κ ((D:ℝ)^(-e)) ≤
      2*sourceDimensionPhaseConstant θ (Cw+1) ε e*κ*(D:ℝ)^(3*e) := by
    rw [div_eq_mul_inv]
    convert hprod using 1
    rw [show 3*e=2*e+e by ring,Real.rpow_add hDp]
    have heq : sourceDimensionPhaseConstant θ (Cw+1) ε e*Real.sqrt κ*(D:ℝ)^(2*e)*
        (2*Real.sqrt κ*(D:ℝ)^e) =
        2*sourceDimensionPhaseConstant θ (Cw+1) ε e*(Real.sqrt κ)^2*((D:ℝ)^(2*e)*(D:ℝ)^e) := by ring
    rw [Real.sq_sqrt (by linarith : 0≤κ)] at heq
    exact heq.symm
  have hcap' : κ≤(D:ℝ)^(100:ℝ) := by simpa using hcap
  have hp : 2*sourceDimensionPhaseConstant θ (Cw+1) ε e*κ*(D:ℝ)^(3*e) ≤
      2*sourceDimensionPhaseConstant θ (Cw+1) ε e*(D:ℝ)^(100+3*e) := by
    rw [Real.rpow_add hDp]
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcap' (by positivity :
      0≤2*sourceDimensionPhaseConstant θ (Cw+1) ε e)) (Real.rpow_nonneg hDp.le (3*e))]
  have hc := cooling_horizon_le hd hD he hε hε4
  have hpow := Real.rpow_le_rpow_of_exponent_le hD (show e≤100+3*e by linarith)
  have hc' := hc.trans (mul_le_mul_of_nonneg_left hpow hB)
  nlinarith [hphase.trans hp]

/-- A fixed order paying the polynomial warmness and condition-number cap. -/
def precision (Cw e : ℝ) : ℕ := Nat.ceil ((Cw+103+5*e)/(2*e))+10

theorem precision_ge_ten (Cw e : ℝ) : 10≤precision Cw e := by unfold precision; omega

theorem precision_payment {Cw e : ℝ} (he : 0<e) :
    Cw+103+5*e≤2*e*(precision Cw e:ℝ) := by
  have h := Nat.le_ceil ((Cw+103+5*e)/(2*e))
  have hp := (div_le_iff₀ (by positivity : 0<2*e)).mp h
  simp only [precision,Nat.cast_add,Nat.cast_ofNat]
  nlinarith

/-- The full path-comparison expression, with actual phase and cooling counts,
vanishes at rate 1/D after the fixed precision is chosen. -/
theorem error_payment {d D K : ℕ} {θ κ Cw ε e C : ℝ}
    (hd : d≤D) (hD : (1:ℝ)≤D) (hθ : 0<θ) (hκ : 1≤κ)
    (hcap : κ≤(D:ℝ)^(100:ℕ)) (he : 0<e) (hCw : 0≤Cw)
    (hε : 0<ε) (hε4 : ε<1/4) (hC : 0≤C) (hK : 1≤K)
    (horder : Cw+103+5*e≤2*e*(K:ℝ)) :
    Real.sqrt ((D:ℝ)^Cw/2*(C*(d:ℝ)*((D:ℝ)^(-e))^(2*K-2))*
      ((referenceHorizon (sourceRate θ κ ((D:ℝ)^(-e)))
        (warmMixingExponent ((D:ℝ)^(Cw+1)) ε):ℝ)/
        Schedule.Dyadic.sourceRate κ ((D:ℝ)^(-e))+(CoolingDyadicHorizon.count d ε:ℝ))) ≤
      Real.sqrt (constant θ Cw ε e C)/(D:ℝ) := by
  have hDp : (0:ℝ)<D := by linarith
  have hA := (sourceDimensionPhaseConstant_pos hθ (by linarith : 0≤Cw+1) he hε hε4).le
  have hB := (coolingConstant_pos he hε hε4).le
  have hc : 0≤constant θ Cw ε e C := by unfold constant; positivity
  have hh := horizon_payment hd hD hθ hκ hcap he hCw hε hε4
  have hpre : (D:ℝ)^Cw/2*(C*(d:ℝ)*((D:ℝ)^(-e))^(2*K-2)) ≤
      (D:ℝ)^Cw/2*(C*(D:ℝ)*((D:ℝ)^(-e))^(2*K-2)) := by
    gcongr
  have hrate := Schedule.Dyadic.sourceRate_pos hκ (Real.rpow_pos_of_pos hDp (-e))
  have hs := mul_le_mul hpre hh (by positivity : 0≤
    (referenceHorizon (sourceRate θ κ ((D:ℝ)^(-e)))
      (warmMixingExponent ((D:ℝ)^(Cw+1)) ε):ℝ)/
      Schedule.Dyadic.sourceRate κ ((D:ℝ)^(-e))+(CoolingDyadicHorizon.count d ε:ℝ))
    (by positivity : 0≤(D:ℝ)^Cw/2*(C*(D:ℝ)*((D:ℝ)^(-e))^(2*K-2)))
  have hid : ((D:ℝ)^Cw/2*(C*(D:ℝ)*((D:ℝ)^(-e))^(2*K-2)))*
      ((2*sourceDimensionPhaseConstant θ (Cw+1) ε e+coolingConstant ε e)*(D:ℝ)^(100+3*e)) =
      constant θ Cw ε e C*(D:ℝ)^(Cw+101+5*e-2*e*(K:ℝ)) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hDp.le]
    calc
      _ = constant θ Cw ε e C *
          (((D:ℝ)^Cw*(D:ℝ)^((1:ℝ)))*(D:ℝ)^(-e*((2*K-2:ℕ):ℝ))*(D:ℝ)^(100+3*e)) := by
        rw [Real.rpow_one]
        unfold constant
        ring
      _ = _ := by
        rw [← Real.rpow_add hDp,← Real.rpow_add hDp,← Real.rpow_add hDp]
        congr 2
        rw [Nat.cast_sub (by omega : 2≤2*K)]
        simp only [Nat.cast_mul,Nat.cast_ofNat]
        ring
  rw [hid] at hs
  have hexp : Cw+101+5*e-2*e*(K:ℝ)≤-2 := by linarith
  have hb := hs.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hD hexp) hc)
  apply (Real.sqrt_le_iff).2
  refine ⟨by positivity,?_⟩
  convert hb using 1
  rw [div_pow,Real.sq_sqrt hc,Real.rpow_neg hDp.le]
  norm_num
  ring

/-- An explicit dimension threshold pays a requested scalar error allocation. -/
def dimensionThreshold (θ Cw ε e C εout : ℝ) : ℕ :=
  Nat.ceil (max 1 (Real.sqrt (constant θ Cw ε e C)/εout))

theorem epsilon_payment {d D K : ℕ} {θ κ Cw ε e C εout : ℝ}
    (hd : d≤D) (hD : (1:ℝ)≤D) (hθ : 0<θ) (hκ : 1≤κ)
    (hcap : κ≤(D:ℝ)^(100:ℕ)) (he : 0<e) (hCw : 0≤Cw)
    (hε : 0<ε) (hε4 : ε<1/4) (hC : 0≤C) (hK : 1≤K)
    (horder : Cw+103+5*e≤2*e*(K:ℝ)) (hout : 0<εout)
    (hthreshold : dimensionThreshold θ Cw ε e C εout≤D) :
    Real.sqrt ((D:ℝ)^Cw/2*(C*(d:ℝ)*((D:ℝ)^(-e))^(2*K-2))*
      ((referenceHorizon (sourceRate θ κ ((D:ℝ)^(-e)))
        (warmMixingExponent ((D:ℝ)^(Cw+1)) ε):ℝ)/
        Schedule.Dyadic.sourceRate κ ((D:ℝ)^(-e))+(CoolingDyadicHorizon.count d ε:ℝ))) ≤ εout := by
  refine (error_payment hd hD hθ hκ hcap he hCw hε hε4 hC hK horder).trans ?_
  have ht : max 1 (Real.sqrt (constant θ Cw ε e C)/εout)≤(D:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hthreshold)
  have hp := (div_le_iff₀ hout).mp ((le_max_right _ _).trans ht)
  exact (div_le_iff₀ (by linarith : (0:ℝ)<D)).mpr (by nlinarith [hp])
end AcceleratedLogConcave.Root.SourcePathDimensionPayment
