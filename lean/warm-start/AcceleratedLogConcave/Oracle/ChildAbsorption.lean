import AcceleratedLogConcave.Oracle.CovarianceSetup
import AcceleratedLogConcave.Oracle.NoisyLayer
import AcceleratedLogConcave.Conditional.GaussianAssembly

/-! Actual child-root inverse and a conditional query-shift compiler adapter.
The source program's universal shift property remains an explicit hypothesis. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.ChildAbsorption
open CovarianceSetup NoisyLayer TapeLowering AffineLowering Matrix
open scoped BigOperators
open AcceleratedLogConcave.Conditional.GaussianAssembly

def reserve (rho radius : ℝ) (v : Fin N → ℝ) : ℝ :=
  Real.sqrt (1 - shiftSq (scaledShift rho radius v))
def explicitInverse (rho radius : ℝ) (v : Fin N → ℝ) : Mat N :=
  1 + (1 / (reserve rho radius v * (1 + reserve rho radius v))) •
    vecMulVec (scaledShift rho radius v) (scaledShift rho radius v)
def Admissible (rho radius Ds : ℝ) (v : Fin N → ℝ) : Prop :=
  0 ≤ rho ∧ 0 < radius ∧ 0 < Ds ∧ shiftSq v ≤ Ds^2 ∧ rho ≤ radius/(2*Ds)

theorem scaled_mass_quarter (h : Admissible rho radius Ds v) :
    shiftSq (scaledShift rho radius v) ≤ (1:ℝ)/4 :=
  child_shift_quarter v h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

theorem scaled_mass_lt_one (h : Admissible rho radius Ds v) :
    mass (scaledShift rho radius v) < 1 := by
  have hq := scaled_mass_quarter h
  change mass (scaledShift rho radius v) ≤ (1:ℝ)/4 at hq
  linarith

theorem reserve_pos (h : Admissible rho radius Ds v) : 0 < reserve rho radius v :=
  AcceleratedLogConcave.Conditional.GaussianAssembly.reserve_pos (scaled_mass_lt_one h)

theorem reserve_sq (h : Admissible rho radius Ds v) :
    (reserve rho radius v)^2 = 1 - shiftSq (scaledShift rho radius v) :=
  AcceleratedLogConcave.Conditional.GaussianAssembly.reserve_sq (scaled_mass_lt_one h).le

theorem reserve_half_le (h : Admissible rho radius Ds v) : (1:ℝ)/2 ≤ reserve rho radius v := by
  have h0 := reserve_pos h
  have hs := reserve_sq h
  have hq := scaled_mass_quarter h
  nlinarith

theorem root_formula (h : Admissible rho radius Ds v) :
    childRoot rho radius v = complement (scaledShift rho radius v) :=
  (complement_eq_sqrt (scaled_mass_lt_one h)).symm

theorem root_action (h : Admissible rho radius Ds v) :
    childRoot rho radius v *ᵥ v = fun i => reserve rho radius v * v i := by
  have ha := reserve_pos h
  have hd : 1 + reserve rho radius v ≠ 0 := by positivity
  have hs := reserve_sq h
  rw [shiftSq_scaled] at hs
  have huv : dotProduct (scaledShift rho radius v) v = (rho/radius)*shiftSq v := by
    simp [dotProduct,scaledShift,shiftSq,pow_two,Finset.mul_sum,mul_assoc]
  rw [root_formula h,complement_mulVec]
  ext i
  rw [huv]
  change v i - ((rho/radius)*v i)*((rho/radius)*shiftSq v)/(1+reserve rho radius v) =
    reserve rho radius v * v i
  field_simp
  linear_combination -(v i)*hs

theorem root_mul_explicitInverse (h : Admissible rho radius Ds v) :
    childRoot rho radius v * explicitInverse rho radius v = 1 := by
  let u := scaledShift rho radius v
  let a := reserve rho radius v
  have ha : 0 < a := reserve_pos h
  have hd : 1+a ≠ 0 := by positivity
  have hs : a^2 = 1 - mass u := reserve_sq h
  have hc : 1/(a*(1+a)) - 1/(1+a) - (1/(1+a))*(1/(a*(1+a)))*mass u = 0 := by
    field_simp
    nlinarith
  rw [root_formula h]
  ext i j
  simp only [complement,explicitInverse,mul_add,sub_mul,one_mul,mul_one,smul_mul,
    Matrix.mul_smul,smul_smul,vecMulVec_mul_vecMulVec]
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
    vecMulVec_apply,Pi.smul_apply]
  have huu : dotProduct u u = mass u := by simp [dotProduct,mass,pow_two]
  change (1 : Mat _) i j - (1/(1+a))*(u i*u j) +
    ((1/(a+a*a))*(u i*u j) - (1/(a+a*a))*(1/(1+a))*(u i*((u ⬝ᵥ u)*u j))) = (1 : Mat _) i j
  rw [huu,show a+a*a = a*(1+a) by ring]
  linear_combination (u i*u j)*hc

theorem explicitInverse_mul_root (h : Admissible rho radius Ds v) :
    explicitInverse rho radius v * childRoot rho radius v = 1 := by
  have ht : (childRoot rho radius v).transpose = childRoot rho radius v := by
    rw [root_formula h]
    simp [complement,transpose_sub,transpose_smul,transpose_vecMulVec]
  have hi : (explicitInverse rho radius v).transpose = explicitInverse rho radius v := by
    simp [explicitInverse,transpose_add,transpose_smul,transpose_vecMulVec]
  have he := congrArg Matrix.transpose (root_mul_explicitInverse h)
  simpa only [transpose_mul,ht,hi,transpose_one] using he

theorem inverse_formula (h : Admissible rho radius Ds v) :
    (childRoot rho radius v)⁻¹ = explicitInverse rho radius v ∧
    childRoot rho radius v * explicitInverse rho radius v = 1 ∧
    explicitInverse rho radius v * childRoot rho radius v = 1 :=
  ⟨inv_eq_right_inv (root_mul_explicitInverse h),root_mul_explicitInverse h,explicitInverse_mul_root h⟩


theorem inverse_action (h : Admissible rho radius Ds v) :
    (childRoot rho radius v)⁻¹ *ᵥ v = fun i => v i / reserve rho radius v := by
  have ha := reserve_pos h
  have hi := inverse_formula h
  have hx := congrArg (fun w => (childRoot rho radius v)⁻¹ *ᵥ w) (root_action h)
  change (childRoot rho radius v)⁻¹ *ᵥ (childRoot rho radius v *ᵥ v) =
    (childRoot rho radius v)⁻¹ *ᵥ (reserve rho radius v • v) at hx
  rw [mulVec_mulVec,hi.1,hi.2.2,one_mulVec,mulVec_smul] at hx
  rw [hi.1]
  ext i
  apply (eq_div_iff ha.ne').2
  have hx' := congrFun hx i
  simpa only [Pi.smul_apply,smul_eq_mul,mul_comm] using hx'.symm


/-- The actual inverse is bounded for the Euclidean block-index norm. -/
theorem inverse_euclidean_bound {v : Fin N → ℝ} (h : Admissible rho radius Ds v) (z : Fin N → ℝ) :
    (∑ i, (((childRoot rho radius v)⁻¹ *ᵥ z) i)^2) ≤ 4*(∑ i, (z i)^2) := by
  let u := scaledShift rho radius v
  let a := reserve rho radius v
  let q := 1/(a*(1+a))
  let t := dotProduct u z
  have ha : 0 < a := reserve_pos h
  have ha2 : (1:ℝ)/2 ≤ a := reserve_half_le h
  have hu : mass u ≤ (1:ℝ)/4 := scaled_mass_quarter h
  have hu0 := mass_nonneg u
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq : q ≤ 2 := by
    dsimp [q]
    apply (div_le_iff₀ (show 0 < a*(1+a) by positivity)).2
    nlinarith
  have hq2 : q^2 ≤ 4 := by nlinarith
  have hqu := mul_le_mul_of_nonneg_right hq2 hu0
  have hk : 2*q+q^2*mass u ≤ 5 := by nlinarith
  have hc : t^2 ≤ mass u*(∑ i, (z i)^2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u z
  have hz : 0 ≤ ∑ i, (z i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hc' : t^2 ≤ (1:ℝ)/4*(∑ i, (z i)^2) :=
    hc.trans (mul_le_mul_of_nonneg_right hu hz)
  rw [(inverse_formula h).1]
  have he : explicitInverse rho radius v *ᵥ z = fun i => z i + q*(u i*t) := by
    ext i
    simp [explicitInverse,Matrix.add_mulVec,smul_mulVec,vecMulVec_mulVec,u,q,a,t,mul_comm]
  rw [he]
  have hn : (∑ i, (z i+q*(u i*t))^2) =
      (∑ i, (z i)^2) + (2*q+q^2*mass u)*t^2 := by
    calc
      _ = ∑ i, ((z i)^2+(2*q*t)*(u i*z i)+(q^2*t^2)*(u i)^2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib,← Finset.mul_sum]
        change (∑ i, (z i)^2) + (2*q*t)*t + (q^2*t^2)*mass u = _
        ring
  rw [hn]
  have hk' := mul_le_mul_of_nonneg_right hk (sq_nonneg t)
  nlinarith

/-- Identify the minus-sign source completion with the existing assembly map. -/
theorem completion_formula {v : Fin N → ℝ} (h : Admissible rho radius Ds v)
    (Z : Point d) (ζ : Fin N → Point d) (i : Fin N) :
    transformedGaussian (childRoot rho radius v) ζ i - (scaledShift rho radius v i) • Z =
      active (fun j => -(scaledShift rho radius v j)) Z ζ i := by
  have hm : mass (fun j => -(scaledShift rho radius v j)) < 1 := by
    simpa [mass] using scaled_mass_lt_one h
  have he := active_eq_sqrt_sum hm Z ζ i
  have hv : vecMulVec (fun j => -(scaledShift rho radius v j))
      (fun j => -(scaledShift rho radius v j)) =
      vecMulVec (scaledShift rho radius v) (scaledShift rho radius v) := by
    ext j k
    simp [vecMulVec]
  rw [hv] at he
  change active _ Z ζ i = -(scaledShift rho radius v i) • Z +
    transformedGaussian (childRoot rho radius v) ζ i at he
  rw [he]
  simp only [neg_smul,sub_eq_add_neg,add_comm]

/-- An explicit source property, not a certificate constructed for arbitrary syntax. -/
def QueryShift (p : Program c .point) (e : GaussianSlot p ≃ Fin N)
    (coeff : Fin c → ℝ) (radius : ℝ) (v : Fin N → ℝ) : Prop :=
  ∀ (d : ℕ) (G : Point d → Point d) (x P Δ : Point d)
    (z : Fin N → Point d) (rest : ResidualTape p),
    run p G ⟨coeff,x+Δ,P⟩ Env.empty
      (joinTape p (fun s => z (e s) + (v (e s)/radius) • Δ) rest) =
    run p G ⟨coeff,x,P⟩ Env.empty (joinTape p (fun s => z (e s)) rest)

/-- Every target execution has the shifted source output and the exact paid prefix. -/
theorem run_freshChild_shift (p : Program c .point) (e : GaussianSlot p ≃ Fin N)
    (κ : Fin (N*N+c) → Fin c') (old : Ref Γ .point)
    (designated : Origin) (auxiliary : Fin N → Origin)
    (rho radius : ℝ) (v : Fin N → ℝ) (coeff : Fin c → ℝ)
    (_hr : 0 < radius) (hshift : QueryShift p e coeff radius v)
    (G : Point d → Point d) (input : Inputs d c') (env : Env d Γ) (x Z : Point d)
    (htable : input.coefficient ∘ κ = matrixTable (childRoot rho radius v) coeff)
    (hcenter : storedPoint env old = x + rho • Z)
    (ω : Tape d (freshChild p e κ old designated auxiliary)) :
    let data := freshChildTapeEquiv p e κ old designated auxiliary ω
    let H := fun j => transformedGaussian (childRoot rho radius v) data.2.1 j -
      (scaledShift rho radius v j) • Z
    let source := run p G ⟨coeff,x,data.1⟩ Env.empty
      (joinTape p (fun s => H (e s)) data.2.2)
    run (freshChild p e κ old designated auxiliary) G input env ω =
      ⟨source.value, [Event.gaussian designated] ++
        List.ofFn (fun j => Event.gaussian (auxiliary j)) ++
        source.trace.filter keepNonGaussian⟩ := by
  let data := freshChildTapeEquiv p e κ old designated auxiliary ω
  let H := fun j => transformedGaussian (childRoot rho radius v) data.2.1 j -
    (scaledShift rho radius v j) • Z
  have hs := hshift d G x data.1 (rho • Z) H data.2.2
  have hc (j : Fin N) : (v j/radius)*rho = (rho/radius)*v j := by ring
  have hh : (fun s => H (e s) + (v (e s)/radius) • (rho • Z)) =
      fun s => transformedGaussian (childRoot rho radius v) data.2.1 (e s) := by
    funext s
    simp only [H,scaledShift,smul_smul,hc,sub_add_cancel]
  rw [hh] at hs
  have ht := run_freshChild p e κ old designated auxiliary (childRoot rho radius v)
    coeff G input env htable ω
  change run (freshChild p e κ old designated auxiliary) G input env ω =
    ⟨(run p G ⟨coeff,storedPoint env old,data.1⟩ Env.empty
      (transformedSourceTape p e (childRoot rho radius v) data.2.1 data.2.2)).value,
    [Event.gaussian designated] ++ List.ofFn (fun j => Event.gaussian (auxiliary j)) ++
      (run p G ⟨coeff,storedPoint env old,data.1⟩ Env.empty
        (transformedSourceTape p e (childRoot rho radius v) data.2.1 data.2.2)).trace.filter
        keepNonGaussian⟩ at ht
  rw [hcenter] at ht
  simp only [transformedSourceTape] at ht
  rw [hs] at ht
  exact ht

end AcceleratedLogConcave.Oracle.ChildAbsorption
