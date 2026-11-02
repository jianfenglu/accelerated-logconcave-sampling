import AcceleratedLogConcave.Tensor.ActualForwardFlowBounds
import Mathlib.Analysis.Complex.ExponentialBounds
import AcceleratedLogConcave.Tensor.FiniteOrderMass
import AcceleratedLogConcave.Conditional.Stein.SpatialDisplacement
import AcceleratedLogConcave.Tensor.AdjointReduction

/-! Exact all-proper displacement coefficients of the
actual forward endpoint. The first derivative uses DT-Id cancellation; higher
orders use the newly derived forward induction. The physical slot chart keeps
all derivative/output indices, and has constant-one loss for every proper cut.
No Gaussian moment is estimated by a Hilbert--Schmidt tensor norm here. -/
noncomputable section
set_option autoImplicit false
open Set
open scoped BigOperators Classical ContDiff
namespace AcceleratedLogConcave.Tensor.ForwardFlow
open Conditional ActualCoefficient EdgeClosure FlowInduction AdjointReduction
open AcceleratedLogConcave.Analysis.SpatialVariation
variable {D : ℕ}

/-- A positive-order displacement coefficient in the standard vector slots. -/
def displacementJetCoeff (T : Space D → Space D) (n : ℕ) (y : Space D) :
    Coeff (Fin n ⊕ Unit) D :=
  vectorCoeff (iteratedFDeriv ℝ n (fun z => T z-z) y)

theorem displacementJetCoeff_one (T : Space D → Space D) (hT : Differentiable ℝ T)
    (y : Space D) :
    displacementJetCoeff T 1 y = rankTwoCoeff
      (fderiv ℝ T y-ContinuousLinearMap.id ℝ (Space D)) := by
  have hd := fderiv_fun_sub (hT y) (differentiableAt_id (x := y) (𝕜 := ℝ))
  simp only [id_eq,fderiv_id] at hd
  rw [displacementJetCoeff,vectorCoeff_one_eq_rankTwo,hd]

/-- Removing the identity at every order at least two is an exact equality. -/
theorem displacementJetCoeff_ge_two (T : Space D → Space D) (hT : ContDiff ℝ ∞ T)
    (n : ℕ) (hn : 2 ≤ n) (y : Space D) :
    displacementJetCoeff T n y = vectorCoeff (iteratedFDeriv ℝ n T y) := by
  have hid : iteratedFDeriv ℝ n (id : Space D → Space D) y = 0 := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le' hn
    ext v
    rw [← along_ofFn_eq_iteratedFDeriv contDiff_id]
    rw [List.ofFn_succ,List.ofFn_succ,along_id_at_least_two]
    rfl
  have hTn : ContDiff ℝ n T := hT.of_le (by simp)
  have hIn : ContDiff ℝ n (id : Space D → Space D) := contDiff_id
  have he := iteratedFDeriv_sub_apply hTn.contDiffAt hIn.contDiffAt (x := y)
  change iteratedFDeriv ℝ n (fun z => T z-z) y = _ at he
  rw [displacementJetCoeff,he,hid,sub_zero]

/-- First derivative first, followed by the j ordered spatial derivative slots.
Output is inr 0; the distinguished gradient input is inr 1. -/
def displacementSlotChart (j : ℕ) : (Fin (j+1) ⊕ Unit) ≃ (Fin j ⊕ Fin 2) where
  toFun
    | .inl i => Fin.cases (.inr 1) (fun k => .inl k) i
    | .inr _ => .inr 0
  invFun
    | .inl i => .inl i.succ
    | .inr k => if k = 0 then .inr () else .inl 0
  left_inv := by
    intro a
    rcases a with i | u
    · refine Fin.cases ?_ (fun k => ?_) i <;> rfl
    · cases u; rfl
  right_inv := by
    intro a
    rcases a with i | k
    · rfl
    · fin_cases k <;> rfl

/-- Literal Frechet tensor in precisely the historical angle receiver slots. -/
def physicalDisplacementCoeff (T : Space D → Space D) (j : ℕ) (y : Space D) :
    Coeff (Fin j ⊕ Fin 2) D :=
  WithLp.toLp 2 (fun a => inner ℝ (basis D (a (.inr 0)))
    (iteratedFDeriv ℝ (j+1) (fun z => T z-z) y
      (Fin.cons (basis D (a (.inr 1))) (fun i => basis D (a (.inl i))))))

theorem physicalDisplacementCoeff_eq_relabel (T : Space D → Space D)
    (j : ℕ) (y : Space D) :
    physicalDisplacementCoeff T j y =
      relabel D (displacementSlotChart j) (displacementJetCoeff T (j+1) y) := by
  ext a
  rfl

/-- Actual forward endpoint has all-order smoothness from original data. -/
theorem contDiff_forwardEndpoint (d : PositiveVarianceFlowData (Space D))
    (hsmall : d.r^2*d.ell ≤ 1/2) (ρ : Icc (0:ℝ) d.b) :
    ContDiff ℝ ∞ (forwardProbabilityTransport d.hF d.hell d.hlo d.hhi d.x
      d.hr d.hb0 d.hb1 ρ : Space D → Space D) := by
  rw [← forwardY_terminal d ρ]
  exact contDiff_forwardY d hsmall ρ ⟨d.hb0,le_rfl⟩

/-- Retains the curvature factor at derivative order one instead of using e+1. -/
theorem original_data_forward_displacement_one_allProper
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (ρ : Icc (0:ℝ) d.b) (y : Space D) :
    AllProper D (displacementJetCoeff
      (forwardProbabilityTransport d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 ρ) 1 y)
      (Real.exp 1*(d.r^2*d.ell)*(d.b-(ρ:ℝ))) := by
  rw [displacementJetCoeff_one _
    ((contDiff_forwardEndpoint d hsmall ρ).differentiable (by simp)) y]
  intro S hS
  exact (rankTwo_splitNorm_le _ S hS).trans
    (norm_fderiv_forwardProbabilityTransport_sub_id_le d.hF d.hell d.hlo d.hhi
      d.x d.hr d.hb0 d.hb1 hsmall ρ.property y)

/-- The original spatial scale has no hidden dimension loss or endpoint division. -/
theorem forward_scale_pow_le_radius {b R : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hR : 0 < R) (k : ℕ) : (b/R)^k ≤ R^(-(k:ℝ)) := by
  rw [div_pow,Real.rpow_neg hR.le,Real.rpow_natCast,div_eq_mul_inv]
  exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hb0 hb1) (by positivity)).trans_eq (one_mul _)

/-- Arithmetic only, preserving the exact radius exponent 1-n. -/
theorem forward_order_scalar_le {α ρ b R c : ℝ}
    (hα : 0 ≤ α) (hρ0 : 0 ≤ ρ) (hρb : ρ ≤ b)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hR : 0 < R) (hc : 32 ≤ c)
    (n : ℕ) (hn : 1 ≤ n) :
    (α*(b^2-ρ^2)/2)*(b/R)^(n-1)*orderConstant n ≤
      α*c^n*(n.factorial : ℝ)*R^((1:ℝ)-(n:ℝ)) := by
  have hclock : 0 ≤ α*(b^2-ρ^2)/2 := by
    have : 0 ≤ b^2-ρ^2 := by nlinarith
    positivity
  have hclock' : α*(b^2-ρ^2)/2 ≤ α := by
    have hd : b^2-ρ^2 ≤ 1 := by nlinarith [sq_nonneg ρ]
    have h := mul_le_mul_of_nonneg_left hd hα
    nlinarith
  have hc0 : 0 ≤ c := by linarith
  have hp := forward_scale_pow_le_radius hb0 hb1 hR (n-1)
  have hconst : orderConstant n ≤ c^n*(n.factorial : ℝ) := by
    have h := orderConstant_growth n hn
    have hp' := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 32) hc n
    have hm := mul_le_mul_of_nonneg_left hp' (Nat.cast_nonneg n.factorial)
    have hn0 : 0 ≤ (n.factorial : ℝ)*(32:ℝ)^n := by positivity
    nlinarith
  have hprod := mul_le_mul hclock' hp (pow_nonneg (div_nonneg hb0 hR.le) _)
    hα
  have hfull := mul_le_mul hprod hconst (orderConstant_nonneg n)
    (mul_nonneg hα (Real.rpow_nonneg hR.le _))
  have hexp : -((n-1:ℕ):ℝ) = (1:ℝ)-(n:ℝ) := by
    rw [Nat.cast_sub hn]
    push_cast
    ring
  rw [hexp] at hfull
  nlinarith

/-- Every positive displacement order: no desired norm budget occurs as a premise. -/
theorem original_data_forward_displacement_allProper
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (ρ : Icc (0:ℝ) d.b) {c : ℝ} (hc : 32 ≤ c)
    (n : ℕ) (hn : 1 ≤ n) (y : Space D) :
    AllProper D (displacementJetCoeff
      (forwardProbabilityTransport d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 ρ) n y)
      (2*(d.r^2*d.ell)*c^n*(n.factorial : ℝ)*
        (Real.sqrt (1-d.b^2))^((1:ℝ)-(n:ℝ))) := by
  have hα := flowAlpha_nonneg d
  have hc0 : 0 ≤ c := by linarith
  have hR : 0 < Real.sqrt (1-d.b^2) :=
    Real.sqrt_pos.mpr (conditionalVariance_pos (by linarith [d.hb0]) d.hb1)
  by_cases hn1 : n = 1
  · subst n
    intro S hS
    have h := original_data_forward_displacement_one_allProper d hsmall ρ y S hS
    have hbρ : 0 ≤ d.b-(ρ:ℝ) := sub_nonneg.mpr ρ.property.2
    have hbρ' : d.b-(ρ:ℝ) ≤ 1 := by linarith [d.hb1,ρ.property.1]
    have he := Real.exp_one_lt_three.le
    have hm := mul_le_mul_of_nonneg_right hbρ' (Real.exp_pos 1).le
    have hnum : Real.exp 1*(d.b-(ρ:ℝ)) ≤ 2*c := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hnum hα
    norm_num
    dsimp only [flowAlpha] at hα hmul
    nlinarith
  · have hn2 : 2 ≤ n := by omega
    rw [displacementJetCoeff_ge_two _ (contDiff_forwardEndpoint d hsmall ρ) n hn2 y]
    intro S hS
    have h := original_data_forward_endpoint_higher_allProper d hsmall ρ n hn2 y S hS
    have hscalar := forward_order_scalar_le (flowAlpha_nonneg d) ρ.property.1 ρ.property.2
      d.hb0 d.hb1.le hR hc n hn
    have hnonneg : 0 ≤ (d.r^2*d.ell)*c^n*(n.factorial : ℝ)*
        (Real.sqrt (1-d.b^2))^((1:ℝ)-(n:ℝ)) := by positivity
    dsimp only [forwardClock,flowScale,flowAlpha] at h hscalar
    nlinarith

/-- The exact proper-cut premise expected by AnglePhysicalBudgets, at c=256. -/
theorem original_data_physicalDisplacement_budget
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (ρ : Icc (0:ℝ) d.b) (j : ℕ) (y : Space D)
    (S : Finset (Fin j ⊕ Fin 2)) (hS : NontrivialSplit S) :
    splitNorm D S (physicalDisplacementCoeff
      (forwardProbabilityTransport d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 ρ) j y) ≤
      2*(d.r^2*d.ell)*(256:ℝ)^(j+1)*((j+1).factorial : ℝ)*
        (Real.sqrt (1-d.b^2))^((1:ℝ)-((j+1:ℕ):ℝ)) := by
  rw [physicalDisplacementCoeff_eq_relabel]
  exact (original_data_forward_displacement_allProper d hsmall ρ (by norm_num : (32:ℝ) ≤ 256)
    (j+1) (by omega) y).relabel (displacementSlotChart j) S hS

/-- Literal D=0 check, independent of any estimate or source law. -/
theorem physicalDisplacementCoeff_dimension_zero (T : Space 0 → Space 0)
    (j : ℕ) (y : Space 0) : physicalDisplacementCoeff T j y = 0 := by
  ext a
  exact Fin.elim0 (a (.inr 0))

/-- The directional-list encoding has the same literal order as iteratedFDeriv. -/
theorem along_map_eq_partialAlong {I : Type*} (v : I → Space D)
    (J : List I) (f : Space D → ℝ) :
    along (J.map v) f = partialAlong v J f := by
  induction J with
  | nil => rfl
  | cons i J ih =>
    simp only [List.map_cons,along,partialAlong]
    rw [ih]
    rfl

/-- Exact ordered-coordinate expression consumed by the Gaussian angle chart.
The first derivative slot is not commuted past or identified with another slot. -/
theorem physicalDisplacementCoeff_eq_ordered (T : Space D → Space D)
    (hT : ContDiff ℝ ∞ T) (j : ℕ) (y : Space D) :
    physicalDisplacementCoeff T j y = WithLp.toLp 2 (fun a =>
      partialAlong (basis D)
        (a (.inr 1)::(List.finRange j).map (fun i => a (.inl i)))
        (fun z => inner ℝ (basis D (a (.inr 0))) (T z-z)) y) := by
  have hD : ContDiff ℝ ∞ (fun z => T z-z) := by
    simpa only [id_eq] using hT.sub contDiff_id
  ext a
  change inner ℝ (basis D (a (.inr 0)))
    (iteratedFDeriv ℝ (j+1) (fun z => T z-z) y
      (Fin.cons (basis D (a (.inr 1))) (fun i => basis D (a (.inl i))))) = _
  rw [← along_ofFn_eq_iteratedFDeriv hD]
  let J := List.ofFn (Fin.cons (basis D (a (.inr 1))) (fun i => basis D (a (.inl i))))
  have hc := congrFun (along_clm hD (innerSL ℝ (basis D (a (.inr 0)))) J) y
  change along J (fun z => inner ℝ (basis D (a (.inr 0))) (T z-z)) y =
    inner ℝ (basis D (a (.inr 0))) (along J (fun z => T z-z) y) at hc
  rw [← hc]
  dsimp only [J]
  rw [List.ofFn_cons,List.ofFn_eq_map]
  simpa only [List.map_cons,List.map_map,Function.comp_def] using
    congrFun (along_map_eq_partialAlong (basis D)
      (a (.inr 1)::(List.finRange j).map (fun i => a (.inl i)))
      (fun z => inner ℝ (basis D (a (.inr 0))) (T z-z))) y

/-- Zero curvature kills every positive displacement coefficient cut, not
necessarily the displacement value, which may be a nonzero translation. -/
theorem physicalDisplacement_allProper_zero_curvature
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (hell : d.ell = 0) (ρ : Icc (0:ℝ) d.b) (j : ℕ) (y : Space D) :
    AllProper D (physicalDisplacementCoeff
      (forwardProbabilityTransport d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 ρ) j y) 0 := by
  intro S hS
  simpa only [hell,mul_zero,zero_mul] using
    original_data_physicalDisplacement_budget d hsmall ρ j y S hS

/-- The singleton slab has identity forward endpoint and zero displacement. -/
theorem physicalDisplacement_zero_of_terminal_zero
    (d : PositiveVarianceFlowData (Space D)) (hb : d.b = 0)
    (ρ : Icc (0:ℝ) d.b) (j : ℕ) (y : Space D) :
    physicalDisplacementCoeff
      (forwardProbabilityTransport d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 ρ) j y = 0 := by
  have hρ : (ρ:ℝ) = d.b := by
    apply le_antisymm ρ.property.2
    linarith [ρ.property.1]
  have he : (forwardProbabilityTransport d.hF d.hell d.hlo d.hhi d.x
      d.hr d.hb0 d.hb1 ρ : Space D → Space D) = id := by
    funext z
    rw [hρ]
    exact forwardProbabilityTransport_terminal d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 z
  rw [he]
  ext a
  simp [physicalDisplacementCoeff]

end AcceleratedLogConcave.Tensor.ForwardFlow
