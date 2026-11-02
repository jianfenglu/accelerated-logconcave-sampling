import AcceleratedLogConcave.Tensor.ActualForwardSpatialVariations
import AcceleratedLogConcave.Analysis.ForwardClosedComparison
import AcceleratedLogConcave.Tensor.OriginalDataFlowBounds

/-! Original-data all-proper FORWARD flow induction.
The trajectory starts at rho and ends at a larger running time. Its variation
and endpoint identification come from ActualForwardSpatialVariations, not from
renaming backward P_n or composing terminal-coordinate inverse-Jacobian jets.
The exact same partition recurrence is reused only after the forward ODE is paid. -/
noncomputable section
set_option autoImplicit false
open Set
open scoped BigOperators Classical ContDiff
namespace AcceleratedLogConcave.Tensor.ForwardFlow
open Conditional ActualCoefficient EdgeClosure FlowInduction ActualPartitionTree
open AcceleratedLogConcave.Analysis.SpatialVariation
open AcceleratedLogConcave.Analysis.SpatialPartition
open AcceleratedLogConcave.Analysis.FixedCut
variable {D : ℕ}

def forwardClock (d : PositiveVarianceFlowData (Space D)) (ρ t : ℝ) : ℝ :=
  flowAlpha d * (t^2-ρ^2)/2

theorem forwardClock_bounds (d : PositiveVarianceFlowData (Space D))
    (hsmall : d.r^2*d.ell ≤ 1/2) (ρ : Icc (0:ℝ) d.b)
    {t : ℝ} (ht : t ∈ Icc (ρ:ℝ) d.b) :
    0 ≤ forwardClock d ρ t ∧ forwardClock d ρ t ≤ 1/4 := by
  have ha := flowAlpha_nonneg d
  have hd : 0 ≤ t^2-(ρ:ℝ)^2 := by nlinarith [ρ.property.1,ht.1]
  have hd' : t^2-(ρ:ℝ)^2 ≤ 1 := by nlinarith [ρ.property.1,ht.1,ht.2,d.hb0,d.hb1,sq_nonneg (ρ:ℝ)]
  have hm := mul_le_mul hsmall hd' hd (by norm_num : (0:ℝ) ≤ 1/2)
  constructor
  · exact div_nonneg (mul_nonneg ha hd) (by norm_num)
  · change (d.r^2*d.ell)*(t^2-(ρ:ℝ)^2)/2 ≤ 1/4
    nlinarith

theorem forwardJetCoeff_initial_one_le (d : PositiveVarianceFlowData (Space D))
    (ρ : Icc (0:ℝ) d.b) (y : Space D)
    (S : Finset (Fin 1 ⊕ Unit)) (hS : NontrivialSplit S) :
    splitNorm D S (forwardJetCoeff d ρ 1 y ρ) ≤ 1 := by
  change splitNorm D S (vectorCoeff (iteratedFDeriv ℝ 1 (forwardY d ρ ρ) y)) ≤ _
  rw [forwardY_initial,vectorCoeff_one_eq_rankTwo,fderiv_id]
  apply (rankTwo_splitNorm_le _ S hS).trans
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simp

theorem forwardJetCoeff_initial_ge_two_zero (d : PositiveVarianceFlowData (Space D))
    (ρ : Icc (0:ℝ) d.b) (n : ℕ) (hn : 2 ≤ n) (y : Space D) :
    forwardJetCoeff d ρ n y ρ = 0 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le' hn
  ext a
  change inner ℝ (basis D (a (.inr ())))
    (iteratedFDeriv ℝ (k+2) (forwardY d ρ ρ) y
      (fun j => basis D (a (.inl j)))) = 0
  rw [forwardY_initial,← along_ofFn_eq_iteratedFDeriv contDiff_id]
  rw [List.ofFn_succ,List.ofFn_succ,along_id_at_least_two]
  simp

/-- The first order is initialized by the identity, including D=0. -/
theorem original_data_forward_first_allProper
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (ρ : Icc (0:ℝ) d.b) (y : Space D)
    {t : ℝ} (ht : t ∈ Icc (ρ:ℝ) d.b) :
    AllProper D (forwardJetCoeff d ρ 1 y t) (Real.exp (forwardClock d ρ t)) := by
  intro S hS
  obtain ⟨hv,hb⟩ := forward_unfolded_variation d hsmall ρ 1 (by omega) y S
  have hsub : Icc (ρ:ℝ) d.b ⊆ Icc (0:ℝ) d.b :=
    fun s hs => ⟨ρ.property.1.trans hs.1,hs.2⟩
  have hf (s : ℝ) : forwardForcingCoeff d ρ 1 (by omega) y s = 0 := by
    ext a
    simp [forwardForcingCoeff,spatialForcing_one,vectorCoeff,mapCoeff]
  have h := forward_homogeneous_bound (flowAlpha_nonneg d)
    (fun s hs => ((hv s (hsub hs)).mono hsub).continuousWithinAt)
    (fun s hs => (hv s (hsub hs)).mono hsub)
    (forwardJetCoeff_initial_one_le d ρ y S hS)
    (fun s hs => by
      have h := hb s (hsub hs)
      rw [hf,splitNorm_zero,add_zero] at h
      exact h.trans (mul_le_mul_of_nonneg_right
        (norm_fderiv_probabilityVelocity_le d (forwardY d ρ s y) (hsub hs))
        (splitNorm_nonneg D S _))) ht
  simpa only [one_mul,forwardClock,splitNorm] using h

/-- Only strictly lower positive forward jets occur in this local forcing lemma. -/
theorem forward_forcing_from_lower_orders
    (d : PositiveVarianceFlowData (Space D)) (ρ : Icc (0:ℝ) d.b)
    (n : ℕ) (hn : 0 < n) (y : Space D) {s : ℝ} (hs : s ∈ Icc 0 d.b)
    (hbranch : ∀ j, 1 ≤ j → j < n →
      AllProper D (forwardJetCoeff d ρ j y s)
        (flowScale d^(j-1)*orderConstant j)) :
    AllProper D (forwardForcingCoeff d ρ n hn y s)
      (flowAlpha d*s*(flowScale d^(n-1)*forcingConstant n hn)) := by
  have h := spatialForcing_allProper
    (probabilityVelocity d.F d.x d.r s) (forwardY d ρ s) y n hn
    (fun k => flowAlpha d*s*primitiveConstant k*flowScale d^(k-1))
    (fun j => flowScale d^(j-1)*orderConstant j)
    (fun k => mul_nonneg
      (mul_nonneg (mul_nonneg (flowAlpha_nonneg d) hs.1) (primitiveConstant_nonneg k))
      (pow_nonneg (flowScale_nonneg d) _))
    (fun j => mul_nonneg (pow_nonneg (flowScale_nonneg d) _) (orderConstant_nonneg j))
    (fun k hk _ => probabilityVelocity_allProper_ge_two d k hk (forwardY d ρ s y) hs)
    hbranch
  rw [show (∑ c ∈ (Finset.univ : Finset (OrderedFinpartition n)).erase
      (OrderedFinpartition.oneBlock n hn),
      (flowAlpha d*s*primitiveConstant c.length*flowScale d^(c.length-1)) *
        ∏ i, flowScale d^(c.partSize i-1)*orderConstant (c.partSize i)) =
      flowAlpha d*s*flowScale d^(n-1)*forcingConstant n hn from
        forcing_weight n hn (flowAlpha d) s (flowScale d)] at h
  simpa only [mul_assoc] using h

/-- Original-data forward all-proper induction, with the correct forward clock.
No continuity, inverse-map chain, lower-jet budget, or desired envelope is a premise. -/
theorem original_data_forward_higher_allProper
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (ρ : Icc (0:ℝ) d.b) (n : ℕ) (hn : 2 ≤ n) (y : Space D)
    {t : ℝ} (ht : t ∈ Icc (ρ:ℝ) d.b) :
    AllProper D (forwardJetCoeff d ρ n y t)
      (forwardClock d ρ t*flowScale d^(n-1)*orderConstant n) := by
  suffices hall : ∀ m, 2 ≤ m → ∀ z : Space D, ∀ u : ℝ, u ∈ Icc (ρ:ℝ) d.b →
      AllProper D (forwardJetCoeff d ρ m z u)
        (forwardClock d ρ u*flowScale d^(m-1)*orderConstant m) from hall n hn y t ht
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn y t ht
    have hsub : Icc (ρ:ℝ) d.b ⊆ Icc (0:ℝ) d.b :=
      fun s hs => ⟨ρ.property.1.trans hs.1,hs.2⟩
    have hforce (s : ℝ) (hs : s ∈ Icc (ρ:ℝ) d.b) :
        AllProper D (forwardForcingCoeff d ρ n (by omega) y s)
          (flowAlpha d*s*(flowScale d^(n-1)*forcingConstant n (by omega))) := by
      apply forward_forcing_from_lower_orders d ρ n (by omega) y (hsub hs)
      intro j hj hjn S hS
      by_cases hj1 : j = 1
      · subst j
        have hfirst := original_data_forward_first_allProper d hsmall ρ y hs S hS
        have he : Real.exp (forwardClock d ρ s) ≤ growthConstant :=
          Real.exp_le_exp.mpr (forwardClock_bounds d hsmall ρ hs).2
        simpa [orderConstant_small (show 1 < 2 by omega)] using hfirst.trans he
      · have hl := ih j hjn (by omega) y s hs S hS
        have hc := forwardClock_bounds d hsmall ρ hs
        have hweight : 0 ≤ flowScale d^(j-1)*orderConstant j :=
          mul_nonneg (pow_nonneg (flowScale_nonneg d) _) (orderConstant_nonneg j)
        calc
          _ ≤ forwardClock d ρ s*flowScale d^(j-1)*orderConstant j := hl
          _ = forwardClock d ρ s*(flowScale d^(j-1)*orderConstant j) := mul_assoc _ _ _
          _ ≤ 1*(flowScale d^(j-1)*orderConstant j) :=
            mul_le_mul_of_nonneg_right (hc.2.trans (by norm_num)) hweight
          _ = _ := one_mul _
    intro S hS
    obtain ⟨hv,hbound⟩ := forward_unfolded_variation d hsmall ρ n (by omega) y S
    have h := forward_proportional_forcing (flowAlpha_nonneg d)
      (fun s hs => ((hv s (hsub hs)).mono hsub).continuousWithinAt)
      (fun s hs => (hv s (hsub hs)).mono hsub)
      (by rw [forwardJetCoeff_initial_ge_two_zero d ρ n hn y,map_zero])
      (fun s hs => (hbound s (hsub hs)).trans (add_le_add
        (mul_le_mul_of_nonneg_right
          (norm_fderiv_probabilityVelocity_le d (forwardY d ρ s y) (hsub hs))
          (splitNorm_nonneg D S _)) (hforce s hs S hS))) ht
    have hw : 0 ≤ flowScale d^(n-1)*forcingConstant n (by omega) :=
      mul_nonneg (pow_nonneg (flowScale_nonneg d) _) (forcingConstant_nonneg _ _)
    have hc := forwardClock_bounds d hsmall ρ ht
    calc
      _ ≤ (flowScale d^(n-1)*forcingConstant n (by omega)) *
          (Real.exp (forwardClock d ρ t)-1) := h
      _ ≤ (flowScale d^(n-1)*forcingConstant n (by omega)) *
          (forwardClock d ρ t*growthConstant) :=
        mul_le_mul_of_nonneg_left (exp_sub_one_le hc.1 hc.2) hw
      _ = forwardClock d ρ t*flowScale d^(n-1)*orderConstant n := by
        rw [orderConstant_recurrence hn]
        ring

/-- Every actual forward endpoint, in the original vector coefficient slots. -/
theorem original_data_forward_endpoint_higher_allProper
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (ρ : Icc (0:ℝ) d.b) (n : ℕ) (hn : 2 ≤ n) (y : Space D) :
    AllProper D (vectorCoeff (iteratedFDeriv ℝ n
      (forwardProbabilityTransport d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 ρ) y))
      (forwardClock d ρ d.b*flowScale d^(n-1)*orderConstant n) := by
  have h := original_data_forward_higher_allProper d hsmall ρ n hn y
    (show d.b ∈ Icc (ρ:ℝ) d.b from ⟨ρ.property.2,le_rfl⟩)
  change AllProper D (vectorCoeff (iteratedFDeriv ℝ n (forwardY d ρ d.b) y)) _ at h
  rwa [forwardY_terminal] at h

/-- Both degeneracies preserve the small factor without dividing by it. -/
theorem forward_higher_cut_zero_of_curvature_zero
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (hell : d.ell = 0) (ρ : Icc (0:ℝ) d.b) (n : ℕ) (hn : 2 ≤ n)
    (y : Space D) (S : Finset (Fin n ⊕ Unit)) (hS : NontrivialSplit S)
    {t : ℝ} (ht : t ∈ Icc (ρ:ℝ) d.b) :
    splitNorm D S (forwardJetCoeff d ρ n y t) = 0 := by
  apply le_antisymm _ (splitNorm_nonneg D S _)
  simpa [forwardClock,flowAlpha,hell] using
    original_data_forward_higher_allProper d hsmall ρ n hn y ht S hS

theorem forward_higher_cut_zero_of_terminal_zero
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (hb : d.b = 0) (ρ : Icc (0:ℝ) d.b) (n : ℕ) (hn : 2 ≤ n)
    (y : Space D) (S : Finset (Fin n ⊕ Unit)) (hS : NontrivialSplit S)
    {t : ℝ} (ht : t ∈ Icc (ρ:ℝ) d.b) :
    splitNorm D S (forwardJetCoeff d ρ n y t) = 0 := by
  have hρ : (ρ:ℝ) = 0 := le_antisymm (ρ.property.2.trans_eq hb) ρ.property.1
  have ht0 : t = 0 := le_antisymm (ht.2.trans_eq hb) (hρ ▸ ht.1)
  apply le_antisymm _ (splitNorm_nonneg D S _)
  simpa [forwardClock,hρ,ht0] using
    original_data_forward_higher_allProper d hsmall ρ n hn y ht S hS

theorem forward_cut_dimension_zero (d : PositiveVarianceFlowData (Space 0))
    (ρ : Icc (0:ℝ) d.b) (n : ℕ) (y : Space 0) (s : ℝ)
    (S : Finset (Fin n ⊕ Unit)) : splitNorm 0 S (forwardJetCoeff d ρ n y s) = 0 := by
  have hz : forwardJetCoeff d ρ n y s = 0 := by
    ext a
    exact Fin.elim0 (a (.inr ()))
  rw [hz,splitNorm_zero]
end AcceleratedLogConcave.Tensor.ForwardFlow
