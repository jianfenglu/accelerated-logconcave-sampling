import AcceleratedLogConcave.Tensor.MaterialJetExpression

noncomputable section
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open AdjointReduction

/-- Unnormalized factorial weight of one positional material route. -/
def materialRouteFactorialWeight {L : Type*} (p : List L × List L) : ℝ :=
  (p.1.length.factorial:ℝ) * ((p.2.length+1).factorial:ℝ)

private theorem material_all_routes_mass {L : Type*} (l : List L) :
    2 * ((routes l).map materialRouteFactorialWeight).sum =
      ((l.length+2).factorial:ℝ) := by
  induction l with
  | nil => norm_num [routes,materialRouteFactorialWeight]
  | cons i l ih =>
    have hterm (p : List L × List L) (hp : p ∈ routes l) :
        materialRouteFactorialWeight (p.1,i::p.2) +
          materialRouteFactorialWeight (i::p.1,p.2) =
        (l.length+3:ℝ) * materialRouteFactorialWeight p := by
      have hlen := route_length l p hp
      have hcast : (p.1.length:ℝ)+(p.2.length:ℝ)=(l.length:ℝ) := by exact_mod_cast hlen
      simp only [materialRouteFactorialWeight,List.length_cons,Nat.factorial_succ,
        Nat.cast_mul,Nat.cast_add,Nat.cast_one]
      rw [←hcast]
      ring
    have hsum :
        ((routes l).map (fun p => materialRouteFactorialWeight (p.1,i::p.2))).sum +
          ((routes l).map (fun p => materialRouteFactorialWeight (i::p.1,p.2))).sum =
        (l.length+3:ℝ) * ((routes l).map materialRouteFactorialWeight).sum := by
      rw [←List.sum_map_add,←List.sum_map_mul_left]
      apply congrArg List.sum
      exact List.map_congr_left hterm
    simp only [routes,List.map_append,List.sum_append,List.map_map,Function.comp_def]
    rw [hsum]
    simp only [List.length_cons]
    calc
      _ = (l.length+3:ℝ) * (2*((routes l).map materialRouteFactorialWeight).sum) := by ring
      _ = _ := by rw [ih,Nat.factorial_succ (l.length+2)]; push_cast; ring

/-- Exact total mass of all nonempty positional subsets. This is the
source's grouped-average count, proved without assuming an averaging certificate. -/
theorem materialRouteMass_exact {L : Type*} (l : List L) :
    ((scoreRoutes l).map (fun p => materialRouteFactorialWeight p / (l.length.factorial:ℝ))).sum =
      (l.length:ℝ)*(l.length+1)/2 := by
  have hh := material_all_routes_mass l
  rw [routes_eq] at hh
  simp only [List.map_cons,List.sum_cons,materialRouteFactorialWeight,
    List.length_nil,Nat.factorial_zero,Nat.cast_one,one_mul] at hh
  simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one] at hh
  have hfactor : (l.length.factorial:ℝ) ≠ 0 := by positivity
  simp only [div_eq_mul_inv]
  rw [List.sum_map_mul_right]
  field_simp
  nlinarith [hh]

/-- One normalized material leaf has at most (q+1)^2 total coefficient
mass when the physical scalar has absolute value at most one. -/
theorem materialLeafMass_le {L : Type*} (l : List L) (a : ℝ) (ha : |a| ≤ 1) :
    (l.length+1:ℝ) +
      ((scoreRoutes l).map (fun p => |2*a*(materialRouteFactorialWeight p / (l.length.factorial:ℝ))|)).sum ≤
      (l.length+1:ℝ)^2 := by
  have hp (p : List L × List L) : 0 ≤ materialRouteFactorialWeight p / (l.length.factorial:ℝ) := by
    unfold materialRouteFactorialWeight
    positivity
  simp_rw [abs_mul,abs_of_nonneg (hp _)]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)]
  rw [List.sum_map_mul_left,materialRouteMass_exact]
  have hq : (0:ℝ) ≤ l.length := by positivity
  have hb := mul_le_mul_of_nonneg_right ha (mul_nonneg hq (show (0:ℝ) ≤ l.length+1 by positivity))
  nlinarith

/-- Discharge the physical scalar bound from the original small-step
condition already used by the actual coefficient budgets. -/
theorem actualMaterialLeafMass_le {D L : Type*} [Fintype D] [DecidableEq D]
    (d : Conditional.PositiveVarianceFlowData (EuclideanSpace ℝ D))
    (hsmall : d.r^2*d.ell ≤ 1/2) (l : List L) {t : ℝ} (ht : -1<t ∧ t<1) :
    (l.length+1:ℝ) +
      ((scoreRoutes l).map (fun p =>
        |2*d.ell*d.r^2*t*(materialRouteFactorialWeight p / (l.length.factorial:ℝ))|)).sum ≤
      (l.length+1:ℝ)^2 := by
  have hpos : 0 ≤ d.ell*d.r^2 := mul_nonneg d.hell (sq_nonneg _)
  have habs : |d.ell*d.r^2*t| ≤ 1 := by
    rw [abs_mul,abs_of_nonneg hpos]
    have ht' : |t| ≤ 1 := abs_le.mpr ⟨ht.1.le,ht.2.le⟩
    calc
      _ ≤ (d.ell*d.r^2)*1 := mul_le_mul_of_nonneg_left ht' hpos
      _ ≤ 1 := by nlinarith [hsmall]
  simpa only [mul_assoc] using materialLeafMass_le l (d.ell*d.r^2*t) habs

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
