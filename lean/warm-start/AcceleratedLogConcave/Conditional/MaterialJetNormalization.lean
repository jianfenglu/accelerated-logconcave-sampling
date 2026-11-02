import AcceleratedLogConcave.Conditional.MaterialJetIdentity

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff RealInnerProductSpace BigOperators
namespace AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
open Analysis Analysis.CoupledVelocityPolynomial Tensor Tensor.AdjointReduction

private theorem inverse_factorial_succ (L : ℝ) (q : ℕ) :
    (L*(q.factorial:ℝ))⁻¹ = (q+1:ℝ)*(L*((q+1).factorial:ℝ))⁻¹ := by
  rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  by_cases hL : L=0
  · simp [hL]
  · have hq : (q.factorial:ℝ) ≠ 0 := by positivity
    have hq1 : (q+1:ℝ) ≠ 0 := by positivity
    field_simp

private theorem inverse_factorial_product (L x y : ℝ) (q a b : ℕ) :
    (L*(q.factorial:ℝ))⁻¹ * (x*y) =
      L*((a.factorial:ℝ)*(b.factorial:ℝ)/(q.factorial:ℝ)) *
        (((L*(a.factorial:ℝ))⁻¹*x)*((L*(b.factorial:ℝ))⁻¹*y)) := by
  by_cases hL : L=0
  · simp [hL]
  · have hq : (q.factorial:ℝ) ≠ 0 := by positivity
    have ha : (a.factorial:ℝ) ≠ 0 := by positivity
    have hb : (b.factorial:ℝ) ≠ 0 := by positivity
    field_simp

variable {D : ℕ} (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))

/-- Actual factorial-normalized center jet, even when ell=0. -/
def normalizedJetList (w : EuclideanSpace ℝ (Fin D))
    (l : List (EuclideanSpace ℝ (Fin D))) (p : ℝ × EuclideanSpace ℝ (Fin D)) : ℝ :=
  (d.ell*d.r*(l.length.factorial:ℝ))⁻¹ * d.scaledJetList w l p

def normalizedRouteTerm (w : EuclideanSpace ℝ (Fin D))
    (A B : List (EuclideanSpace ℝ (Fin D))) (t : ℝ) (y : EuclideanSpace ℝ (Fin D)) : ℝ :=
  ∑ k : Fin D, d.normalizedJetList (coordinateDirection D k) A (t,y) *
    d.normalizedJetList w (coordinateDirection D k :: B) (t,y)

/-- Exact labeled-subset normalization. Coefficients are kept explicit
rather than replacing a sum by an assumed average. -/
theorem material_normalizedJetList (w : EuclideanSpace ℝ (Fin D))
    (l : List (EuclideanSpace ℝ (Fin D))) {t : ℝ} (ht : -1<t ∧ t<1)
    (y : EuclideanSpace ℝ (Fin D)) :
    materialDerivative d.materialVelocity (d.normalizedJetList w l) (t,y) =
      (l.length+1:ℝ) * ((d.ell*d.r*((l.length+1).factorial:ℝ))⁻¹ *
        d.scaledJetAdjoint l.length w (fun i => l.get i) t y) +
      (2*d.ell*d.r^2*t) * ((scoreRoutes l).map (fun p =>
        ((p.1.length.factorial:ℝ)*((p.2.length+1).factorial:ℝ)/(l.length.factorial:ℝ)) *
          d.normalizedRouteTerm w p.1 p.2 t y)).sum := by
  have hf := ((d.contDiffOn_scaledJetCoordinate l.length w (fun i => l.get i)).contDiffAt
    ((isOpen_openDomain _).mem_nhds (show (t,y) ∈ openDomain _ from ht))).differentiableAt (by simp)
  change DifferentiableAt ℝ (d.scaledJetList w l) (t,y) at hf
  have hd : materialDerivative d.materialVelocity (d.normalizedJetList w l) (t,y) =
      (d.ell*d.r*(l.length.factorial:ℝ))⁻¹ *
        materialDerivative d.materialVelocity (d.scaledJetList w l) (t,y) := by
    unfold normalizedJetList materialDerivative
    rw [fderiv_const_mul hf]
    simp
  rw [hd,d.material_scaledJet_list w l ht y,mul_add]
  have hp := inverse_factorial_succ (d.ell*d.r) l.length
  rw [hp]
  have hroute : (d.ell*d.r*(l.length.factorial:ℝ))⁻¹ * d.materialRouteSum w l t y =
      (d.ell*d.r) * ((scoreRoutes l).map (fun p =>
        ((p.1.length.factorial:ℝ)*((p.2.length+1).factorial:ℝ)/(l.length.factorial:ℝ)) *
          d.normalizedRouteTerm w p.1 p.2 t y)).sum := by
    unfold materialRouteSum
    rw [←List.sum_map_mul_left,←List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p _
    unfold materialRouteTerm normalizedRouteTerm normalizedJetList
    rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simpa only [List.length_cons,mul_assoc] using inverse_factorial_product (d.ell*d.r)
      (d.scaledJetList (coordinateDirection D k) p.1 (t,y))
      (d.scaledJetList w (coordinateDirection D k::p.2) (t,y))
      l.length p.1.length (p.2.length+1)
  rw [hp] at hroute
  calc
    _ = (l.length+1:ℝ) * ((d.ell*d.r*((l.length+1).factorial:ℝ))⁻¹ *
          d.scaledJetAdjoint l.length w (fun i => l.get i) t y) +
        (2*d.r*t) * (((l.length+1:ℝ)*(d.ell*d.r*((l.length+1).factorial:ℝ))⁻¹) *
          d.materialRouteSum w l t y) := by ring
    _ = _ := by rw [hroute]; ring

end AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
