import AcceleratedLogConcave.Tensor.MaterialRouteEvaluation
import AcceleratedLogConcave.Tensor.MaterialRouteMass

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open Conditional Analysis AdjointReduction

private theorem routes_map {L K : Type*} (f : L → K) (l : List L) :
    routes (l.map f) = (routes l).map (fun p => (p.1.map f,p.2.map f)) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.map_cons,routes,ih,List.map_append,List.map_map,Function.comp_def]


private theorem scoreRoutes_map {L K : Type*} (f : L → K) (l : List L) :
    scoreRoutes (l.map f) = (scoreRoutes l).map (fun p => (p.1.map f,p.2.map f)) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.map_cons,scoreRoutes,ih,routes_map,List.map_append,List.map_map,Function.comp_def]


private theorem ofFn_tensor_apply {E F : Type*} (T : ∀ n : ℕ, (Fin n → E) → F)
    {n : ℕ} (v : Fin n → E) :
    T (List.ofFn v).length (fun i => (List.ofFn v).get i) = T n v := by
  have hn : (List.ofFn v).length = n := List.length_ofFn
  generalize he : List.ofFn v = l at hn ⊢
  subst n
  have hv : (fun i => l.get i) = v := by
    apply List.ofFn_injective
    rw [List.ofFn_get,he]
  rw [hv]

/-- Exact one-step material expansion of every actual normalized jet
coefficient into literal canonical Expr values. All positional subset
multiplicities and scalar coefficients are retained, including rho0/ell0. -/
theorem material_coefficient_leaf_expansion {D : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (n : ℕ) {t : ℝ} (ht : -1<t ∧ t<1) (y : EuclideanSpace ℝ (Fin D))
    (a : Fin (n+2) → Fin D) :
    materialDerivative d.materialVelocity
      (fun p => coefficientEnvironment d.F d.x d.ell d.r p.1 (Sum.inl n) p.2 a) (t,y) =
    (n+2:ℝ) * Expr.evaluate (coefficientEnvironment d.F d.x d.ell d.r t)
      (interpolationPotential d.F d.x d.r t) (materialJetPrincipalExpr n) y a +
    (2*d.ell*d.r^2*t) *
      ((scoreRoutes (List.finRange (n+1))).attach.map (fun p =>
        (materialRouteFactorialWeight p.val / ((n+1).factorial:ℝ)) *
          Expr.evaluate (coefficientEnvironment d.F d.x d.ell d.r t)
            (interpolationPotential d.F d.x d.r t) (materialJetRouteExpr p.val p.property) y a)).sum := by
  let v : Fin (n+1) → EuclideanSpace ℝ (Fin D) := fun i => coordinateDirection D (a i.succ)
  let w := coordinateDirection D (a 0)
  have he : (fun p => coefficientEnvironment d.F d.x d.ell d.r p.1 (Sum.inl n) p.2 a) =
      d.normalizedJetList w (List.ofFn v) := by
    funext p
    exact coefficient_eq_normalizedJetList d n p.1 p.2 a
  rw [he,d.material_normalizedJetList w (List.ofFn v) ht y,
    materialJetPrincipalExpr_evaluate d n ht y a]
  have hprincipal := ofFn_tensor_apply (fun q dirs =>
    (q+1:ℝ) * ((d.ell*d.r*((q+1).factorial:ℝ))⁻¹ *
      d.scaledJetAdjoint q w dirs t y)) v
  rw [hprincipal]
  clear he
  have hcast : ((n+1:ℕ):ℝ)+1=(n:ℝ)+2 := by push_cast; ring
  rw [hcast]
  simp_rw [materialJetRouteExpr_evaluate]
  have hatt := List.attach_map_val
    (l := scoreRoutes (List.finRange (n+1)))
    (f := fun p : List (Fin (n+1)) × List (Fin (n+1)) =>
      (materialRouteFactorialWeight p / ((n+1).factorial:ℝ)) *
        d.normalizedRouteTerm w (p.1.map v) (p.2.map v) t y)
  rw [hatt]
  congr 1
  congr 1
  rw [List.ofFn_eq_map,scoreRoutes_map]
  simp only [List.map_map,Function.comp_def,List.length_map,List.length_finRange,
    materialRouteFactorialWeight]

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
