import AcceleratedLogConcave.Tensor.MaterialRouteSlots

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open Conditional AdjointReduction CoordinateReduction

private theorem expr_cast_evaluate {D r s : ℕ} (h : r=s) (e : Expr signature r)
    (ρ : CoefficientEnvironment signature D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (y : EuclideanSpace ℝ (Fin D)) (a : Fin s → Fin D) :
    Expr.evaluate ρ H (h ▸ e) y a = Expr.evaluate ρ H e y (a ∘ finCongr h) := by
  cases h
  rfl

private theorem ofFn_get_map {E F : Type*} (l : List E) (g : E → F) :
    List.ofFn (fun i => g (l.get i)) = l.map g := by
  rw [List.ofFn_comp',List.ofFn_get]

/-- Full actual nonlinear material route semantics. The route and all
slot permutations are constructed from positional labels; no operand or
whole-expression equality is assumed. -/
theorem materialJetRouteExpr_evaluate {D q : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (p : List (Fin q) × List (Fin q)) (hp : p ∈ scoreRoutes (List.finRange q))
    (t : ℝ) (y : EuclideanSpace ℝ (Fin D)) (a : Fin (q+1) → Fin D) :
    Expr.evaluate (coefficientEnvironment d.F d.x d.ell d.r t)
      (interpolationPotential d.F d.x d.r t) (materialJetRouteExpr p hp) y a =
    d.normalizedRouteTerm (coordinateDirection D (a 0))
      (p.1.map (fun i => coordinateDirection D (a i.succ)))
      (p.2.map (fun i => coordinateDirection D (a i.succ))) t y := by
  rcases p with ⟨A,B⟩
  cases A with
  | nil => exact False.elim ((scoreRoutes_left_ne_nil (List.finRange q) ([],B) hp) rfl)
  | cons u A =>
    let p : List (Fin q) × List (Fin q) := (u::A,B)
    have hr : p ∈ routes (List.finRange q) := by rw [routes_eq]; exact List.mem_cons_of_mem _ hp
    let raw : Fin (A.length+B.length+2) → Fin D := fun i =>
      a (materialRouteOutputEquiv p hr (Fin.cast (by simp [p]; omega) i))
    have he : A.length+B.length+2=q+1 := by
      have hh := route_length (List.finRange q) p hr
      simp only [p,List.length_cons,List.length_finRange] at hh
      omega
    have hvalue :
        Expr.evaluate (coefficientEnvironment d.F d.x d.ell d.r t)
          (interpolationPotential d.F d.x d.r t) (materialJetRouteExpr p hp) y a =
        Expr.evaluate (coefficientEnvironment d.F d.x d.ell d.r t)
          (interpolationPotential d.F d.x d.r t) (materialJetContractExpr A.length B.length) y raw := by
      dsimp only [materialJetRouteExpr]
      change Expr.evaluate _ _ (he ▸ materialJetContractExpr A.length B.length) y _ = _
      rw [expr_cast_evaluate]
      apply congrArg (fun b : Fin (A.length+B.length+2) → Fin D =>
        Expr.evaluate (coefficientEnvironment d.F d.x d.ell d.r t)
          (interpolationPotential d.F d.x d.r t) (materialJetContractExpr A.length B.length) y b)
      funext i
      rfl
    have hleft (k : Fin D) :
        leftAssignment (0 : Fin (A.length+2)) raw k =
        (show Fin (A.length+2) → Fin D from Fin.cons k
          (fun i => a (((u::A).get i).succ))) := by
      unfold leftAssignment
      rw [Fin.insertNth_zero']
      congr 1
      funext i
      exact congrArg a (materialRouteOutputEquiv_left p hr i)
    have hright (k : Fin D) :
        rightAssignment (1 : Fin (B.length+2)) raw k =
        (show Fin (B.length+2) → Fin D from Fin.cons (a 0)
          (Fin.cons k (fun i => a ((B.get i).succ)))) := by
      have hb : (fun i : Fin (B.length+1) =>
          raw (Fin.cast (by omega) (Fin.natAdd (A.length+1) i))) =
          Fin.cons (a 0) (fun i => a ((B.get i).succ)) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact congrArg a (materialRouteOutputEquiv_output p hr)
        · exact congrArg a (materialRouteOutputEquiv_right p hr j)
      unfold rightAssignment
      rw [hb]
      change (show Fin (B.length+2) → Fin D from
        Fin.insertNth (0 : Fin (B.length+1)).succ k
          (Fin.cons (a 0) (fun i => a ((B.get i).succ)))) = _
      rw [Fin.insertNth_succ_cons,Fin.insertNth_zero']
    rw [hvalue,materialJetContractExpr_evaluate]
    simp_rw [hleft,hright]
    simp only [Fin.cons_zero,Fin.cons_succ]
    have hL : List.ofFn (fun i => coordinateDirection D (a (((u::A).get i).succ))) =
        (u::A).map (fun i => coordinateDirection D (a i.succ)) :=
      ofFn_get_map (u::A) (fun i : Fin q => coordinateDirection D (a i.succ))
    have hR (k : Fin D) :
        List.ofFn (fun i : Fin (B.length+1) =>
          coordinateDirection D ((show Fin (B.length+1) → Fin D from Fin.cons k (fun j => a ((B.get j).succ))) i)) =
        coordinateDirection D k :: B.map (fun i => coordinateDirection D (a i.succ)) := by
      rw [List.ofFn_succ]
      simp only [Fin.cons_zero,Fin.cons_succ]
      rw [ofFn_get_map B (fun i : Fin q => coordinateDirection D (a i.succ))]
    unfold PositiveVarianceFlowData.normalizedRouteTerm
    apply Finset.sum_congr rfl
    intro k _
    exact congrArg₂ (fun x y : ℝ => x*y)
      (congrArg (fun l => d.normalizedJetList (coordinateDirection D k) l (t,y)) hL)
      (congrArg (fun l => d.normalizedJetList (coordinateDirection D (a 0)) l (t,y)) (hR k))

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
