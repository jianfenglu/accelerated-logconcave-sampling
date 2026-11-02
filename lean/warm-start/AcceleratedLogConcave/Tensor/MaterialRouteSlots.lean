import AcceleratedLogConcave.Tensor.MaterialJetExpression
import Mathlib.Data.List.NodupEquivFin

noncomputable section
open scoped Classical NNReal
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open AdjointReduction

/-- A single distinguished output followed by ordered input slots. -/
def materialHeadTailEquiv (n : ℕ) : Fin (n+1) ≃ (Unit ⊕ Fin n) where
  toFun := Fin.cases (.inl ()) Sum.inr
  invFun := Sum.elim (fun _ => 0) Fin.succ
  left_inv i := by refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv a := by rcases a with ⟨⟩ | j <;> rfl

/-- Positional route inputs give a genuine bijection, including repeated
physical coordinate values. Only labels, not values, are distinct. -/
def materialRouteInputEquiv {q : ℕ} (p : List (Fin q) × List (Fin q))
    (hp : p ∈ routes (List.finRange q)) :
    (Fin p.1.length ⊕ Fin p.2.length) ≃ Fin q :=
  finSumFinEquiv.trans ((finCongr (show (p.1++p.2).length=p.1.length+p.2.length from List.length_append).symm).trans
    (List.Nodup.getEquivOfForallMemList (p.1++p.2)
      ((route_perm (List.finRange q) p hp).nodup_iff.mpr (List.nodup_finRange q))
      (fun i => (route_perm (List.finRange q) p hp).mem_iff.mpr (List.mem_finRange i))))


theorem materialRouteInputEquiv_left {q : ℕ} (p : List (Fin q) × List (Fin q))
    (hp : p ∈ routes (List.finRange q)) (i : Fin p.1.length) :
    materialRouteInputEquiv p hp (.inl i) = p.1.get i := by
  change (p.1++p.2)[i.val] = p.1[i.val]
  exact List.getElem_append_left i.isLt

theorem materialRouteInputEquiv_right {q : ℕ} (p : List (Fin q) × List (Fin q))
    (hp : p ∈ routes (List.finRange q)) (i : Fin p.2.length) :
    materialRouteInputEquiv p hp (.inr i) = p.2.get i := by
  change (p.1++p.2)[p.1.length+i.val] = p.2[i.val]
  rw [List.getElem_append_right (by omega)]
  simp

/-- Raw contraction outputs list A inputs, then the right output and B
inputs. This equivalence restores the actual output and original input order. -/
def materialRouteOutputEquiv {q : ℕ} (p : List (Fin q) × List (Fin q))
    (hp : p ∈ routes (List.finRange q)) :
    Fin (p.1.length+p.2.length+1) ≃ Fin (q+1) :=
  (finCongr (by omega : p.1.length+p.2.length+1=p.1.length+(p.2.length+1))).trans
    (finSumFinEquiv.symm.trans
      ((Equiv.sumCongr (Equiv.refl _) (materialHeadTailEquiv p.2.length)).trans
        ((Equiv.sumAssoc _ _ _).symm.trans
          ((Equiv.sumCongr (Equiv.sumComm _ _) (Equiv.refl _)).trans
            ((Equiv.sumAssoc _ _ _).trans
              ((Equiv.sumCongr (Equiv.refl _) (materialRouteInputEquiv p hp)).trans
                (materialHeadTailEquiv q).symm))))))


theorem materialRouteOutputEquiv_left {q : ℕ} (p : List (Fin q) × List (Fin q))
    (hp : p ∈ routes (List.finRange q)) (i : Fin p.1.length) :
    materialRouteOutputEquiv p hp
      (Fin.cast (by omega) (Fin.castAdd (p.2.length+1) i)) = (p.1.get i).succ := by
  simp [materialRouteOutputEquiv,materialHeadTailEquiv,materialRouteInputEquiv_left]

theorem materialRouteOutputEquiv_output {q : ℕ} (p : List (Fin q) × List (Fin q))
    (hp : p ∈ routes (List.finRange q)) :
    materialRouteOutputEquiv p hp
      (Fin.cast (by omega) (Fin.natAdd p.1.length (0 : Fin (p.2.length+1)))) = 0 := by
  simp [materialRouteOutputEquiv,materialHeadTailEquiv]

theorem materialRouteOutputEquiv_right {q : ℕ} (p : List (Fin q) × List (Fin q))
    (hp : p ∈ routes (List.finRange q)) (i : Fin p.2.length) :
    materialRouteOutputEquiv p hp
      (Fin.cast (by omega) (Fin.natAdd p.1.length i.succ)) = (p.2.get i).succ := by
  simp [materialRouteOutputEquiv,materialHeadTailEquiv,materialRouteInputEquiv_right]

/-- The route actually occurs with nonempty left operand, so both child
jets satisfy the restricted grammar's arity-at-least-two condition. -/
def materialJetRouteExpr {q : ℕ} (p : List (Fin q) × List (Fin q))
    (hp : p ∈ scoreRoutes (List.finRange q)) : Expr signature (q+1) := by
  have ha : 1 ≤ p.1.length := List.length_pos_iff.mpr
    (scoreRoutes_left_ne_nil (List.finRange q) p hp)
  have hr : p ∈ routes (List.finRange q) := by rw [routes_eq]; exact List.mem_cons_of_mem _ hp
  have hlen := route_length (List.finRange q) p hr
  simp only [List.length_finRange] at hlen
  have he : (p.1.length-1)+p.2.length+2=q+1 := by omega
  let raw := materialJetContractExpr (p.1.length-1) p.2.length
  let perm : Equiv.Perm (Fin (q+1)) :=
    (finCongr (by omega : q+1=p.1.length+p.2.length+1)).trans
      (materialRouteOutputEquiv p hr)
  exact .permute perm (he ▸ raw)

private theorem expr_cast_size {r s : ℕ} (h : r=s) (e : Expr signature r) :
    (h ▸ e).size = e.size := by cases h; rfl

private theorem expr_cast_weight {r s : ℕ} (h : r=s) (e : Expr signature r) :
    (h ▸ e).weight = e.weight := by cases h; rfl

theorem materialJetRouteExpr_size {q : ℕ} (p : List (Fin q) × List (Fin q))
    (hp : p ∈ scoreRoutes (List.finRange q)) :
    (materialJetRouteExpr p hp).size = q+4 := by
  have ha : 1 ≤ p.1.length := List.length_pos_iff.mpr
    (scoreRoutes_left_ne_nil (List.finRange q) p hp)
  have hr : p ∈ routes (List.finRange q) := by rw [routes_eq]; exact List.mem_cons_of_mem _ hp
  have hlen := route_length (List.finRange q) p hr
  simp only [List.length_finRange] at hlen
  dsimp only [materialJetRouteExpr]
  rw [Expr.permute_size,expr_cast_size,materialJetContractExpr_size]
  omega

theorem materialJetRouteExpr_weight {q : ℕ} (p : List (Fin q) × List (Fin q))
    (hp : p ∈ scoreRoutes (List.finRange q)) :
    (materialJetRouteExpr p hp).weight = ((q-1 : ℕ) : ℝ≥0) := by
  have ha : 1 ≤ p.1.length := List.length_pos_iff.mpr
    (scoreRoutes_left_ne_nil (List.finRange q) p hp)
  have hr : p ∈ routes (List.finRange q) := by rw [routes_eq]; exact List.mem_cons_of_mem _ hp
  have hlen := route_length (List.finRange q) p hr
  simp only [List.length_finRange] at hlen
  dsimp only [materialJetRouteExpr]
  rw [Expr.permute_weight,expr_cast_weight,materialJetContractExpr_weight]
  have hn : p.1.length-1+p.2.length=q-1 := by omega
  exact_mod_cast hn

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
