import AcceleratedLogConcave.Tensor.MaterialIteration

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators NNReal
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open Conditional Analysis AdjointReduction

def materialMass {r : ℕ} (ts : List (MaterialTerm r)) : ℝ :=
  (ts.map (fun u => |u.coefficient|)).sum

@[simp] theorem materialMass_mapExpr {r s : ℕ} (ts : List (MaterialTerm r))
    (f : Expr signature r → Expr signature s) :
    materialMass (ts.map (MaterialTerm.mapExpr f)) = materialMass ts := by
  simp [materialMass,MaterialTerm.mapExpr,List.map_map,Function.comp_def]

@[simp] theorem materialMass_append {r : ℕ} (ts us : List (MaterialTerm r)) :
    materialMass (ts++us) = materialMass ts+materialMass us := by simp [materialMass]

theorem materialMass_nonneg {r : ℕ} (ts : List (MaterialTerm r)) : 0 ≤ materialMass ts :=
  List.sum_nonneg (fun u hu => by obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hu; exact abs_nonneg _)

/-- Explicit quadratic coefficient mass for one whole-expression step.
The scale condition is discharged from original data below. -/
theorem materialExpressionStep_mass (l : ℝ) (hl : |l| ≤ 1) {r : ℕ} (e : Expr signature r) :
    materialMass (materialExpressionStep l e) ≤ 2*(e.size:ℝ)^2 := by
  induction e with
  | coefficient c =>
    cases c with
    | inl n =>
      have hh := materialLeafMass_le (List.finRange (n+1)) l hl
      have hn : (0:ℝ) ≤ n+2 := by positivity
      simp only [List.length_finRange,Nat.cast_add,Nat.cast_one] at hh
      simp only [materialExpressionStep,materialMass,List.map_cons,List.sum_cons,List.map_map,
        Function.comp_def,abs_of_nonneg hn]
      have hatt := List.attach_map_val (l := scoreRoutes (List.finRange (n+1)))
        (f := fun p => |2*l*(materialRouteFactorialWeight p / ((n+1).factorial:ℝ))|)
      rw [hatt]
      change (n+2:ℝ) +
        ((scoreRoutes (List.finRange (n+1))).map (fun p =>
          |2*l*(materialRouteFactorialWeight p / ((n+1).factorial:ℝ))|)).sum ≤ 2*((n+2:ℕ):ℝ)^2
      have hc : ((n+2:ℕ):ℝ) = (n:ℝ)+2 := by push_cast; ring
      rw [hc]
      have hh' : (n+2:ℝ) +
          ((scoreRoutes (List.finRange (n+1))).map (fun p =>
            |2*l*(materialRouteFactorialWeight p / ((n+1).factorial:ℝ))|)).sum ≤ (n+2:ℝ)^2 := by
        convert hh using 1 <;> ring
      exact hh'.trans (by nlinarith [sq_nonneg (n+2:ℝ)])
    | inr u => simp [materialExpressionStep,materialMass,Expr.size,signature]
  | permute π e ih => simpa [materialExpressionStep] using ih
  | contract e f i j ihe ihf =>
    simp only [materialExpressionStep,materialMass_append,materialMass_mapExpr,Expr.size,Nat.cast_add,Nat.cast_one]
    have ha : (0:ℝ) ≤ e.size := by positivity
    have hb : (0:ℝ) ≤ f.size := by positivity
    nlinarith [mul_nonneg ha hb]
  | derivative e ih => simp [materialExpressionStep,materialMass]; positivity
  | adjoint i e ih =>
    rw [materialExpressionStep,materialMass_append,materialMass_mapExpr]
    simp only [materialMass,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
      Expr.size,Nat.cast_add,Nat.cast_one]
    have ha : (0:ℝ) ≤ e.size := by positivity
    change (List.map (fun u => |u.coefficient|) (materialExpressionStep l e)).sum ≤ _ at ih
    nlinarith

theorem actual_materialExpressionStep_mass {D r : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (hsmall : d.r^2*d.ell ≤ 1/2) (e : Expr signature r) :
    materialMass (materialExpressionStep (d.ell*d.r^2) e) ≤ 2*(e.size:ℝ)^2 := by
  apply materialExpressionStep_mass
  rw [abs_of_nonneg (mul_nonneg d.hell (sq_nonneg _))]
  nlinarith

@[simp] theorem materialMass_flatMap {r s : ℕ} (ts : List (MaterialTerm r))
    (f : MaterialTerm r → List (MaterialTerm s)) :
    materialMass (ts.flatMap f) = (ts.map (fun u => materialMass (f u))).sum := by
  induction ts with
  | nil => simp [materialMass]
  | cons u ts ih => simp [List.flatMap_cons,ih]

theorem materialTermStep_mass (l : ℝ) {r : ℕ} (u : MaterialTerm r) :
    materialMass (materialTermStep l u) =
      |u.coefficient| * ((u.degree:ℝ)+materialMass (materialExpressionStep l u.expression)) := by
  simp only [materialTermStep,materialMass,List.map_cons,List.sum_cons,List.map_map,Function.comp_def,
    abs_mul,abs_of_nonneg (Nat.cast_nonneg u.degree : (0:ℝ) ≤ u.degree)]
  rw [List.sum_map_mul_left]
  ring

/-- Explicit coefficient budget, retaining source order dependence. -/
def materialMassBudget (s : ℕ) : ℕ → ℝ
  | 0 => 1
  | k+1 => ((k:ℝ)+2*((s+3*k:ℕ):ℝ)^2)*materialMassBudget s k

theorem materialIterate_mass (l : ℝ) (hl : |l| ≤ 1) {r : ℕ} (e : Expr signature r) (k : ℕ) :
    materialMass (materialIterate l e k) ≤ materialMassBudget e.size k := by
  induction k with
  | zero => simp [materialIterate,materialMass,materialMassBudget]
  | succ k ih =>
    let A : ℝ := (k:ℝ)+2*((e.size+3*k:ℕ):ℝ)^2
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hterm (u : MaterialTerm r) (hu : u ∈ materialIterate l e k) :
        materialMass (materialTermStep l u) ≤ A*|u.coefficient| := by
      have hm := materialExpressionStep_mass l hl u.expression
      have hs := materialIterate_size_degree l e k u hu
      have hsz : (u.expression.size:ℝ) ≤ ((e.size+3*k:ℕ):ℝ) := by exact_mod_cast hs.1
      have hdeg : (u.degree:ℝ) ≤ (k:ℝ) := by exact_mod_cast hs.2
      have hnon : (0:ℝ) ≤ u.expression.size := by positivity
      have hbound : (u.degree:ℝ)+materialMass (materialExpressionStep l u.expression) ≤ A := by
        dsimp [A]
        nlinarith [sq_le_sq₀ hnon (by positivity) |>.mpr hsz]
      rw [materialTermStep_mass]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hbound (abs_nonneg u.coefficient)
    rw [materialIterate,materialMass_flatMap]
    calc
      _ ≤ ((materialIterate l e k).map (fun u => A*|u.coefficient|)).sum :=
        List.sum_le_sum hterm
      _ = A*materialMass (materialIterate l e k) := List.sum_map_mul_left _ _ _
      _ ≤ A*materialMassBudget e.size k := mul_le_mul_of_nonneg_left ih hA
      _ = materialMassBudget e.size (k+1) := rfl

theorem materialMassBudget_le (s k : ℕ) :
    materialMassBudget s k ≤ (3*((s:ℝ)+3*(k:ℝ)+1)^2)^k := by
  induction k with
  | zero => simp [materialMassBudget]
  | succ k ih =>
    let A : ℝ := 3*((s:ℝ)+3*(k:ℝ)+1)^2
    let B : ℝ := 3*((s:ℝ)+3*((k+1:ℕ):ℝ)+1)^2
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hAB : A ≤ B := by
      dsimp [A,B]
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) s,Nat.cast_nonneg (α := ℝ) k]
    have hfactor : (k:ℝ)+2*((s+3*k:ℕ):ℝ)^2 ≤ B := by
      dsimp [B]
      push_cast
      nlinarith [sq_nonneg ((s:ℝ)+3*(k:ℝ)),Nat.cast_nonneg (α := ℝ) s,
        Nat.cast_nonneg (α := ℝ) k]
    have hAp : 0 ≤ A^k := pow_nonneg hA _
    rw [materialMassBudget]
    calc
      _ ≤ ((k:ℝ)+2*((s+3*k:ℕ):ℝ)^2)*A^k :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ ≤ B*A^k := mul_le_mul_of_nonneg_right hfactor hAp
      _ ≤ B*B^k := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA hAB k) hB
      _ = B^(k+1) := by rw [pow_succ]; ring

theorem actual_materialIterate_mass {D r : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (hsmall : d.r^2*d.ell ≤ 1/2) (e : Expr signature r) (k : ℕ) :
    materialMass (materialIterate (d.ell*d.r^2) e k) ≤
      (3*((e.size:ℝ)+3*(k:ℝ)+1)^2)^k := by
  have hl : |d.ell*d.r^2| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg d.hell (sq_nonneg _))]
    nlinarith
  exact (materialIterate_mass _ hl e k).trans (materialMassBudget_le e.size k)

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
