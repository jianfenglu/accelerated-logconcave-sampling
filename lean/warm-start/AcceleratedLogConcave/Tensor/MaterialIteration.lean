import AcceleratedLogConcave.Tensor.MaterialTermDerivative

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff BigOperators NNReal
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open Conditional Analysis Analysis.CoupledVelocityPolynomial

theorem materialTermStep_isMaterial (l : ℝ) {r : ℕ} (u : MaterialTerm r)
    (hu : IsMaterialExpression u.expression) :
    ∀ v ∈ materialTermStep l u, IsMaterialExpression v.expression := by
  intro v hv
  simp only [materialTermStep,List.mem_cons,List.mem_map] at hv
  rcases hv with rfl | ⟨w,hw,rfl⟩
  · exact hu
  · exact materialExpressionStep_isMaterial l u.expression hu w hw

theorem materialIterate_isMaterial (l : ℝ) {r : ℕ} (e : Expr signature r)
    (he : IsMaterialExpression e) (k : ℕ) :
    ∀ u ∈ materialIterate l e k, IsMaterialExpression u.expression := by
  induction k with
  | zero =>
    intro u hu
    have hh := List.mem_singleton.mp hu
    subst u
    exact he
  | succ k ih =>
    intro u hu
    obtain ⟨v,hv,hu⟩ := List.mem_flatMap.mp hu
    exact materialTermStep_isMaterial l v (ih v hv) u hu

theorem contDiffOn_materialTermValue {D r : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (u : MaterialTerm r) (hu : IsMaterialExpression u.expression) (a : Fin r → Fin D) :
    ContDiffOn ℝ ∞ (u.value d a) (openDomain (EuclideanSpace ℝ (Fin D))) :=
  (contDiffOn_const.mul (contDiff_fst.contDiffOn.pow u.degree)).mul
    (contDiffOn_materialExpressionValue d u.expression hu a)

def materialTermsValue {D r : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (ts : List (MaterialTerm r)) (a : Fin r → Fin D)
    (p : ℝ × EuclideanSpace ℝ (Fin D)) : ℝ := (ts.map (fun u => u.value d a p)).sum

theorem contDiffOn_materialTermsValue {D r : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (ts : List (MaterialTerm r)) (h : ∀ u ∈ ts, IsMaterialExpression u.expression)
    (a : Fin r → Fin D) :
    ContDiffOn ℝ ∞ (materialTermsValue d ts a) (openDomain (EuclideanSpace ℝ (Fin D))) := by
  induction ts with
  | nil => exact contDiffOn_const
  | cons u ts ih =>
    exact (contDiffOn_materialTermValue d u (h u (by simp)) a).add
      (ih (fun v hv => h v (by simp [hv])))

theorem materialDerivative_terms {D r : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (ts : List (MaterialTerm r)) (h : ∀ u ∈ ts, IsMaterialExpression u.expression)
    (a : Fin r → Fin D) {t : ℝ} (ht : -1<t ∧ t<1)
    (y : EuclideanSpace ℝ (Fin D)) :
    materialDerivative d.materialVelocity (materialTermsValue d ts a) (t,y) =
      materialTermsValue d (ts.flatMap (materialTermStep (d.ell*d.r^2))) a (t,y) := by
  induction ts with
  | nil =>
    change fderiv ℝ (fun _ : ℝ × EuclideanSpace ℝ (Fin D) => (0:ℝ)) (t,y)
      (d.materialVelocity (t,y)) = 0
    simp
  | cons u ts ih =>
    have hu := h u (by simp)
    have hs : ∀ v ∈ ts, IsMaterialExpression v.expression := fun v hv => h v (by simp [hv])
    have hdu := ((contDiffOn_materialTermValue d u hu a).contDiffAt
      ((isOpen_openDomain _).mem_nhds (show (t,y) ∈ openDomain _ from ht))).differentiableAt (by simp)
    have hds := ((contDiffOn_materialTermsValue d ts hs a).contDiffAt
      ((isOpen_openDomain _).mem_nhds (show (t,y) ∈ openDomain _ from ht))).differentiableAt (by simp)
    change fderiv ℝ (fun p => u.value d a p + materialTermsValue d ts a p) (t,y)
      (d.materialVelocity (t,y)) = _
    rw [fderiv_fun_add hdu hds]
    change materialDerivative d.materialVelocity (u.value d a) (t,y) +
      materialDerivative d.materialVelocity (materialTermsValue d ts a) (t,y) = _
    rw [materialTermStep_evaluate d u hu a ht y,ih hs]
    simp [materialTermsValue,List.flatMap_cons]

theorem materialIterate_zero_value {D r : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D))) (e : Expr signature r)
    (a : Fin r → Fin D) (p : ℝ × EuclideanSpace ℝ (Fin D)) :
    materialTermsValue d (materialIterate (d.ell*d.r^2) e 0) a p =
      materialExpressionValue d e a p := by
  simp [materialTermsValue,materialIterate,MaterialTerm.value]

/-- The actual all-order finite material-derivative ladder. Together with
its base this identifies the recursive monomial expansion without a new
regularity or derivative-certificate assumption. -/
theorem materialIterate_derivative {D r : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D))) (e : Expr signature r)
    (he : IsMaterialExpression e) (k : ℕ) (a : Fin r → Fin D)
    {t : ℝ} (ht : -1<t ∧ t<1) (y : EuclideanSpace ℝ (Fin D)) :
    materialDerivative d.materialVelocity
      (materialTermsValue d (materialIterate (d.ell*d.r^2) e k) a) (t,y) =
      materialTermsValue d (materialIterate (d.ell*d.r^2) e (k+1)) a (t,y) :=
  materialDerivative_terms d _ (materialIterate_isMaterial _ e he k) a ht y

theorem materialIterate_size_degree (l : ℝ) {r : ℕ} (e : Expr signature r) (k : ℕ) :
    ∀ u ∈ materialIterate l e k, u.expression.size ≤ e.size+3*k ∧ u.degree ≤ k := by
  induction k with
  | zero =>
    intro u hu
    have hh := List.mem_singleton.mp hu
    subst u
    simp
  | succ k ih =>
    intro u hu
    obtain ⟨v,hv,hu⟩ := List.mem_flatMap.mp hu
    have hv' := ih v hv
    simp only [materialTermStep,List.mem_cons,List.mem_map] at hu
    rcases hu with rfl | ⟨w,hw,rfl⟩
    · constructor <;> dsimp <;> omega
    · have hsz := materialExpressionStep_size l v.expression w hw
      have hdeg := materialExpressionStep_degree l v.expression w hw
      constructor <;> dsimp <;> omega

theorem materialIterate_weight (l : ℝ) {r : ℕ} (e : Expr signature r) (k : ℕ) :
    ∀ u ∈ materialIterate l e k, u.expression.weight ≤ e.weight+2*(k:ℝ≥0) := by
  induction k with
  | zero =>
    intro u hu
    have hh := List.mem_singleton.mp hu
    subst u
    simp
  | succ k ih =>
    intro u hu
    obtain ⟨v,hv,hu⟩ := List.mem_flatMap.mp hu
    have hv' := ih v hv
    simp only [materialTermStep,List.mem_cons,List.mem_map] at hu
    rcases hu with rfl | ⟨w,hw,rfl⟩
    · dsimp
      calc
        _ ≤ e.weight+2*(k:ℝ≥0) := hv'
        _ ≤ (e.weight+2*(k:ℝ≥0))+2 := le_add_of_nonneg_right (by positivity)
        _ = e.weight+2*((k+1:ℕ):ℝ≥0) := by push_cast; ring
    · have hw' := materialExpressionStep_weight l v.expression w hw
      dsimp
      calc
        _ ≤ v.expression.weight+2 := hw'
        _ ≤ (e.weight+2*(k:ℝ≥0))+2 := add_le_add hv' (le_refl 2)
        _ = e.weight+2*((k+1:ℕ):ℝ≥0) := by push_cast; ring

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
