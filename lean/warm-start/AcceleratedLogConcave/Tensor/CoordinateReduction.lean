import AcceleratedLogConcave.Tensor.AdjointReduction

/-!
# Literal coordinate identities for the local reduction rules

The established expression evaluator is used throughout. All Leibniz and score
branches are retained with their positional multiplicity. Physical coordinates
supply new derivative directions; global graph compilation remains separate.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff

namespace AcceleratedLogConcave.Tensor.CoordinateReduction
open AdjointReduction

variable {Name : Type*} {σ : CoefficientSignature Name} {D : ℕ}

/-- An actual coordinate scalar field of the established tensor evaluator. -/
def sectionValue (ρ : CoefficientEnvironment σ D)
    (H : EuclideanSpace ℝ (Fin D) → ℝ) {r : ℕ} (e : Expr σ r)
    (a : Fin r → Fin D) : EuclideanSpace ℝ (Fin D) → ℝ :=
  fun x => Expr.evaluate ρ H e x a

/-- The left insertion is exactly the assignment in `crossContract`. -/
def leftAssignment {r s : ℕ} (i : Fin (r+2))
    (a : Fin (r+s+2) → Fin D) (k : Fin D) : Fin (r+2) → Fin D :=
  Fin.insertNth i k (fun t : Fin (r+1) =>
    a (Fin.cast (by omega : (r+1)+(s+1) = r+s+2) (Fin.castAdd (s+1) t)))

/-- The right insertion uses the complementary original output slots. -/
def rightAssignment {r s : ℕ} (i : Fin (s+2))
    (a : Fin (r+s+2) → Fin D) (k : Fin D) : Fin (s+2) → Fin D :=
  Fin.insertNth i k (fun t : Fin (s+1) =>
    a (Fin.cast (by omega : (r+1)+(s+1) = r+s+2) (Fin.natAdd (r+1) t)))

theorem section_permute (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    {r : ℕ} (p : Equiv.Perm (Fin r)) (e : Expr σ r) (a : Fin r → Fin D) :
    sectionValue ρ H (.permute p e) a = sectionValue ρ H e (a ∘ p) := rfl

theorem section_contract (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    {r s : ℕ} (e : Expr σ (r+2)) (f : Expr σ (s+2)) (i : Fin (r+2)) (j : Fin (s+2))
    (a : Fin (r+s+2) → Fin D) :
    sectionValue ρ H (.contract e f i j) a = fun x => ∑ k : Fin D,
      sectionValue ρ H e (leftAssignment i a k) x *
        sectionValue ρ H f (rightAssignment j a k) x := rfl

theorem section_derivative (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    {r : ℕ} (e : Expr σ r) (a : Fin (r+1) → Fin D) :
    sectionValue ρ H (.derivative e) a =
      dir (coordinateDirection D (a (Fin.last r))) (sectionValue ρ H e (a ∘ Fin.castSucc)) := rfl

theorem section_adjoint (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    {r : ℕ} (e : Expr σ (r+2)) (i : Fin (r+2)) (a : Fin (r+1) → Fin D) :
    sectionValue ρ H (.adjoint i e) a =
      adjointField H (coordinateDirection D) (fun k => sectionValue ρ H e (Fin.insertNth i k a)) := rfl

/-- Smooth coefficients and potential give actual smooth evaluated expressions. -/
theorem contDiff_section (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (hρ : ∀ c a, ContDiff ℝ ∞ (fun x => ρ c x a)) (hH : ContDiff ℝ ∞ H)
    {r : ℕ} (e : Expr σ r) : ∀ a : Fin r → Fin D, ContDiff ℝ ∞ (sectionValue ρ H e a) := by
  induction e with
  | coefficient c => intro a; exact hρ c a
  | permute p e ih => intro a; rw [section_permute]; exact ih _
  | contract e f i j ihe ihf =>
    intro a
    rw [section_contract]
    exact ContDiff.sum (fun k _ => (ihe _).mul (ihf _))
  | derivative e ih => intro a; rw [section_derivative]; exact contDiff_dir (ih _) _
  | adjoint i e ih =>
    intro a
    rw [section_adjoint]
    unfold adjointField
    apply ContDiff.sum
    intro k _
    exact (contDiff_dir (ih _) _).neg.add ((contDiff_dir hH _).mul (ih _))

/-- Appending labels is literal composition in the stated order. -/
theorem partialAlong_append {E L : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : L → E) (A B : List L) (f : E → ℝ) :
    partialAlong d (A ++ B) f = partialAlong d A (partialAlong d B f) := by
  induction A with
  | nil => rfl
  | cons i A ih => simp only [List.cons_append, partialAlong, ih]

/-- Permutation changes only the literal free-slot assignment. -/
theorem decorated_permute {L : Type*} (d : L → EuclideanSpace ℝ (Fin D)) (J : List L)
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    {r : ℕ} (p : Equiv.Perm (Fin r)) (e : Expr σ r) (a : Fin r → Fin D) :
    partialAlong d J (sectionValue ρ H (.permute p e) a) =
      partialAlong d J (sectionValue ρ H e (a ∘ p)) := rfl

/-- A derivative node supplies exactly its last physical coordinate, innermost. -/
theorem decorated_derivative (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    {r : ℕ} (e : Expr σ r) (a : Fin (r+1) → Fin D) (J : List (Fin D)) :
    partialAlong (coordinateDirection D) J (sectionValue ρ H (.derivative e) a) =
      partialAlong (coordinateDirection D) (J ++ [a (Fin.last r)])
        (sectionValue ρ H e (a ∘ Fin.castSucc)) := by
  rw [section_derivative, partialAlong_append]
  rfl

/-- The complete coordinate Leibniz expansion, rather than one chosen route. -/
theorem decorated_contract {L : Type*} (d : L → EuclideanSpace ℝ (Fin D)) (J : List L)
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (hρ : ∀ c a, ContDiff ℝ ∞ (fun x => ρ c x a)) (hH : ContDiff ℝ ∞ H)
    {r s : ℕ} (e : Expr σ (r+2)) (f : Expr σ (s+2)) (i : Fin (r+2)) (j : Fin (s+2))
    (a : Fin (r+s+2) → Fin D) :
    partialAlong d J (sectionValue ρ H (.contract e f i j) a) = fun x =>
      ∑ k : Fin D, ((routes J).map (fun p =>
        partialAlong d p.1 (sectionValue ρ H e (leftAssignment i a k)) x *
        partialAlong d p.2 (sectionValue ρ H f (rightAssignment j a k)) x)).sum := by
  rw [section_contract, partialAlong_sum d J Finset.univ _
    (fun k _ => (contDiff_section ρ H hρ hH e _).mul (contDiff_section ρ H hρ hH f _))]
  simp_rw [partialAlong_mul d J (contDiff_section ρ H hρ hH e _)
    (contDiff_section ρ H hρ hH f _)]


/-- The literal adjoint evaluator has every principal and nonempty score branch. -/
theorem decorated_evaluate_adjoint {L : Type*} (d : L → EuclideanSpace ℝ (Fin D)) (J : List L)
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (hρ : ∀ c a, ContDiff ℝ ∞ (fun x => ρ c x a)) (hH : ContDiff ℝ ∞ H)
    {r : ℕ} (e : Expr σ (r+2)) (i : Fin (r+2)) (a : Fin (r+1) → Fin D) :
    partialAlong d J (sectionValue ρ H (.adjoint i e) a) = fun x =>
      adjointField H (coordinateDirection D)
        (fun k => partialAlong d J (sectionValue ρ H e (Fin.insertNth i k a))) x +
      ∑ k : Fin D, ((scoreRoutes J).map (fun p =>
        partialAlong d p.1 (dir (coordinateDirection D k) H) x *
          partialAlong d p.2 (sectionValue ρ H e (Fin.insertNth i k a)) x)).sum := by
  rw [section_adjoint]
  exact decorated_adjointField d J hH _ _ (fun k => contDiff_section ρ H hρ hH e _)

private theorem sum_list_mul_right {A : Type*} (l : List A) (F : A → ℝ) (b : ℝ) :
    (l.map F).sum * b = (l.map (fun a => F a * b)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, add_mul, ih]

private theorem integrable_list_sum {X A : Type*} [MeasurableSpace X]
    (ν : Measure X) (l : List A) (F : A → X → ℝ)
    (hF : ∀ a ∈ l, Integrable (F a) ν) :
    Integrable (fun x => (l.map (fun a => F a x)).sum) ν := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simpa using (hF a (by simp)).fun_add (ih (fun b hb => hF b (by simp [hb])))

private theorem integral_list_sum {X A : Type*} [MeasurableSpace X]
    (ν : Measure X) (l : List A) (F : A → X → ℝ)
    (hF : ∀ a ∈ l, Integrable (F a) ν) :
    (∫ x, (l.map (fun a => F a x)).sum ∂ν) = (l.map (fun a => ∫ x, F a x ∂ν)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [integral_add (hF a (by simp))
      (integrable_list_sum ν l F (fun b hb => hF b (by simp [hb]))),
      ih (fun b hb => hF b (by simp [hb]))]

section ProductExpansion
variable {E L K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [Fintype K] [DecidableEq K]

/-- Only actual product integrability is packaged here. No integration identity,
commutation rule, quadrature estimate or evaluation certificate is a field. -/
structure ProductIntegrability (ν : Measure E) (d : L → E) (J : List L)
    (H f : E → ℝ) (v : E) (g : K → E → ℝ) : Prop where
  product : Integrable (fun x => partialAlong d J f x * ∏ q, g q x) ν
  score : Integrable (fun x => dir v H x * partialAlong d J f x * ∏ q, g q x) ν
  divergence : Integrable (fun x => dir v (partialAlong d J f) x * ∏ q, g q x) ν
  recipients : ∀ q, Integrable (fun x => partialAlong d J f x * dir v (g q) x *
    ∏ s ∈ Finset.univ.erase q, g s x) ν
  commutators : ∀ p ∈ scoreRoutes J, Integrable (fun x =>
    partialAlong d p.1 (dir v H) x * partialAlong d p.2 f x * ∏ q, g q x) ν

omit [MeasurableSpace E] [DecidableEq K] in
/-- Every pointwise score route survives multiplication by the other occurrences. -/
theorem decorated_adjoint_mul_prod (d : L → E) (J : List L) {H f : E → ℝ}
    (hH : ContDiff ℝ ∞ H) (hf : ContDiff ℝ ∞ f) (v : E) (g : K → E → ℝ) :
    (fun x => partialAlong d J (adjointComponent H v f) x * ∏ q, g q x) = fun x =>
      adjointComponent H v (partialAlong d J f) x * ∏ q, g q x +
      ((scoreRoutes J).map (fun p =>
        partialAlong d p.1 (dir v H) x * partialAlong d p.2 f x * ∏ q, g q x)).sum := by
  funext x
  rw [congrFun (decorated_adjoint d J hH hf v) x, add_mul, sum_list_mul_right]

/-- The integrability of the complete decorated adjoint product is derived. -/
theorem integrable_decorated_adjoint_mul_prod (ν : Measure E) (d : L → E) (J : List L)
    {H f : E → ℝ} (hH : ContDiff ℝ ∞ H) (hf : ContDiff ℝ ∞ f) (v : E) (g : K → E → ℝ)
    (hi : ProductIntegrability ν d J H f v g) :
    Integrable (fun x => partialAlong d J (adjointComponent H v f) x * ∏ q, g q x) ν := by
  rw [decorated_adjoint_mul_prod d J hH hf v g]
  have hp : Integrable (fun x => adjointComponent H v (partialAlong d J f) x * ∏ q, g q x) ν := by
    simpa only [adjointComponent, add_mul, neg_mul] using hi.divergence.fun_neg.fun_add hi.score
  exact hp.add (integrable_list_sum ν (scoreRoutes J) _ hi.commutators)

variable [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- One complete integral reduction retains all recipient and score branches. -/
theorem integral_decorated_adjoint_mul_prod (d : L → E) (J : List L) {H f : E → ℝ}
    (hH : ContDiff ℝ ∞ H) (hf : ContDiff ℝ ∞ f) (v : E) (g : K → E → ℝ)
    (hg : ∀ q, Differentiable ℝ (g q)) (hZ : Integrable (fun x => Real.exp (-H x)) μ)
    (hi : ProductIntegrability (μ.tilted (fun x => -H x)) d J H f v g) :
    (∫ x, partialAlong d J (adjointComponent H v f) x * ∏ q, g q x ∂μ.tilted (fun x => -H x)) =
      (∑ q, ∫ x, partialAlong d J f x * dir v (g q) x *
        ∏ s ∈ Finset.univ.erase q, g s x ∂μ.tilted (fun x => -H x)) +
      ((scoreRoutes J).map (fun p => ∫ x,
        partialAlong d p.1 (dir v H) x * partialAlong d p.2 f x * ∏ q, g q x
          ∂μ.tilted (fun x => -H x))).sum := by
  rw [decorated_adjoint_mul_prod d J hH hf v g]
  have hp : Integrable (fun x => adjointComponent H v (partialAlong d J f) x * ∏ q, g q x)
      (μ.tilted (fun x => -H x)) := by
    simpa only [adjointComponent, add_mul, neg_mul] using hi.divergence.fun_neg.fun_add hi.score
  rw [integral_add hp (integrable_list_sum _ (scoreRoutes J) _ hi.commutators),
    integral_adjoint_mul_prod g v (hH.differentiable (by simp))
      ((contDiff_partialAlong d J hf).differentiable (by simp)) hg hZ
      hi.product hi.score hi.divergence hi.recipients,
    integral_list_sum _ (scoreRoutes J) _ hi.commutators]

end ProductExpansion

section FieldExpansion
variable {E L K C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype K] [DecidableEq K] [Fintype C]

omit [DecidableEq K] in
/-- The complete coordinate field is a sum of the actual scalar components. -/
theorem decorated_field_mul_prod (d : L → E) (J : List L) {H : E → ℝ}
    (hH : ContDiff ℝ ∞ H) (v : C → E) (f : C → E → ℝ)
    (hf : ∀ k, ContDiff ℝ ∞ (f k)) (g : K → E → ℝ) :
    (fun x => partialAlong d J (adjointField H v f) x * ∏ q, g q x) = fun x =>
      ∑ k, partialAlong d J (adjointComponent H (v k) (f k)) x * ∏ q, g q x := by
  unfold adjointField
  rw [partialAlong_sum d J Finset.univ (fun k => adjointComponent H (v k) (f k)) (fun k _ =>
    (contDiff_dir (hf k) (v k)).neg.add ((contDiff_dir hH (v k)).mul (hf k)))]
  funext x
  exact Finset.sum_mul _ _ _

variable [MeasurableSpace E]

/-- Integrability is proved for the complete field, not imposed on its value. -/
theorem integrable_decorated_field_mul_prod (ν : Measure E) (d : L → E) (J : List L)
    {H : E → ℝ} (hH : ContDiff ℝ ∞ H) (v : C → E) (f : C → E → ℝ)
    (hf : ∀ k, ContDiff ℝ ∞ (f k)) (g : K → E → ℝ)
    (hi : ∀ k, ProductIntegrability ν d J H (f k) (v k) g) :
    Integrable (fun x => partialAlong d J (adjointField H v f) x * ∏ q, g q x) ν := by
  rw [decorated_field_mul_prod d J hH v f hf g]
  exact integrable_finsetSum _ (fun k _ =>
    integrable_decorated_adjoint_mul_prod ν d J hH (hf k) (v k) g (hi k))

variable [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- No coordinate, recipient occurrence or score route is selected or discarded. -/
theorem integral_decorated_field_mul_prod (d : L → E) (J : List L) {H : E → ℝ}
    (hH : ContDiff ℝ ∞ H) (v : C → E) (f : C → E → ℝ)
    (hf : ∀ k, ContDiff ℝ ∞ (f k)) (g : K → E → ℝ)
    (hg : ∀ q, Differentiable ℝ (g q)) (hZ : Integrable (fun x => Real.exp (-H x)) μ)
    (hi : ∀ k, ProductIntegrability (μ.tilted (fun x => -H x)) d J H (f k) (v k) g) :
    (∫ x, partialAlong d J (adjointField H v f) x * ∏ q, g q x ∂μ.tilted (fun x => -H x)) =
      (∑ k, ∑ q, ∫ x, partialAlong d J (f k) x * dir (v k) (g q) x *
        ∏ s ∈ Finset.univ.erase q, g s x ∂μ.tilted (fun x => -H x)) +
      ∑ k, ((scoreRoutes J).map (fun p => ∫ x,
        partialAlong d p.1 (dir (v k) H) x * partialAlong d p.2 (f k) x * ∏ q, g q x
          ∂μ.tilted (fun x => -H x))).sum := by
  rw [decorated_field_mul_prod d J hH v f hf g,
    integral_finsetSum _ (fun k _ =>
      integrable_decorated_adjoint_mul_prod _ d J hH (hf k) (v k) g (hi k))]
  simp_rw [integral_decorated_adjoint_mul_prod d J hH (hf _) (v _) g hg hZ (hi _)]
  exact Finset.sum_add_distrib

end FieldExpansion

section EvaluatorIntegral
variable {L K : Type*} [Fintype K] [DecidableEq K]

/-- The literal adjoint expression has integrable decorated coordinate products. -/
theorem integrable_decorated_evaluate_adjoint
    (ν : Measure (EuclideanSpace ℝ (Fin D))) (d : L → EuclideanSpace ℝ (Fin D)) (J : List L)
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (hρ : ∀ c a, ContDiff ℝ ∞ (fun x => ρ c x a)) (hH : ContDiff ℝ ∞ H)
    {r : ℕ} (e : Expr σ (r+2)) (i : Fin (r+2)) (a : Fin (r+1) → Fin D)
    (g : K → EuclideanSpace ℝ (Fin D) → ℝ)
    (hi : ∀ k : Fin D, ProductIntegrability ν d J H
      (sectionValue ρ H e (Fin.insertNth i k a)) (coordinateDirection D k) g) :
    Integrable (fun x => partialAlong d J (fun x => Expr.evaluate ρ H (.adjoint i e) x a) x *
      ∏ q, g q x) ν := by
  exact integrable_decorated_field_mul_prod ν d J hH (coordinateDirection D)
    (fun k => sectionValue ρ H e (Fin.insertNth i k a))
    (fun k => contDiff_section ρ H hρ hH e _) g hi

/-- Complete one-step reduction of the actual adjoint coordinate evaluator under
the actual tilted Haar measure. Equal-valued occurrence positions remain distinct. -/
theorem integral_decorated_evaluate_adjoint
    {μ : Measure (EuclideanSpace ℝ (Fin D))} [μ.IsAddHaarMeasure]
    (d : L → EuclideanSpace ℝ (Fin D)) (J : List L)
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (hρ : ∀ c a, ContDiff ℝ ∞ (fun x => ρ c x a)) (hH : ContDiff ℝ ∞ H)
    {r : ℕ} (e : Expr σ (r+2)) (i : Fin (r+2)) (a : Fin (r+1) → Fin D)
    (g : K → EuclideanSpace ℝ (Fin D) → ℝ) (hg : ∀ q, Differentiable ℝ (g q))
    (hZ : Integrable (fun x => Real.exp (-H x)) μ)
    (hi : ∀ k : Fin D, ProductIntegrability (μ.tilted (fun x => -H x)) d J H
      (sectionValue ρ H e (Fin.insertNth i k a)) (coordinateDirection D k) g) :
    (∫ x, partialAlong d J (fun x => Expr.evaluate ρ H (.adjoint i e) x a) x *
      ∏ q, g q x ∂μ.tilted (fun x => -H x)) =
      (∑ k : Fin D, ∑ q, ∫ x,
        partialAlong d J (sectionValue ρ H e (Fin.insertNth i k a)) x *
        dir (coordinateDirection D k) (g q) x * ∏ s ∈ Finset.univ.erase q, g s x
          ∂μ.tilted (fun x => -H x)) +
      ∑ k : Fin D, ((scoreRoutes J).map (fun p => ∫ x,
        partialAlong d p.1 (dir (coordinateDirection D k) H) x *
        partialAlong d p.2 (sectionValue ρ H e (Fin.insertNth i k a)) x * ∏ q, g q x
          ∂μ.tilted (fun x => -H x))).sum := by
  exact integral_decorated_field_mul_prod d J hH (coordinateDirection D)
    (fun k => sectionValue ρ H e (Fin.insertNth i k a))
    (fun k => contDiff_section ρ H hρ hH e _) g hg hZ hi

end EvaluatorIntegral

end AcceleratedLogConcave.Tensor.CoordinateReduction
