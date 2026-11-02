import AcceleratedLogConcave.Tensor.Expressions
import AcceleratedLogConcave.Gibbs.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Local adjoint-reduction identities and restricted-grammar termination

The identities below use actual Fréchet derivatives. Labeled routing is a list,
so repeated directions retain their Leibniz multiplicity. The structural
reduction relation is only a termination interface, not yet the complete
semantics-preserving ordered-network compiler or the final RMS estimate.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace AcceleratedLogConcave.Tensor.AdjointReduction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual directional derivative, with constant spatial direction. -/
def dir (v : E) (f : E → ℝ) : E → ℝ := fun x => fderiv ℝ f x v

/-- Ordered differentiation; labels and their direction values are separate. -/
def partialAlong {L : Type*} (d : L → E) : List L → (E → ℝ) → E → ℝ
  | [], f => f
  | i :: J, f => dir (d i) (partialAlong d J f)

/-- Every label position is routed once. List multiplicity is intentional. -/
def routes {L : Type*} : List L → List (List L × List L)
  | [] => [([], [])]
  | i :: J => (routes J).map (fun p => (p.1, i :: p.2)) ++
      (routes J).map (fun p => (i :: p.1, p.2))

theorem routes_length {L : Type*} (J : List L) : (routes J).length = 2 ^ J.length := by
  induction J with
  | nil => simp [routes]
  | cons i J ih => simp [routes, ih, pow_succ]; omega

/-- Smoothness of every actual directional derivative. -/
theorem contDiff_dir {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (v : E) :
    ContDiff ℝ ∞ (dir v f) :=
  ((contDiff_infty_iff_fderiv.mp hf).2).clm_apply contDiff_const

theorem contDiff_partialAlong {L : Type*} (d : L → E) (J : List L)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (partialAlong d J f) := by
  induction J with
  | nil => exact hf
  | cons i J ih => exact contDiff_dir ih _

theorem dir_add (v : E) {f g : E → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) : dir v (fun x => f x + g x) = (fun x => dir v f x + dir v g x) := by
  funext x
  simpa [dir] using congrArg (fun L : E →L[ℝ] ℝ => L v)
    (fderiv_fun_add (hf x) (hg x))

theorem dir_neg (v : E) (f : E → ℝ) : dir v (fun x => -f x) = (fun x => -dir v f x) := by
  funext x
  simp [dir]

theorem dir_mul (v : E) {f g : E → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) :
    dir v (fun x => f x * g x) = fun x => dir v f x * g x + f x * dir v g x := by
  funext x
  have h := congrArg (fun L : E →L[ℝ] ℝ => L v)
    (fderiv_fun_mul (hf x) (hg x))
  simpa [dir, add_comm, mul_comm] using h

/-- Schwarz symmetry applied to actual directional derivatives. -/
theorem dir_comm {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (v w : E) :
    dir v (dir w f) = dir w (dir v f) := by
  funext x
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (contDiff_infty_iff_fderiv.mp hf).2.differentiable (by simp)
  change fderiv ℝ (fun y => fderiv ℝ f y w) x v =
    fderiv ℝ (fun y => fderiv ℝ f y v) x w
  rw [((hd x).hasFDerivAt.clm_apply (hasFDerivAt_const w x)).fderiv,
    ((hd x).hasFDerivAt.clm_apply (hasFDerivAt_const v x)).fderiv]
  simpa using (hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq v w


/-- Routes with a nonempty left group, still keeping positional multiplicities. -/
def scoreRoutes {L : Type*} : List L → List (List L × List L)
  | [] => []
  | i :: J => (scoreRoutes J).map (fun p => (p.1, i :: p.2)) ++
      (routes J).map (fun p => (i :: p.1, p.2))

theorem routes_eq {L : Type*} (J : List L) : routes J = ([], J) :: scoreRoutes J := by
  induction J with
  | nil => rfl
  | cons i J ih =>
    simp only [routes, scoreRoutes]
    rw [ih]
    rfl

theorem scoreRoutes_left_ne_nil {L : Type*} (J : List L)
    (p : List L × List L) (hp : p ∈ scoreRoutes J) : p.1 ≠ [] := by
  induction J generalizing p with
  | nil => simp [scoreRoutes] at hp
  | cons i J ih =>
    simp only [scoreRoutes, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, _, rfl⟩
    · exact ih q hq
    · simp

theorem route_length {L : Type*} (J : List L) (p : List L × List L)
    (hp : p ∈ routes J) : p.1.length + p.2.length = J.length := by
  induction J generalizing p with
  | nil => simp [routes] at hp; subst p; rfl
  | cons i J ih =>
    simp only [routes, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · simp only [List.length_cons]; have := ih q hq; omega
    · simp only [List.length_cons]; have := ih q hq; omega

theorem contDiff_list_sum {I : Type*} (l : List I) (F : I → E → ℝ)
    (hF : ∀ a ∈ l, ContDiff ℝ ∞ (F a)) :
    ContDiff ℝ ∞ (fun x => (l.map (fun a => F a x)).sum) := by
  induction l with
  | nil => simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : E => (0 : ℝ)))
  | cons a l ih =>
    exact (hF a (by simp)).add (ih (fun b hb => hF b (by simp [hb])))

theorem dir_list_sum {I : Type*} (v : E) (l : List I) (F : I → E → ℝ)
    (hF : ∀ a ∈ l, ContDiff ℝ ∞ (F a)) :
    dir v (fun x => (l.map (fun a => F a x)).sum) =
      fun x => (l.map (fun a => dir v (F a) x)).sum := by
  induction l with
  | nil => funext x; simp [dir]
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [dir_add v ((hF a (by simp)).differentiable (by simp))]
    · rw [ih (fun b hb => hF b (by simp [hb]))]
    · exact (contDiff_list_sum l F (fun b hb => hF b (by simp [hb]))).differentiable
        (by simp)

theorem partialAlong_add {L : Type*} (d : L → E) (J : List L)
    {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    partialAlong d J (fun x => f x + g x) = (fun x => partialAlong d J f x + partialAlong d J g x) := by
  induction J with
  | nil => rfl
  | cons i J ih =>
    simp only [partialAlong]
    rw [ih]
    exact dir_add _ ((contDiff_partialAlong d J hf).differentiable (by simp))
      ((contDiff_partialAlong d J hg).differentiable (by simp))

theorem partialAlong_neg {L : Type*} (d : L → E) (J : List L) (f : E → ℝ) :
    partialAlong d J (fun x => -f x) = (fun x => -partialAlong d J f x) := by
  induction J with
  | nil => rfl
  | cons i J ih => simp only [partialAlong, ih, dir_neg]

theorem partialAlong_dir {L : Type*} (d : L → E) (J : List L)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (v : E) :
    partialAlong d J (dir v f) = dir v (partialAlong d J f) := by
  induction J with
  | nil => rfl
  | cons i J ih =>
    simp only [partialAlong, ih]
    exact dir_comm (contDiff_partialAlong d J hf) _ _

theorem dir_partialAlong_mul {L : Type*} (d : L → E) (A B : List L) (v : E)
    {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    dir v (fun x => partialAlong d A f x * partialAlong d B g x) =
      fun x => dir v (partialAlong d A f) x * partialAlong d B g x +
        partialAlong d A f x * dir v (partialAlong d B g) x :=
  dir_mul v ((contDiff_partialAlong d A hf).differentiable (by simp))
    ((contDiff_partialAlong d B hg).differentiable (by simp))

/-- Full labeled Leibniz expansion, including repeated spatial directions. -/
theorem partialAlong_mul {L : Type*} (d : L → E) (J : List L)
    {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    partialAlong d J (fun x => f x * g x) =
      fun x => ((routes J).map (fun p => partialAlong d p.1 f x * partialAlong d p.2 g x)).sum := by
  induction J with
  | nil => funext x; simp [partialAlong, routes]
  | cons i J ih =>
    simp only [partialAlong]
    rw [ih, dir_list_sum (d i) (routes J)
      (fun p x => partialAlong d p.1 f x * partialAlong d p.2 g x)
      (fun p _ => (contDiff_partialAlong d p.1 hf).mul (contDiff_partialAlong d p.2 hg))]
    simp_rw [dir_partialAlong_mul d _ _ _ hf hg]
    funext x
    simp only [routes, List.map_append, List.sum_append, List.map_map,
      Function.comp_def, partialAlong, List.sum_map_add]
    ring

/-- One coordinate contribution to the formal weighted divergence. -/
def adjointComponent (H : E → ℝ) (v : E) (f : E → ℝ) : E → ℝ :=
  fun x => -dir v f x + dir v H x * f x

/-- Exact commutator: nonempty groups differentiate the score, and the principal
term keeps the full original label list on the operand. -/
theorem decorated_adjoint {L : Type*} (d : L → E) (J : List L) {H f : E → ℝ}
    (hH : ContDiff ℝ ∞ H) (hf : ContDiff ℝ ∞ f) (v : E) :
    partialAlong d J (adjointComponent H v f) = fun x =>
      adjointComponent H v (partialAlong d J f) x +
      ((scoreRoutes J).map (fun p =>
        partialAlong d p.1 (dir v H) x * partialAlong d p.2 f x)).sum := by
  change partialAlong d J (fun x => -dir v f x + dir v H x * f x) = _
  rw [partialAlong_add d J (contDiff_dir hf v).neg
    ((contDiff_dir hH v).mul hf), partialAlong_neg, partialAlong_dir d J hf v,
    partialAlong_mul d J (contDiff_dir hH v) hf, routes_eq]
  funext x
  simp only [List.map_cons, List.sum_cons, partialAlong,
    adjointComponent]
  ring



/-- Derivatives of the score are derivatives of the actual Hessian. -/
theorem dir_dir_eq_hessian {H : E → ℝ} (hH : ContDiff ℝ ∞ H) (v w : E) :
    dir v (dir w H) = fun x => fderiv ℝ (fderiv ℝ H) x v w := by
  funext x
  have hd := (contDiff_infty_iff_fderiv.mp hH).2.differentiable (by simp)
  change fderiv ℝ (fun y => fderiv ℝ H y w) x v = _
  rw [((hd x).hasFDerivAt.clm_apply (hasFDerivAt_const w x)).fderiv]
  simp

theorem nonempty_score_is_hessian {L : Type*} (d : L → E) (i : L) (J : List L)
    {H : E → ℝ} (hH : ContDiff ℝ ∞ H) (v : E) :
    partialAlong d (i :: J) (dir v H) =
      partialAlong d J (fun x => fderiv ℝ (fderiv ℝ H) x (d i) v) := by
  rw [partialAlong, ← partialAlong_dir d J (contDiff_dir hH v) (d i),
    dir_dir_eq_hessian hH]

theorem dir_sum {K : Type*} (s : Finset K) (v : E) (f : K → E → ℝ)
    (hf : ∀ k ∈ s, Differentiable ℝ (f k)) :
    dir v (fun x => ∑ k ∈ s, f k x) = fun x => ∑ k ∈ s, dir v (f k) x := by
  funext x
  simp only [dir, fderiv_fun_sum (fun k hk => hf k hk x)]
  simp

theorem partialAlong_sum {L K : Type*} (d : L → E) (J : List L)
    (s : Finset K) (f : K → E → ℝ) (hf : ∀ k ∈ s, ContDiff ℝ ∞ (f k)) :
    partialAlong d J (fun x => ∑ k ∈ s, f k x) =
      fun x => ∑ k ∈ s, partialAlong d J (f k) x := by
  induction J with
  | nil => rfl
  | cons i J ih =>
    simp only [partialAlong]
    rw [ih, dir_sum s (d i) (fun k => partialAlong d J (f k))
      (fun k hk => (contDiff_partialAlong d J (hf k hk)).differentiable (by simp))]

/-- The formal adjoint is a literal finite coordinate sum. -/
def adjointField {K : Type*} [Fintype K] (H : E → ℝ) (v : K → E)
    (f : K → E → ℝ) : E → ℝ := fun x => ∑ k, adjointComponent H (v k) (f k) x

theorem decorated_adjointField {L K : Type*} [Fintype K] (d : L → E) (J : List L)
    {H : E → ℝ} (hH : ContDiff ℝ ∞ H) (v : K → E) (f : K → E → ℝ)
    (hf : ∀ k, ContDiff ℝ ∞ (f k)) :
    partialAlong d J (adjointField H v f) = fun x =>
      adjointField H v (fun k => partialAlong d J (f k)) x +
      ∑ k, ((scoreRoutes J).map (fun p =>
        partialAlong d p.1 (dir (v k) H) x * partialAlong d p.2 (f k) x)).sum := by
  change partialAlong d J (fun x => ∑ k, adjointComponent H (v k) (f k) x) = _
  have ha (k : K) : ContDiff ℝ ∞ (adjointComponent H (v k) (f k)) :=
    (contDiff_dir (hf k) (v k)).neg.add ((contDiff_dir hH (v k)).mul (hf k))
  rw [partialAlong_sum d J Finset.univ (fun k => adjointComponent H (v k) (f k))
    (fun k _ => ha k)]
  simp_rw [decorated_adjoint d J hH (hf _) _]
  funext x
  simp only [Finset.sum_add_distrib, adjointField]

/-- Bridge to the established expression evaluator: no supplied value certificate. -/
theorem evaluate_adjoint_eq_field {Name : Type*} {σ : CoefficientSignature Name} {D r : ℕ}
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (e : Expr σ (r+2)) (i : Fin (r+2)) (a : Fin (r+1) → Fin D) :
    (fun x => Expr.evaluate ρ H (.adjoint i e) x a) =
      adjointField H (coordinateDirection D)
        (fun k x => Expr.evaluate ρ H e x (Fin.insertNth i k a)) := rfl

/-- Product rule indexed by occurrences, not by distinct field values. -/
theorem dir_prod {K : Type*} [DecidableEq K] (s : Finset K) (v : E) (g : K → E → ℝ)
    (hg : ∀ k ∈ s, Differentiable ℝ (g k)) :
    dir v (fun x => ∏ k ∈ s, g k x) = fun x =>
      ∑ k ∈ s, dir v (g k) x * ∏ j ∈ s.erase k, g j x := by
  funext x
  simp only [dir, fderiv_finsetProd (fun k hk => hg k hk x)]
  simp [mul_comm]


/-- Every position is routed once: recombining the two groups preserves the
entire original list as a multiset, including repeated labels. -/
theorem route_perm {L : Type*} (J : List L) (p : List L × List L)
    (hp : p ∈ routes J) : (p.1 ++ p.2).Perm J := by
  induction J generalizing p with
  | nil => simp [routes] at hp; subst p; exact List.Perm.refl _
  | cons i J ih =>
    simp only [routes, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact List.perm_middle.trans ((ih q hq).cons i)
    · exact (ih q hq).cons i

/-- Labels keep their relative order on each side. -/
theorem route_sublists {L : Type*} (J : List L) (p : List L × List L)
    (hp : p ∈ routes J) : p.1.Sublist J ∧ p.2.Sublist J := by
  induction J generalizing p with
  | nil => simp [routes] at hp; subst p; exact ⟨List.Sublist.refl _, List.Sublist.refl _⟩
  | cons i J ih =>
    simp only [routes, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact ⟨(ih q hq).1.cons _, (ih q hq).2.cons_cons _⟩
    · exact ⟨(ih q hq).1.cons_cons _, (ih q hq).2.cons _⟩

/-- The principal empty-left route is unique even with repeated labels. -/
theorem empty_left_iff {L : Type*} (J : List L) (p : List L × List L)
    (hp : p ∈ routes J) (h : p.1 = []) : p = ([], J) := by
  rw [routes_eq] at hp
  rcases List.mem_cons.mp hp with rfl | hs
  · rfl
  · exact False.elim (scoreRoutes_left_ne_nil J p hs h)

section WeightedIBP
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Whole-space weighted integration by parts for an actual adjoint component.
The hypotheses are product integrability, not an assumed integration identity. -/
theorem integral_adjoint_mul {H f g : E → ℝ} (v : E)
    (hH : Differentiable ℝ H) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hZ : Integrable (fun x => Real.exp (-H x)) μ)
    (hfg : Integrable (fun x => f x * g x) (μ.tilted (fun x => -H x)))
    (hs : Integrable (fun x => dir v H x * f x * g x) (μ.tilted (fun x => -H x)))
    (hdf : Integrable (fun x => dir v f x * g x) (μ.tilted (fun x => -H x)))
    (hdg : Integrable (fun x => f x * dir v g x) (μ.tilted (fun x => -H x))) :
    ∫ x, adjointComponent H v f x * g x ∂(μ.tilted (fun x => -H x)) =
      ∫ x, f x * dir v g x ∂(μ.tilted (fun x => -H x)) := by
  have hp := Gibbs.integral_tilted_fderiv (μ := μ) (f := fun x => f x * g x)
    v hH (hf.fun_mul hg) hZ
    (by simpa only [dir, mul_assoc] using hs)
    (by
      change Integrable (dir v (fun x => f x * g x)) _
      rw [dir_mul v hf hg]
      exact hdf.add hdg)
    hfg
  have heq : ∫ x, dir v f x * g x ∂(μ.tilted (fun x => -H x)) +
      ∫ x, f x * dir v g x ∂(μ.tilted (fun x => -H x)) =
      ∫ x, dir v H x * f x * g x ∂(μ.tilted (fun x => -H x)) := by
    change (∫ x, dir v (fun y => f y * g y) x ∂_) = _ at hp
    rw [dir_mul v hf hg, integral_add hdf hdg] at hp
    simpa only [dir, mul_assoc] using hp
  calc
    _ = -(∫ x, dir v f x * g x ∂(μ.tilted (fun x => -H x))) +
        ∫ x, dir v H x * f x * g x ∂(μ.tilted (fun x => -H x)) := by
      simp only [adjointComponent, add_mul, neg_mul]
      have hn : Integrable (fun x => -(dir v f x * g x))
          (μ.tilted (fun x => -H x)) := by
        exact hdf.fun_neg
      rw [integral_add hn hs, integral_neg]
    _ = _ := by linarith


/-- Full-product IBP chooses exactly one of the indexed OTHER occurrences.
The operand f never appears among the derivative recipients in this sum. -/
theorem integral_adjoint_mul_prod {K : Type*} [Fintype K] [DecidableEq K]
    {H f : E → ℝ} (g : K → E → ℝ) (v : E)
    (hH : Differentiable ℝ H) (hf : Differentiable ℝ f)
    (hg : ∀ k, Differentiable ℝ (g k))
    (hZ : Integrable (fun x => Real.exp (-H x)) μ)
    (hfg : Integrable (fun x => f x * ∏ k, g k x) (μ.tilted (fun x => -H x)))
    (hs : Integrable (fun x => dir v H x * f x * ∏ k, g k x)
      (μ.tilted (fun x => -H x)))
    (hdf : Integrable (fun x => dir v f x * ∏ k, g k x)
      (μ.tilted (fun x => -H x)))
    (hterms : ∀ k, Integrable (fun x => f x * dir v (g k) x *
      ∏ j ∈ Finset.univ.erase k, g j x) (μ.tilted (fun x => -H x))) :
    ∫ x, adjointComponent H v f x * (∏ k, g k x) ∂(μ.tilted (fun x => -H x)) =
      ∑ k, ∫ x, f x * dir v (g k) x * (∏ j ∈ Finset.univ.erase k, g j x)
        ∂(μ.tilted (fun x => -H x)) := by
  have hprod : Differentiable ℝ (fun x => ∏ k, g k x) := by fun_prop
  have hdg : Integrable (fun x => f x * dir v (fun y => ∏ k, g k y) x)
      (μ.tilted (fun x => -H x)) := by
    rw [dir_prod Finset.univ v g (fun k _ => hg k)]
    simp_rw [Finset.mul_sum, ← mul_assoc]
    exact integrable_finsetSum Finset.univ (fun k _ => hterms k)
  rw [integral_adjoint_mul v hH hf hprod hZ hfg hs hdf hdg,
    dir_prod Finset.univ v g (fun k _ => hg k)]
  simp_rw [Finset.mul_sum, ← mul_assoc]
  exact integral_finsetSum Finset.univ (fun k _ => hterms k)


/-- Whole-space IBP for the actual finite-coordinate formal divergence,
including the empty-coordinate (dimension-zero) case. -/
theorem integral_adjointField_mul {K : Type*} [Fintype K]
    {H g : E → ℝ} (v : K → E) (f : K → E → ℝ)
    (hH : Differentiable ℝ H) (hg : Differentiable ℝ g)
    (hf : ∀ k, Differentiable ℝ (f k))
    (hZ : Integrable (fun x => Real.exp (-H x)) μ)
    (hfg : ∀ k, Integrable (fun x => f k x * g x) (μ.tilted (fun x => -H x)))
    (hs : ∀ k, Integrable (fun x => dir (v k) H x * f k x * g x)
      (μ.tilted (fun x => -H x)))
    (hdf : ∀ k, Integrable (fun x => dir (v k) (f k) x * g x)
      (μ.tilted (fun x => -H x)))
    (hdg : ∀ k, Integrable (fun x => f k x * dir (v k) g x)
      (μ.tilted (fun x => -H x))) :
    ∫ x, adjointField H v f x * g x ∂(μ.tilted (fun x => -H x)) =
      ∑ k, ∫ x, f k x * dir (v k) g x ∂(μ.tilted (fun x => -H x)) := by
  have hi (k : K) : Integrable (fun x => adjointComponent H (v k) (f k) x * g x)
      (μ.tilted (fun x => -H x)) := by
    simpa only [adjointComponent, add_mul, neg_mul] using (hdf k).fun_neg.fun_add (hs k)
  simp_rw [adjointField, Finset.sum_mul]
  rw [integral_finsetSum Finset.univ (fun k _ => hi k)]
  exact Finset.sum_congr rfl (fun k _ => integral_adjoint_mul (v k) hH (hf k) hg
    hZ (hfg k) (hs k) (hdf k) (hdg k))

end WeightedIBP

section Termination
omit [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Name Label : Type*} {σ : CoefficientSignature Name}

/-- All unexpanded syntax nodes, including zero-cost slot permutations. This
rank is for termination, not the later formula-size complexity estimate. -/
def syntaxRank : {r : ℕ} → Expr σ r → ℕ
  | _, .coefficient _ => 0
  | _, .permute _ e => syntaxRank e + 1
  | _, .contract e f _ _ => syntaxRank e + syntaxRank f + 1
  | _, .derivative e => syntaxRank e + 1
  | _, .adjoint _ e => syntaxRank e + 1

/-- Opaque occurrences in the structural scheduler. Score leaves retain both
the former divergence direction and their nonempty score-derivative group. -/
inductive Pending (σ : CoefficientSignature Name) (Label : Type*) (E : Type*)
  | formula {r : ℕ} (expression : Expr σ r) (labels : List Label)
  | score (divergenceDirection : E) (labels : List Label) (nonempty : labels ≠ [])

namespace Pending
variable {σ : CoefficientSignature Name}

def rank : Pending σ Label E → ℕ
  | .formula e _ => syntaxRank e
  | .score _ _ _ => 0

/-- An outside derivative is added in front of, without changing, old labels. -/
def decorate (i : Label) : Pending σ Label E → Pending σ Label E
  | .formula e J => .formula e (i :: J)
  | .score v J h => .score v (i :: J) (by simp)

@[simp] theorem rank_decorate (i : Label) (p : Pending σ Label E) :
    (p.decorate i).rank = p.rank := by cases p <;> rfl

def Terminal : Pending σ Label E → Prop
  | .formula (.coefficient _) _ => True
  | .score _ _ _ => True
  | _ => False

theorem terminal_iff_rank_eq_zero (p : Pending σ Label E) : p.Terminal ↔ p.rank = 0 := by
  cases p with
  | score => simp [Terminal, rank]
  | formula e J => cases e <;> simp [Terminal, rank, syntaxRank]
end Pending

def forestRank (s : List (Pending σ Label E)) : ℕ := (s.map Pending.rank).sum

/-- Concrete local reduction, oriented as `Step next current` for well-foundedness.
It is a structural shadow: the complete coordinate-network interpretation is a
separate compiler obligation. Principal IBP recipients are different LIST POSITIONS,
including when the two fields happen to have equal values. -/
inductive Step : List (Pending σ Label E) → List (Pending σ Label E) → Prop
  | permute {r : ℕ} (p : Equiv.Perm (Fin r)) (e : Expr σ r) (J : List Label)
      (before after : List (Pending σ Label E)) :
      Step (before ++ [.formula e J] ++ after)
        (before ++ [.formula (.permute p e) J] ++ after)
  | derivative {r : ℕ} (e : Expr σ r) (J : List Label) (i : Label)
      (before after : List (Pending σ Label E)) :
      Step (before ++ [.formula e (J ++ [i])] ++ after)
        (before ++ [.formula (.derivative e) J] ++ after)
  | contract {r s : ℕ} (e : Expr σ (r+2)) (f : Expr σ (s+2))
      (i : Fin (r+2)) (j : Fin (s+2)) (J A B : List Label)
      (route : (A, B) ∈ routes J) (before after : List (Pending σ Label E)) :
      Step (before ++ [.formula e A, .formula f B] ++ after)
        (before ++ [.formula (.contract e f i j) J] ++ after)
  | score {r : ℕ} (e : Expr σ (r+2)) (i : Fin (r+2)) (v : E)
      (J A B : List Label) (route : (A, B) ∈ scoreRoutes J)
      (before after : List (Pending σ Label E)) :
      Step (before ++ [.score v A (scoreRoutes_left_ne_nil J (A, B) route),
        .formula e B] ++ after)
        (before ++ [.formula (.adjoint i e) J] ++ after)
  | ibpAfter {r : ℕ} (e : Expr σ (r+2)) (i : Fin (r+2)) (J : List Label)
      (newLabel : Label) (other : Pending σ Label E)
      (before between after : List (Pending σ Label E)) :
      Step (before ++ [.formula e J] ++ between ++ [other.decorate newLabel] ++ after)
        (before ++ [.formula (.adjoint i e) J] ++ between ++ [other] ++ after)
  | ibpBefore {r : ℕ} (e : Expr σ (r+2)) (i : Fin (r+2)) (J : List Label)
      (newLabel : Label) (other : Pending σ Label E)
      (before between after : List (Pending σ Label E)) :
      Step (before ++ [other.decorate newLabel] ++ between ++ [.formula e J] ++ after)
        (before ++ [other] ++ between ++ [.formula (.adjoint i e) J] ++ after)

/-- Every actual scheduler constructor removes one original syntax node. -/
theorem step_rank {s t : List (Pending σ Label E)} (h : Step t s) :
    forestRank t + 1 = forestRank s := by
  cases h <;> simp only [forestRank, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, Pending.rank_decorate] <;>
    simp only [Pending.rank, syntaxRank] <;> omega

theorem step_rank_lt {s t : List (Pending σ Label E)} (h : Step t s) :
    forestRank t < forestRank s := by have := step_rank h; omega

/-- No infinite chain of the concrete reduction rules is possible. -/
theorem step_wellFounded : WellFounded (Step (σ := σ) (Label := Label) (E := E)) :=
  (measure forestRank).wf.mono (fun _ _ h => step_rank_lt h)

theorem step_length {s t : List (Pending σ Label E)} (h : Step t s) : s.length ≤ t.length := by
  cases h <;> simp

theorem step_two_le {s t : List (Pending σ Label E)} (h : Step t s) (hs : 2 ≤ s.length) :
    2 ≤ t.length := hs.trans (step_length h)


/-- Zero remaining syntax nodes means that every occurrence is terminal. -/
theorem forestRank_eq_zero_iff (s : List (Pending σ Label E)) :
    forestRank s = 0 ↔ ∀ p ∈ s, p.Terminal := by
  induction s with
  | nil => simp [forestRank]
  | cons p s ih =>
    change p.rank + forestRank s = 0 ↔ _
    rw [Nat.add_eq_zero_iff, ← Pending.terminal_iff_rank_eq_zero, ih]
    simp

/-- A nonterminal state with at least two occurrences always has a legal
structural reduction. An adjoint uses a genuinely different old position.
The label type only needs a value for the newly created derivative position. -/
theorem step_progress [Nonempty Label] (s : List (Pending σ Label E))
    (hs : 2 ≤ s.length) (h : forestRank s ≠ 0) : ∃ t, Step t s := by
  classical
  have hn : ¬ ∀ p ∈ s, p.Terminal := fun hh => h ((forestRank_eq_zero_iff s).mpr hh)
  push Not at hn
  obtain ⟨p, hp, hnt⟩ := hn
  obtain ⟨before, after, rfl⟩ := List.mem_iff_append.mp hp
  cases p with
  | score v J hJ => exact False.elim (hnt True.intro)
  | formula e J =>
    cases e with
    | coefficient c => exact False.elim (hnt True.intro)
    | permute perm e => exact ⟨_, by simpa using (Step.permute perm e J before after)⟩
    | derivative e =>
      exact ⟨_, by simpa using (Step.derivative e J (Classical.choice inferInstance) before after)⟩
    | contract e f i j =>
      exact ⟨_, by simpa using (Step.contract e f i j J [] J (by rw [routes_eq]; simp) before after)⟩
    | adjoint i e =>
      cases before with
      | nil =>
        cases after with
        | nil => simp at hs
        | cons other rest =>
          exact ⟨_, by simpa using (Step.ibpAfter e i J (Classical.choice inferInstance)
            other [] [] rest)⟩
      | cons other rest =>
        exact ⟨_, by simpa using (Step.ibpBefore e i J (Classical.choice inferInstance)
          other [] rest after)⟩

/-- The exact number of removed syntax nodes bounds any concrete reduction
chain. This counts actual steps, not vertices of a chain. -/
inductive Steps : ℕ → List (Pending σ Label E) → List (Pending σ Label E) → Prop
  | zero (s) : Steps 0 s s
  | succ {n s t u} (first : Step t s) (rest : Steps n t u) : Steps (n+1) s u

theorem steps_rank {n : ℕ} {s t : List (Pending σ Label E)} (h : Steps n s t) :
    forestRank t + n = forestRank s := by
  induction h with
  | zero => simp
  | succ first rest ih => have := step_rank first; omega

theorem steps_le_initial_rank {n : ℕ} {s t : List (Pending σ Label E)} (h : Steps n s t) :
    n ≤ forestRank s := by have := steps_rank h; omega

/-- Structural reduction actually reaches coefficient/score leaves. This is
not yet the semantics-preserving coordinate-network compiler. -/
theorem exists_terminal [Nonempty Label] (s : List (Pending σ Label E))
    (hs : 2 ≤ s.length) :
    ∃ n t, Steps n s t ∧ (∀ p ∈ t, p.Terminal) ∧ n = forestRank s := by
  induction s using step_wellFounded.induction with
  | h s ih =>
    by_cases hz : forestRank s = 0
    · exact ⟨0, s, Steps.zero s, (forestRank_eq_zero_iff s).mp hz, hz.symm⟩
    · obtain ⟨t, ht⟩ := step_progress s hs hz
      obtain ⟨n, u, hn, hu, heq⟩ := ih t ht (step_two_le ht hs)
      refine ⟨n+1, u, Steps.succ ht hn, hu, ?_⟩
      rw [heq]
      exact step_rank ht

end Termination

end AcceleratedLogConcave.Tensor.AdjointReduction
