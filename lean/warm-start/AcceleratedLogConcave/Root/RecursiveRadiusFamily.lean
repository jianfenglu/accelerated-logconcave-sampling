import AcceleratedLogConcave.Root.ClockBackwardKernel
import AcceleratedLogConcave.Conditional.SourceParameterDomain
import AcceleratedLogConcave.Conditional.RecursiveReferenceFamily
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Constructed recursive reference children for the normalized sampling root.
The physical oracle potential is `z ↦ V (sqrt h • z)`, whose upper curvature
is h. The source radius band satisfies the actual mean-family domain whenever
0 < h ≤ 1/2. Every root slot uses precision K and the prescribed final width.
The source wrapper fixes the public geometry's R and final GL order; unused
numerical mesh fields provably do not change the recursive reference law.
Executable tape coupling and retained approximation estimates are separate. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Root.RecursiveRadiusFamily
open Conditional ClockBackwardKernel

variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem radius_pos {h : ℝ} (hh : 0 < h) (r : RadiusBand h) : 0 < (r : ℝ) := by
  exact lt_of_lt_of_le
    (mul_pos (div_pos (Real.sqrt_pos.mpr (by norm_num)) (by norm_num))
      (Real.sqrt_pos.mpr (by positivity))) r.2.1

theorem radius_small {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1 / 2)
    (r : RadiusBand h) : (r : ℝ) ^ 2 * h ≤ 1 / 2 := by
  have hr := radius_pos hh r
  have hs := Real.sq_sqrt (show 0 ≤ 2*h by positivity)
  have hr2 : (r : ℝ) ^ 2 ≤ 2*h := by
    nlinarith [r.2.2, Real.sqrt_nonneg (2*h)]
  have hb := mul_le_mul_of_nonneg_right hr2 hh.le
  nlinarith [sq_nonneg (h - 1 / 2)]

theorem sourceWidth_pos {h : ℝ} (hh : 0 < h) : 0 < sourceWidth h := by
  unfold sourceWidth
  exact div_pos (div_pos (Real.sqrt_pos.mpr (by norm_num)) (by norm_num))
    (mul_pos (by norm_num) (Real.sqrt_pos.mpr (by positivity)))

theorem sourceWidth_eq (h : ℝ) :
    sourceWidth h = Real.sqrt 3 / Real.sqrt (2*h) := by
  unfold sourceWidth
  ring

/-- The actual prescribed radius and width, with all centers retained. -/
def parameters {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1 / 2)
    (r : RadiusBand h) (center : E) : SourceParameters E h :=
  ⟨(center, r, sourceWidth h), radius_pos hh r, sourceWidth_pos hh,
    radius_small hh hhalf r⟩

omit [Fintype ι] in
@[simp] theorem parameters_center {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1 / 2)
    (r : RadiusBand h) (center : E) : (parameters hh hhalf r center).center = center := rfl
omit [Fintype ι] in
@[simp] theorem parameters_radius {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1 / 2)
    (r : RadiusBand h) (center : E) : (parameters hh hhalf r center).radius = r := rfl
omit [Fintype ι] in
@[simp] theorem parameters_width {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1 / 2)
    (r : RadiusBand h) (center : E) : (parameters hh hhalf r center).width = sourceWidth h := rfl

omit [Fintype ι] in
theorem continuous_parameters {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1 / 2) :
    Continuous (fun z : RadiusBand h × E => parameters hh hhalf z.1 z.2) := by
  apply Continuous.subtype_mk
  exact continuous_snd.prodMk
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_const)

/-- The source's original-gradient coordinate scaling. -/
def physicalPotential (V : E → ℝ) (h : ℝ) : E → ℝ :=
  fun z => V (Real.sqrt h • z)

theorem physicalPotential_C2 {V : E → ℝ} (hV : ContDiff ℝ 2 V) (h : ℝ) :
    ContDiff ℝ 2 (physicalPotential V h) :=
  hV.comp (contDiff_id.const_smul (Real.sqrt h))

private theorem fderiv_scale {V : E → ℝ} (hV : ContDiff ℝ 2 V) (a : ℝ) (z : E) :
    fderiv ℝ (fun w => V (a • w)) z = a • fderiv ℝ V (a • z) := by
  have hd := ((hV.differentiable (by norm_num)) (a • z)).hasFDerivAt.comp z
    ((hasFDerivAt_id z).const_smul a)
  calc
    _ = (fderiv ℝ V (a • z)).comp (a • ContinuousLinearMap.id ℝ E) := hd.fderiv
    _ = _ := by ext u; simp

private theorem hessian_scale {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (a : ℝ) (z u v : E) :
    fderiv ℝ (fderiv ℝ (fun w => V (a • w))) z u v =
      a ^ 2 * fderiv ℝ (fderiv ℝ V) (a • z) u v := by
  have he : fderiv ℝ (fun w => V (a • w)) =
      fun w => a • fderiv ℝ V (a • w) := funext (fderiv_scale hV a)
  rw [he]
  have hd := (((hV.fderiv_right (m := 1) (by norm_num)).differentiable
    (by norm_num)) (a • z)).hasFDerivAt.comp z ((hasFDerivAt_id z).const_smul a)
  have hd' : fderiv ℝ (fun w => a • fderiv ℝ V (a • w)) z =
      a • (fderiv ℝ (fderiv ℝ V) (a • z)).comp
        (a • ContinuousLinearMap.id ℝ E) := (hd.const_smul a).fderiv
  rw [hd']
  simp [pow_two, mul_assoc]

/-- Both Hessian arguments acquire the physical scale; no original-potential
higher derivatives or lower positive curvature are used. -/
theorem physicalPotential_hessian {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    {h : ℝ} (hh : 0 ≤ h) (z u v : E) :
    fderiv ℝ (fderiv ℝ (physicalPotential V h)) z u v =
      h * fderiv ℝ (fderiv ℝ V) (Real.sqrt h • z) u v := by
  change fderiv ℝ (fderiv ℝ (fun w => V (Real.sqrt h • w))) z u v = _
  rw [hessian_scale hV, Real.sq_sqrt hh]

theorem physicalPotential_hessian_nonneg {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ V) z a a)
    {h : ℝ} (hh : 0 ≤ h) (z a : E) :
    0 ≤ fderiv ℝ (fderiv ℝ (physicalPotential V h)) z a a := by
  rw [physicalPotential_hessian hV hh]
  exact mul_nonneg hh (hlo _ _)

theorem physicalPotential_hessian_upper {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ V) z a a ≤ ‖a‖ ^ 2)
    {h : ℝ} (hh : 0 ≤ h) (z a : E) :
    fderiv ℝ (fderiv ℝ (physicalPotential V h)) z a a ≤ h * ‖a‖ ^ 2 := by
  rw [physicalPotential_hessian hV hh]
  exact mul_le_mul_of_nonneg_left (hup _ _) hh

section ConstructedFamily
variable [DecidableEq ι] {m : ℕ}

/-- Exact reference updates use only R and the final GL inventory. Numerical
conditional/forward meshes and pure graph auxiliaries do not change this law. -/
theorem parentFamily_geometry {F : EuclideanSpace ℝ ι → ℝ} {ell : ℝ}
    (hF : ContDiff ℝ 2 F) (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (G G' : Numerics.AffineGraph.MeanGeometry m) (hm : 0 < m)
    (hR : G.R = G'.R) (C : RecursiveReference.Family ι ell) :
    RecursiveReference.parentFamily hF hell hlo hup G hm C =
      RecursiveReference.parentFamily hF hell hlo hup G' hm C := by
  cases G
  cases G'
  dsimp only at hR
  cases hR
  rfl

/-- The complete recursively constructed law is independent of unused
numerical mesh fields, at every real precision and every retained input. -/
theorem referenceFamily_geometry {F : EuclideanSpace ℝ ι → ℝ} {ell : ℝ}
    (hF : ContDiff ℝ 2 F) (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (G G' : Numerics.AffineGraph.MeanGeometry m) (hm : 0 < m)
    (hR : G.R = G'.R) (t : ℝ) (ht : 0 < t) (q : ℝ) :
    RecursiveReference.referenceFamily hF hell hlo hup G hm t ht q =
      RecursiveReference.referenceFamily hF hell hlo hup G' hm t ht q := by
  by_cases hq : Oracle.Precision.terminal q
  · rw [RecursiveReference.referenceFamily_terminal hF hell hlo hup G hm t ht q hq,
      RecursiveReference.referenceFamily_terminal hF hell hlo hup G' hm t ht q hq]
  · have hq' : (1 / 2 : ℝ) < q := lt_of_not_ge hq
    rw [RecursiveReference.referenceFamily_nonterminal hF hell hlo hup G hm t ht q hq',
      RecursiveReference.referenceFamily_nonterminal hF hell hlo hup G' hm t ht q hq']
    rw [referenceFamily_geometry hF hell hlo hup G G' hm hR t ht (q-t)]
    exact parentFamily_geometry hF hell hlo hup G G' hm hR _
termination_by Oracle.Precision.precisionRank t q
decreasing_by exact RecursiveReference.precision_child_lt ht (lt_of_not_ge hq)

/-- Every root slot calls the constructed recursive mean reference at precision
K, its actual radius and the common final width. There is no supplied family
or child-invariance premise. Distinct slots retain their full fixed inventory. -/
def radiusChildren {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1 / 2)
    {F : EuclideanSpace ℝ ι → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ h * ‖a‖ ^ 2)
    (G : Numerics.AffineGraph.MeanGeometry m) (hm : 0 < m)
    (t : ℝ) (ht : 0 < t) (K : ℕ) : RadiusChildren ι h K where
  kernel _ :=
    (RecursiveReference.referenceFamily hF hh.le hlo hup G hm t ht (K : ℝ)).kernel.comap
      (fun z => (parameters hh hhalf z.1.1 z.1.2, z.2))
      (((continuous_parameters hh hhalf).measurable.comp measurable_fst).prodMk measurable_snd)
  markov _ := by
    let C := RecursiveReference.referenceFamily hF hh.le hlo hup G hm t ht (K : ℝ)
    let : IsMarkovKernel C.kernel := C.markov
    exact inferInstanceAs (IsMarkovKernel (C.kernel.comap
      (fun z : (RadiusBand h × E) × E => (parameters hh hhalf z.1.1 z.1.2, z.2))
      (((continuous_parameters hh hhalf).measurable.comp measurable_fst).prodMk measurable_snd)))
  invariant _ r center := by
    let C := RecursiveReference.referenceFamily hF hh.le hlo hup G hm t ht (K : ℝ)
    have he :
        (C.kernel.comap (fun z => (parameters hh hhalf z.1.1 z.1.2, z.2))
          (((continuous_parameters hh hhalf).measurable.comp measurable_fst).prodMk measurable_snd)).comap
          (fun p => ((r,center),p)) measurable_prodMk_left =
        C.kernel.comap (fun p => (parameters hh hhalf r center,p)) measurable_prodMk_left := by
      ext p : 1
      rfl
    rw [he]
    exact C.invariant (parameters hh hhalf r center)

/-- Literal source sections, before any Gaussian averaging. The precision is
the actual integer K and the child input is the original designated p. -/
theorem radiusChildren_apply {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1 / 2)
    {F : EuclideanSpace ℝ ι → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ h * ‖a‖ ^ 2)
    (G : Numerics.AffineGraph.MeanGeometry m) (hm : 0 < m)
    (t : ℝ) (ht : 0 < t) (K : ℕ)
    (i : Fin (ClockSchedule.sourceCells h * ClockSchedule.sourceOrder K))
    (r : RadiusBand h) (center p : E) :
    (radiusChildren hh hhalf hF hlo hup G hm t ht K).kernel i ((r,center),p) =
      (RecursiveReference.referenceFamily hF hh.le hlo hup G hm t ht (K : ℝ)).kernel
        (parameters hh hhalf r center,p) := rfl

/-- The normalized sampling root uses the actual rescaled original potential,
with curvature h derived from the original upper bound I. -/
def physicalRadiusChildren {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1 / 2)
    {V : EuclideanSpace ℝ ι → ℝ} (hV : ContDiff ℝ 2 V)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ V) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ V) z a a ≤ ‖a‖ ^ 2)
    (G : Numerics.AffineGraph.MeanGeometry m) (hm : 0 < m)
    (t : ℝ) (ht : 0 < t) (K : ℕ) : RadiusChildren ι h K :=
  radiusChildren hh hhalf (physicalPotential_C2 hV h)
    (physicalPotential_hessian_nonneg hV hlo hh.le)
    (physicalPotential_hessian_upper hV hup hh.le) G hm t ht K

/-- The internal mean quadrature order is fixed by the public root K, rather
than changed along the decreasing real precision labels. -/
def meanOrder (Csch : ℝ) (K : ℕ) (w : ℝ) : ℕ :=
  Nat.ceil (Csch * ((K : ℝ) + 2) / w)

theorem meanOrder_pos {Csch w : ℝ} (hC : 0 < Csch) (hw : 0 < w) (K : ℕ) :
    0 < meanOrder Csch K w := by
  apply Nat.ceil_pos.mpr
  exact div_pos (mul_pos hC (by positivity)) hw

/-- The prescribed public geometry has R=h^t and the literal schedule order.
The scalar schedule guards remain explicit; no error or work conclusion is a
premise. Its conditional/forward meshes do not enter the exact reference law. -/
def sourceRadiusChildren {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1 / 2)
    {V : EuclideanSpace ℝ ι → ℝ} (hV : ContDiff ℝ 2 V)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ V) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ V) z a a ≤ ‖a‖ ^ 2)
    (Csch w : ℝ) (hC : 0 < Csch) (hw : 0 < w)
    (t : ℝ) (ht : 0 < t) (K : ℕ)
    (G : Numerics.AffineGraph.MeanGeometry (meanOrder Csch K w))
    (_hR : G.R = h ^ t) : RadiusChildren ι h K :=
  physicalRadiusChildren hh hhalf hV hlo hup G (meanOrder_pos hC hw K) t ht K

section RootKernel
variable {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1 / 2)
    {V : EuclideanSpace ℝ ι → ℝ} (hV : ContDiff ℝ 2 V)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ V) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ V) z a a ≤ ‖a‖ ^ 2)
    (Csch w : ℝ) (hC : 0 < Csch) (hw : 0 < w)
    (t : ℝ) (ht : 0 < t) (K : ℕ)
    (G : Numerics.AffineGraph.MeanGeometry (meanOrder Csch K w))
    (hR : G.R = h ^ t)
    (P : Analysis.Poisson.ReferencePoissonFamily (EuclideanSpace ℝ ι) 0 (1 / 2))

/-- Concrete clock kernel using the constructed recursive source children.
The supplied exact parent Poisson family remains explicit; this definition
does not assert an identification of that family with the original V. -/
def sourceRootKernel : Kernel (ClockLaw.Clock × Kinetic.GaussianPhase E) E :=
  sourceKernelFromRadiusFamily P h hh K
    (sourceRadiusChildren hh hhalf hV hlo hup Csch w hC hw t ht K G hR)

instance sourceRootKernel_markov : IsMarkovKernel
    (sourceRootKernel hh hhalf hV hlo hup Csch w hC hw t ht K G hR P) := by
  unfold sourceRootKernel
  infer_instance

/-- Every actual clock section is stationary in the dormant Gaussian input.
There is no unresolved child-family input to this conclusion. -/
theorem sourceRootKernel_conditionallyInvariant (clock : ClockLaw.Clock) :
    ∀ (x : E × E) (s : Set E), MeasurableSet s →
      (∫⁻ p, sourceRootKernel hh hhalf hV hlo hup Csch w hC hw t ht K G hR P
        (clock,(x,p)) s ∂stdGaussian E) = stdGaussian E s :=
  sourceKernelFromRadiusFamily_conditionallyInvariant P h hh K
    (sourceRadiusChildren hh hhalf hV hlo hup Csch w hC hw t ht K G hR) clock

end RootKernel

end ConstructedFamily

end AcceleratedLogConcave.Root.RecursiveRadiusFamily
