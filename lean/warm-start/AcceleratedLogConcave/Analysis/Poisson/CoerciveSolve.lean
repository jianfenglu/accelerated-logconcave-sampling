import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Topology.Algebra.Module.LinearPMap

noncomputable section
open InnerProductSpace
open scoped RealInnerProductSpace

namespace AcceleratedLogConcave.Analysis.Poisson

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- The closed graph restricted to the kernel of the scalar constraint. -/
def centeredGraph (A : H →ₗ.[ℝ] K) (ell : H →L[ℝ] ℝ) :
    Submodule ℝ (WithLp 2 (H × K)) :=
  A.graph.comap (WithLp.prodContinuousLinearEquiv 2 ℝ H K).toLinearMap ⊓
    (ell.comp (WithLp.fstL 2 ℝ H K)).ker

omit [CompleteSpace H] [CompleteSpace K] in
theorem centeredGraph_closed (A : H →ₗ.[ℝ] K) (hA : A.IsClosed)
    (ell : H →L[ℝ] ℝ) : IsClosed (centeredGraph A ell : Set (WithLp 2 (H × K))) :=
  (hA.preimage (WithLp.prodContinuousLinearEquiv 2 ℝ H K).continuous).inter
    (ell.comp (WithLp.fstL 2 ℝ H K)).isClosed_ker

private def valueMap (A : H →ₗ.[ℝ] K) (ell : H →L[ℝ] ℝ) :
    centeredGraph A ell →L[ℝ] H :=
  (WithLp.fstL 2 ℝ H K).comp (centeredGraph A ell).subtypeL

private def gradientMap (A : H →ₗ.[ℝ] K) (ell : H →L[ℝ] ℝ) :
    centeredGraph A ell →L[ℝ] K :=
  (WithLp.sndL 2 ℝ H K).comp (centeredGraph A ell).subtypeL

private def energyForm (A : H →ₗ.[ℝ] K) (ell : H →L[ℝ] ℝ) :
    centeredGraph A ell →L[ℝ] centeredGraph A ell →L[ℝ] ℝ :=
  let compose : (K →L[ℝ] ℝ) →L[ℝ] centeredGraph A ell →L[ℝ] ℝ :=
    (gradientMap A ell).precomp ℝ
  compose.comp ((innerSL ℝ : K →L[ℝ] K →L[ℝ] ℝ).comp (gradientMap A ell))

omit [CompleteSpace H] [CompleteSpace K] in
private theorem energyForm_apply (A : H →ₗ.[ℝ] K) (ell : H →L[ℝ] ℝ)
    (u v : centeredGraph A ell) :
    energyForm A ell u v = inner ℝ (gradientMap A ell u) (gradientMap A ell v) := rfl

omit [CompleteSpace H] [CompleteSpace K] in
private theorem graph_coercive (A : H →ₗ.[ℝ] K) (ell : H →L[ℝ] ℝ)
    {m : ℝ} (hm : 0 < m)
    (hcoer : ∀ u : A.domain, ell u = 0 → m * ‖(u : H)‖ ^ 2 ≤ ‖A u‖ ^ 2) :
    IsCoercive (energyForm A ell) := by
  refine ⟨m / (m + 1), by positivity, ?_⟩
  intro x
  obtain ⟨u, hu, hAu⟩ := A.mem_graph_iff.mp x.property.1
  change (u : H) = (x : WithLp 2 (H × K)).fst at hu
  change A u = (x : WithLp 2 (H × K)).snd at hAu
  have hell : ell u = 0 := by
    rw [hu]
    exact x.property.2
  have hc := hcoer u hell
  have hn : ‖x‖ ^ 2 = ‖(u : H)‖ ^ 2 + ‖A u‖ ^ 2 := by
    change ‖(x : WithLp 2 (H × K))‖ ^ 2 = _
    rw [WithLp.prod_norm_sq_eq_of_L2]
    simp only [← hu, ← hAu]
  rw [energyForm_apply, real_inner_self_eq_norm_sq]
  have hg : gradientMap A ell x = A u := hAu.symm
  rw [hg]
  rw [mul_assoc, ← sq, div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < m + 1)]
  nlinarith

private def graphLift (A : H →ₗ.[ℝ] K) (ell : H →L[ℝ] ℝ)
    (u : A.domain) (hu : ell u = 0) : centeredGraph A ell :=
  ⟨WithLp.toLp 2 ((u : H), A u), ⟨A.mem_graph u, hu⟩⟩

/-- A closed operator coercive on a closed scalar constraint has a unique
zero-regularization weak solution on that constraint. -/
theorem existsUnique_centered_solution (A : H →ₗ.[ℝ] K) (hA : A.IsClosed)
    (ell : H →L[ℝ] ℝ) {m : ℝ} (hm : 0 < m)
    (hcoer : ∀ u : A.domain, ell u = 0 → m * ‖(u : H)‖ ^ 2 ≤ ‖A u‖ ^ 2)
    (f : H) :
    ∃! u : A.domain, ell u = 0 ∧ ∀ v : A.domain, ell v = 0 →
      inner ℝ (A u) (A v) = inner ℝ f (v : H) := by
  let : CompleteSpace (centeredGraph A ell) :=
    (centeredGraph_closed A hA ell).completeSpace_coe
  let B := energyForm A ell
  have hB : IsCoercive B := graph_coercive A ell hm hcoer
  let F : centeredGraph A ell →L[ℝ] ℝ := (innerSL ℝ f).comp (valueMap A ell)
  let rhs : centeredGraph A ell := (toDual ℝ (centeredGraph A ell)).symm F
  let x := hB.continuousLinearEquivOfBilin.symm rhs
  have hx (y : centeredGraph A ell) : B x y = F y := by
    rw [← hB.continuousLinearEquivOfBilin_apply, ContinuousLinearEquiv.apply_symm_apply]
    exact toDual_symm_apply
  obtain ⟨u, hu, hAu⟩ := A.mem_graph_iff.mp x.property.1
  change (u : H) = (x : WithLp 2 (H × K)).fst at hu
  change A u = (x : WithLp 2 (H × K)).snd at hAu
  have hell : ell u = 0 := by rw [hu]; exact x.property.2
  have hsol (v : A.domain) (hv : ell v = 0) :
      inner ℝ (A u) (A v) = inner ℝ f (v : H) := by
    have hh := hx (graphLift A ell v hv)
    change inner ℝ (x : WithLp 2 (H × K)).snd (A v) = inner ℝ f (v : H) at hh
    simpa only [← hAu] using hh
  refine ⟨u, ⟨hell, hsol⟩, ?_⟩
  intro w hw
  have hwx : hB.continuousLinearEquivOfBilin (graphLift A ell w hw.1) = rhs := by
    apply (toDual ℝ (centeredGraph A ell)).injective
    ext y
    rw [toDual_apply_apply, hB.continuousLinearEquivOfBilin_apply]
    obtain ⟨v, hv, hAv⟩ := A.mem_graph_iff.mp y.property.1
    change (v : H) = (y : WithLp 2 (H × K)).fst at hv
    change A v = (y : WithLp 2 (H × K)).snd at hAv
    have hellv : ell v = 0 := by rw [hv]; exact y.property.2
    change inner ℝ (A w) (y : WithLp 2 (H × K)).snd = (toDual ℝ (centeredGraph A ell)) rhs y
    rw [show (toDual ℝ (centeredGraph A ell)) rhs = F from LinearIsometryEquiv.apply_symm_apply _ _]
    change inner ℝ (A w) (y : WithLp 2 (H × K)).snd = inner ℝ f (y : WithLp 2 (H × K)).fst
    rw [← hv, ← hAv]
    exact hw.2 v hellv
  have heq : graphLift A ell w hw.1 = x :=
    hB.continuousLinearEquivOfBilin.injective (hwx.trans (hB.continuousLinearEquivOfBilin.apply_symm_apply rhs).symm)
  apply Subtype.ext
  have hh := congrArg (fun z : centeredGraph A ell => (z : WithLp 2 (H × K)).fst) heq
  exact hh.trans hu.symm

/-- A closed operator coercive on a closed scalar constraint has a unique
variational solution for a gradient-paired forcing on that constraint. -/
theorem existsUnique_centered_gradient_solution (A : H →ₗ.[ℝ] K) (hA : A.IsClosed)
    (ell : H →L[ℝ] ℝ) {m : ℝ} (hm : 0 < m)
    (hcoer : ∀ u : A.domain, ell u = 0 → m * ‖(u : H)‖ ^ 2 ≤ ‖A u‖ ^ 2)
    (f : K) :
    ∃! u : A.domain, ell u = 0 ∧ ∀ v : A.domain, ell v = 0 →
      inner ℝ (A u) (A v) = inner ℝ f (A v) := by
  let : CompleteSpace (centeredGraph A ell) :=
    (centeredGraph_closed A hA ell).completeSpace_coe
  let B := energyForm A ell
  have hB : IsCoercive B := graph_coercive A ell hm hcoer
  let F : centeredGraph A ell →L[ℝ] ℝ := (innerSL ℝ f).comp (gradientMap A ell)
  let rhs : centeredGraph A ell := (toDual ℝ (centeredGraph A ell)).symm F
  let x := hB.continuousLinearEquivOfBilin.symm rhs
  have hx (y : centeredGraph A ell) : B x y = F y := by
    rw [← hB.continuousLinearEquivOfBilin_apply, ContinuousLinearEquiv.apply_symm_apply]
    exact toDual_symm_apply
  obtain ⟨u, hu, hAu⟩ := A.mem_graph_iff.mp x.property.1
  change (u : H) = (x : WithLp 2 (H × K)).fst at hu
  change A u = (x : WithLp 2 (H × K)).snd at hAu
  have hell : ell u = 0 := by rw [hu]; exact x.property.2
  have hsol (v : A.domain) (hv : ell v = 0) :
      inner ℝ (A u) (A v) = inner ℝ f (A v) := by
    have hh := hx (graphLift A ell v hv)
    change inner ℝ (x : WithLp 2 (H × K)).snd (A v) = inner ℝ f (A v) at hh
    simpa only [← hAu] using hh
  refine ⟨u, ⟨hell, hsol⟩, ?_⟩
  intro w hw
  have hwx : hB.continuousLinearEquivOfBilin (graphLift A ell w hw.1) = rhs := by
    apply (toDual ℝ (centeredGraph A ell)).injective
    ext y
    rw [toDual_apply_apply, hB.continuousLinearEquivOfBilin_apply]
    obtain ⟨v, hv, hAv⟩ := A.mem_graph_iff.mp y.property.1
    change (v : H) = (y : WithLp 2 (H × K)).fst at hv
    change A v = (y : WithLp 2 (H × K)).snd at hAv
    have hellv : ell v = 0 := by rw [hv]; exact y.property.2
    change inner ℝ (A w) (y : WithLp 2 (H × K)).snd = (toDual ℝ (centeredGraph A ell)) rhs y
    rw [show (toDual ℝ (centeredGraph A ell)) rhs = F from LinearIsometryEquiv.apply_symm_apply _ _]
    change inner ℝ (A w) (y : WithLp 2 (H × K)).snd = inner ℝ f (y : WithLp 2 (H × K)).snd
    rw [← hAv]
    exact hw.2 v hellv
  have heq : graphLift A ell w hw.1 = x :=
    hB.continuousLinearEquivOfBilin.injective (hwx.trans (hB.continuousLinearEquivOfBilin.apply_symm_apply rhs).symm)
  apply Subtype.ext
  have hh := congrArg (fun z : centeredGraph A ell => (z : WithLp 2 (H × K)).fst) heq
  exact hh.trans hu.symm

omit [CompleteSpace H] [CompleteSpace K] in
/-- Sharp value and energy estimates for a centered weak solution. -/
theorem centered_solution_estimates (A : H →ₗ.[ℝ] K) (ell : H →L[ℝ] ℝ)
    {m : ℝ} (hm : 0 < m)
    (hcoer : ∀ u : A.domain, ell u = 0 → m * ‖(u : H)‖ ^ 2 ≤ ‖A u‖ ^ 2)
    (f : H) (u : A.domain) (hu : ell u = 0)
    (hsol : ∀ v : A.domain, ell v = 0 →
      inner ℝ (A u) (A v) = inner ℝ f (v : H)) :
    m * ‖(u : H)‖ ≤ ‖f‖ ∧ m * ‖A u‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  have he : ‖A u‖ ^ 2 ≤ ‖f‖ * ‖(u : H)‖ := by
    rw [← real_inner_self_eq_norm_sq, hsol u hu]
    exact real_inner_le_norm _ _
  have hc := hcoer u hu
  have hvalue : m * ‖(u : H)‖ ≤ ‖f‖ := by
    by_cases hz : ‖(u : H)‖ = 0
    · simp only [hz, mul_zero, norm_nonneg]
    · have hpos : 0 < ‖(u : H)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      nlinarith
  refine ⟨hvalue, ?_⟩
  have henergy := mul_le_mul_of_nonneg_left he hm.le
  have hfinal := mul_le_mul_of_nonneg_left hvalue (norm_nonneg f)
  nlinarith

end AcceleratedLogConcave.Analysis.Poisson
