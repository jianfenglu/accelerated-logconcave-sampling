import AcceleratedLogConcave.Analysis.Poisson.Centered
import AcceleratedLogConcave.External.Samplinglib.TechnicalLemmas.FunctionalInequalities.OrdinaryWeakResolvent

/-!
# Operator and differential realization of a weak Poisson solution

The abstract adjoint is Mathlib's densely defined partial-operator adjoint.
The distributional differential expression is recovered from the already proved
positive resolvent at parameter one and forcing `f + u`, using uniqueness.
No differentiability of the L2 forcing is assumed.
-/

noncomputable section
open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace LinearPMap

namespace AcceleratedLogConcave.Analysis.Poisson
open WeightedGradient

section Abstract
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- The variational equation is exactly membership in the operator `D*D`. -/
theorem weak_iff_adjoint (D : H →ₗ.[ℝ] K) (hD : Dense (D.domain : Set H))
    (u : D.domain) (f : H) :
    (∀ v : D.domain, inner ℝ (D u) (D v) = inner ℝ f (v : H)) ↔
      ∃ h : D u ∈ D.adjoint.domain, D.adjoint ⟨D u, h⟩ = f := by
  constructor
  · intro hu
    have hd := D.mem_adjoint_domain_of_exists (D u) ⟨f, fun v => (hu v).symm⟩
    exact ⟨hd, LinearPMap.adjoint_apply_eq hD _ (fun v => (hu v).symm)⟩
  · rintro ⟨h, he⟩ v
    have hi := LinearPMap.adjoint_isFormalAdjoint hD ⟨D u, h⟩ v
    rw [he] at hi
    exact hi.symm

omit [CompleteSpace H] in
/-- Uniqueness for the positive resolvent, without any centering assumption. -/
theorem one_resolvent_unique (D : H →ₗ.[ℝ] K) (f : H) (u w : D.domain)
    (hu : ∀ v : D.domain, inner ℝ (u : H) (v : H) + inner ℝ (D u) (D v) =
      inner ℝ f (v : H))
    (hw : ∀ v : D.domain, inner ℝ (w : H) (v : H) + inner ℝ (D w) (D v) =
      inner ℝ f (v : H)) : u = w := by
  have h := sub_eq_zero.mpr ((hu (u - w)).trans (hw (u - w)).symm)
  simp only [Submodule.coe_sub, D.map_sub, inner_sub_right] at h
  have he : ‖((u : H) - (w : H))‖ ^ 2 + ‖D (u - w)‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    rw [D.map_sub]
    simp only [inner_sub_left, inner_sub_right] at h ⊢
    linear_combination h
  apply Subtype.ext
  have hn : ‖((u : H) - (w : H))‖ = 0 := by
    nlinarith [sq_nonneg (‖D (u - w)‖), norm_nonneg ((u : H) - (w : H))]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)
end Abstract

section Weighted
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) (V : E → ℝ)
  (hV : ContDiff ℝ 1 V) (hI : Integrable (fun x => Real.exp (-V x)))
  (hμ : μ = volume.tilted (fun x => -V x))

/-- The actual weighted weak equation identifies the actual adjoint domain. -/
theorem weak_poisson_adjoint (u : Sobolev μ V hV hI hμ) (f : Lp ℝ 2 μ)
    (hu : ∀ v : Sobolev μ V hV hI hμ,
      inner ℝ (closedGradient μ V hV hI hμ u) (closedGradient μ V hV hI hμ v) =
        inner ℝ f (v : Lp ℝ 2 μ)) :
    ∃ h : closedGradient μ V hV hI hμ u ∈ (closedGradient μ V hV hI hμ).adjoint.domain,
      (closedGradient μ V hV hI hμ).adjoint ⟨closedGradient μ V hV hI hμ u, h⟩ = f :=
  (weak_iff_adjoint _ (closedGradient_dense μ V hV hI hμ) u f).mp hu

/-- The actual solution has its genuine ordinary weak gradient and solves
`Δu = ∇V · Du - f` distributionally. This remains meaningful for arbitrary L2
forcing; no derivative of `f` appears. -/
theorem weak_poisson_differential (u : Sobolev μ V hV hI hμ) (f : Lp ℝ 2 μ)
    (hu : ∀ v : Sobolev μ V hV hI hμ,
      inner ℝ (closedGradient μ V hV hI hμ u) (closedGradient μ V hV hI hμ v) =
        inner ℝ f (v : Lp ℝ 2 μ)) :
    LocallyIntegrable (fun x => (u : Lp ℝ 2 μ) x) ∧
    LocallyIntegrable (fun x => closedGradient μ V hV hI hμ u x) ∧
    (∀ ψ : E → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∀ v : E,
      Integrable (fun x => ψ x * inner ℝ (closedGradient μ V hV hI hμ u x) v) ∧
      Integrable (fun x => (u : Lp ℝ 2 μ) x * fderiv ℝ ψ x v) ∧
      (∫ x, ψ x * inner ℝ (closedGradient μ V hV hI hμ u x) v) =
        -∫ x, (u : Lp ℝ 2 μ) x * fderiv ℝ ψ x v) ∧
    ∀ φ : E → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      Integrable (fun x => (u : Lp ℝ 2 μ) x * Laplacian.laplacian φ x) ∧
      Integrable (fun x => (inner ℝ (gradient V x)
        (closedGradient μ V hV hI hμ u x) - f x) * φ x) ∧
      (∫ x, (u : Lp ℝ 2 μ) x * Laplacian.laplacian φ x) =
        ∫ x, (inner ℝ (gradient V x) (closedGradient μ V hV hI hμ u x) - f x) * φ x := by
  subst μ
  let μ := volume.tilted (fun x => -V x)
  obtain ⟨w, hw, hwL, hDwL, hd, _, _, hlap⟩ :=
    AutoSamplingTheory.TechnicalLemmas.FunctionalInequalities.OrdinaryWeakResolvent.weak_resolvent_laplacian
      V hV hI (compactGradient μ V hV hI rfl)
      (compactGradient_closable μ V hV hI rfl)
      (mem_compactGradient_graph μ V hV hI rfl) 1 zero_lt_one (f + (u : Lp ℝ 2 μ))
  have hwu : w = u := by
    apply one_resolvent_unique (closedGradient μ V hV hI rfl) (f + (u : Lp ℝ 2 μ)) w u
    · intro v
      simpa only [one_mul, closedGradient] using hw v
    · intro v
      rw [inner_add_left, hu v, add_comm]
  subst w
  refine ⟨hwL, hDwL, hd, ?_⟩
  intro φ hφ hc
  obtain ⟨h1, h2, h3⟩ := hlap φ hφ hc
  have hae : (fun x => (1 * (u : Lp ℝ 2 μ) x + inner ℝ (gradient V x)
      (closedGradient μ V hV hI rfl u x) - (f + (u : Lp ℝ 2 μ)) x) * φ x) =ᵐ[volume]
      (fun x => (inner ℝ (gradient V x) (closedGradient μ V hV hI rfl u x) - f x) * φ x) := by
    have hadd := Lp.coeFn_add f (u : Lp ℝ 2 μ)
    have hvol : volume ≪ μ := by
      exact absolutelyContinuous_tilted hI
    filter_upwards [hvol.ae_le hadd] with x hx
    rw [hx]
    simp only [Pi.add_apply]
    ring
  exact ⟨h1, h2.congr hae, h3.trans (integral_congr_ae hae)⟩
end Weighted
end AcceleratedLogConcave.Analysis.Poisson
