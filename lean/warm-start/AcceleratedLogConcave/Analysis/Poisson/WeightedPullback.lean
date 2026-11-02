import AcceleratedLogConcave.Analysis.Poisson.Pullback
import AcceleratedLogConcave.Analysis.WeightedGradient.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Transport of the actual closed Sobolev domain

Composition by a C1 measure-preserving spatial diffeomorphism carries the
actual closed weighted gradient graph to the reference graph. The Jacobian
acts only when transforming the gradient, not in the unitary vector pullback.
-/
noncomputable section
open MeasureTheory InnerProductSpace Filter
open scoped ContDiff Topology RealInnerProductSpace
namespace AcceleratedLogConcave.Analysis.Poisson
open WeightedGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

section Field
variable (μ : Measure E) (A : E → E →L[ℝ] E) (hA : Continuous A)
  (M : ℝ) (hM : ∀ x, ‖A x‖ ≤ M)
include hA hM

private theorem field_memLp (G : Lp E 2 μ) : MemLp (fun x => A x (G x)) 2 μ := by
  apply (Lp.memLp G).of_le_mul
    ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hA.aestronglyMeasurable.prodMk (Lp.aestronglyMeasurable G)))
  exact Eventually.of_forall fun x => ((A x).le_opNorm (G x)).trans
    (mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _))

private def fieldAction (G : Lp E 2 μ) : Lp E 2 μ := (field_memLp μ A hA M hM G).toLp _
private theorem fieldAction_coe (G : Lp E 2 μ) :
    fieldAction μ A hA M hM G =ᵐ[μ] fun x => A x (G x) :=
  (field_memLp μ A hA M hM G).coeFn_toLp

/-- Multiplication by a continuous uniformly bounded spatial matrix field. -/
def fieldMultiplier : Lp E 2 μ →L[ℝ] Lp E 2 μ := LinearMap.mkContinuous
  { toFun := fieldAction μ A hA M hM
    map_add' := by
      intro G F
      apply Lp.ext
      filter_upwards [fieldAction_coe μ A hA M hM (G + F), fieldAction_coe μ A hA M hM G,
        fieldAction_coe μ A hA M hM F, Lp.coeFn_add G F,
        Lp.coeFn_add (fieldAction μ A hA M hM G) (fieldAction μ A hA M hM F)] with x h1 h2 h3 h4 h5
      simp only [h1, h4, h5, Pi.add_apply, h2, h3, map_add]
    map_smul' := by
      intro c G
      apply Lp.ext
      filter_upwards [fieldAction_coe μ A hA M hM (c • G), fieldAction_coe μ A hA M hM G,
        Lp.coeFn_smul c G, Lp.coeFn_smul c (fieldAction μ A hA M hM G)] with x h1 h2 h3 h4
      simp only [RingHom.id_apply, h1, h3, h4, Pi.smul_apply, h2, map_smul] }
  M (fun G => Lp.norm_le_mul_norm_of_ae_le_mul (by
    filter_upwards [fieldAction_coe μ A hA M hM G] with x hx
    change ‖(fieldAction μ A hA M hM G) x‖ ≤ M * ‖G x‖
    rw [hx]
    exact ((A x).le_opNorm (G x)).trans
      (mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _))))

theorem fieldMultiplier_coe (G : Lp E 2 μ) :
    fieldMultiplier μ A hA M hM G =ᵐ[μ] fun x => A x (G x) := fieldAction_coe μ A hA M hM G
theorem fieldMultiplier_norm_le : ‖fieldMultiplier μ A hA M hM‖ ≤ M :=
  LinearMap.mkContinuous_norm_le _ ((norm_nonneg (A 0)).trans (hM 0)) _
end Field

omit [MeasurableSpace E] [BorelSpace E] in
/-- Ordinary C1 chain rule in the gradient/adjoint convention. -/
theorem gradient_comp_adjoint (f : E → ℝ) (Φ : E → E)
    (hf : Differentiable ℝ f) (hΦ : Differentiable ℝ Φ) (x : E) :
    gradient (f ∘ Φ) x = (fderiv ℝ Φ x).adjoint (gradient f (Φ x)) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, fderiv_comp x (hf (Φ x)) (hΦ x), ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left, inner_gradient_left]

section Transport
variable (μ ν : Measure E) (U V : E → ℝ)
  (hU : ContDiff ℝ 1 U) (hV : ContDiff ℝ 1 V)
  (hIU : Integrable (fun x => Real.exp (-U x))) (hIV : Integrable (fun x => Real.exp (-V x)))
  (hμ : μ = volume.tilted (fun x => -U x)) (hν : ν = volume.tilted (fun x => -V x))
  (e : E ≃ₜ E) (he : MeasurePreserving e μ ν) (heC : ContDiff ℝ 1 e)
  (M : ℝ) (hM : ∀ x, ‖fderiv ℝ e x‖ ≤ M)

/-- The transpose Jacobian as an actual bounded multiplier on reference L2. -/
def jacobianAdjointMultiplier : Lp E 2 μ →L[ℝ] Lp E 2 μ :=
  fieldMultiplier μ (fun x => (fderiv ℝ e x).adjoint)
    (ContinuousLinearMap.adjoint.continuous.comp (heC.continuous_fderiv one_ne_zero)) M
    (fun x => by simpa using hM x)

/-- A compact smooth graph pair transforms by the actual C1 chain rule. -/
theorem compact_graph_pullback (u : Lp ℝ 2 ν) (G : Lp E 2 ν)
    (hgraph : (u, G) ∈ (compactGradient ν V hV hIV hν).graph) :
    (pullback e.toMeasurableEquiv he u,
      jacobianAdjointMultiplier μ e heC M hM (pullback e.toMeasurableEquiv he G)) ∈
        (closedGradient μ U hU hIU hμ).graph := by
  let : IsProbabilityMeasure μ := hμ ▸ isProbabilityMeasure_tilted hIU
  obtain ⟨φ, hφ, hc, hu, hG⟩ := (mem_compactGradient_graph ν V hV hIV hν u G).mp hgraph
  have hp : pullback e.toMeasurableEquiv he u =ᵐ[μ] (φ ∘ e) := by
    filter_upwards [pullback_coeFn e.toMeasurableEquiv he u, he.quasiMeasurePreserving.ae hu] with x hx hy
    exact hx.trans hy
  have hq : jacobianAdjointMultiplier μ e heC M hM (pullback e.toMeasurableEquiv he G) =ᵐ[μ]
      gradient (φ ∘ e) := by
    filter_upwards [fieldMultiplier_coe μ (fun x => (fderiv ℝ e x).adjoint)
      (ContinuousLinearMap.adjoint.continuous.comp (heC.continuous_fderiv one_ne_zero)) M
      (fun x => by simpa using hM x) (pullback e.toMeasurableEquiv he G),
      pullback_coeFn e.toMeasurableEquiv he G, he.quasiMeasurePreserving.ae hG] with x hx hy hz
    change (pullback e.toMeasurableEquiv he G) x = G (e x) at hy
    rw [gradient_comp_adjoint φ e (hφ.differentiable (by simp)) (heC.differentiable one_ne_zero),
      ← hz, ← hy]
    exact hx
  have hφp : MemLp (φ ∘ e) 2 μ := (memLp_congr_ae hp).mp (Lp.memLp (pullback e.toMeasurableEquiv he u))
  have hφq : MemLp (gradient (φ ∘ e)) 2 μ :=
    (memLp_congr_ae hq).mp
      (Lp.memLp (jacobianAdjointMultiplier μ e heC M hM (pullback e.toMeasurableEquiv he G)))
  have h := c1_mem_closedGradient_graph μ U hU hIU hμ
    ((hφ.of_le (by simp) : ContDiff ℝ 1 φ).comp heC) hφp hφq
  have hpEq : hφp.toLp (φ ∘ e) = pullback e.toMeasurableEquiv he u :=
    Lp.ext (hφp.coeFn_toLp.trans hp.symm)
  have hqEq : hφq.toLp (gradient (φ ∘ e)) =
      jacobianAdjointMultiplier μ e heC M hM (pullback e.toMeasurableEquiv he G) :=
    Lp.ext (hφq.coeFn_toLp.trans hq.symm)
  rwa [hpEq, hqEq] at h

/-- Transport of the complete closed weighted gradient graph. No smooth
representative is imposed on the domain element. -/
theorem closed_graph_pullback (u : Lp ℝ 2 ν) (G : Lp E 2 ν)
    (hgraph : (u, G) ∈ (closedGradient ν V hV hIV hν).graph) :
    (pullback e.toMeasurableEquiv he u,
      jacobianAdjointMultiplier μ e heC M hM (pullback e.toMeasurableEquiv he G)) ∈
        (closedGradient μ U hU hIU hμ).graph := by
  rw [closedGradient_graph_eq] at hgraph
  change (u, G) ∈ closure ((compactGradient ν V hV hIV hν).graph : Set _) at hgraph
  obtain ⟨p, hp, ht⟩ := mem_closure_iff_seq_limit.mp hgraph
  have hpull : Continuous (fun p : Lp ℝ 2 ν × Lp E 2 ν =>
      (pullback e.toMeasurableEquiv he p.1,
        jacobianAdjointMultiplier μ e heC M hM (pullback e.toMeasurableEquiv he p.2))) :=
    ((pullback e.toMeasurableEquiv he).continuous.comp continuous_fst).prodMk
      ((jacobianAdjointMultiplier μ e heC M hM).continuous.comp
        ((pullback e.toMeasurableEquiv he).continuous.comp continuous_snd))
  apply (closedGradient_isClosed μ U hU hIU hμ).mem_of_tendsto ((hpull.tendsto _).comp ht)
  exact Eventually.of_forall (fun n => compact_graph_pullback μ ν U V hU hV hIU hIV hμ hν e he heC M hM
    (p n).1 (p n).2 (hp n))
include heC hM in
/-- A C1 diffeomorphism with bounded forward and inverse derivatives transports
exactly the genuine Sobolev domains. Thus the pulled-back family has a common
domain once its spatial transport maps satisfy these geometric bounds. -/
theorem sobolev_pullback_iff (heInv : ContDiff ℝ 1 e.symm)
    (N : ℝ) (hN : ∀ x, ‖fderiv ℝ e.symm x‖ ≤ N) (u : Lp ℝ 2 ν) :
    u ∈ (closedGradient ν V hV hIV hν).domain ↔
      pullback e.toMeasurableEquiv he u ∈ (closedGradient μ U hU hIU hμ).domain := by
  constructor
  · intro hu
    exact LinearPMap.mem_domain_of_mem_graph
      (closed_graph_pullback μ ν U V hU hV hIU hIV hμ hν e he heC M hM u
        (closedGradient ν V hV hIV hν ⟨u, hu⟩)
        ((closedGradient ν V hV hIV hν).mem_graph ⟨u, hu⟩))
  · intro hu
    have heRev : MeasurePreserving e.symm ν μ := MeasurePreserving.symm e.toMeasurableEquiv he
    have hback := closed_graph_pullback ν μ V U hV hU hIV hIU hν hμ
      e.symm heRev heInv N hN (pullback e.toMeasurableEquiv he u)
        (closedGradient μ U hU hIU hμ ⟨pullback e.toMeasurableEquiv he u, hu⟩)
        ((closedGradient μ U hU hIU hμ).mem_graph ⟨pullback e.toMeasurableEquiv he u, hu⟩)
    have hcancel : pullback e.symm.toMeasurableEquiv heRev
        (pullback e.toMeasurableEquiv he u) = u := by
      change Lp.compMeasurePreserving e.symm heRev (Lp.compMeasurePreserving e he u) = u
      rw [← Lp.compMeasurePreserving_comp_apply]
      simp only [Homeomorph.self_comp_symm, Lp.compMeasurePreserving_id_apply]
    rw [hcancel] at hback
    exact LinearPMap.mem_domain_of_mem_graph hback

end Transport
end AcceleratedLogConcave.Analysis.Poisson
