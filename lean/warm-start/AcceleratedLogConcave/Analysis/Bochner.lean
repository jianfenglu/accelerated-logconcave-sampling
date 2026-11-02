import AcceleratedLogConcave.Analysis.Poisson.GraphCore
import AcceleratedLogConcave.Analysis.Poisson.HessianMultiplier

/-!
# Bochner estimates on the weighted generator core

The Hessian is represented by the genuine gradients of directional derivatives
in a fixed orthonormal basis. The graph-core theorem supplies approximation of
actual Poisson solutions in value, gradient, and generator simultaneously.
-/
noncomputable section
open MeasureTheory InnerProductSpace Filter
open scoped ContDiff RealInnerProductSpace Topology

namespace AcceleratedLogConcave.Analysis.Poisson
open WeightedGradient
open AutoSamplingTheory.TechnicalLemmas.FunctionalInequalities

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The directional first derivative used for a Hessian row. -/
def directional (φ : E → ℝ) (b : E) : E → ℝ := fun x => fderiv ℝ φ x b

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem directional_smooth {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (b : E) :
    ContDiff ℝ ∞ (directional φ b) := by
  exact (hφ.fderiv_right (by simp)).clm_apply contDiff_const

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem directional_compact {φ : E → ℝ} (hφ : HasCompactSupport φ) (b : E) :
    HasCompactSupport (directional φ b) := hφ.fderiv_apply ℝ b

/-- Genuine compact C1 gradients are square integrable under every finite law. -/
theorem compact_gradient_memLp (μ : Measure E) [IsFiniteMeasure μ]
    {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    MemLp (gradient φ) 2 μ := by
  have hcont : Continuous (gradient φ) :=
    (toDual ℝ E).symm.continuous.comp (hφ.continuous_fderiv one_ne_zero)
  apply hcont.memLp_of_hasCompactSupport
  exact HasCompactSupport.of_support_subset_isCompact hc.isCompact
    (CompactWeightedPoissonCoercivity.gradient_support φ)

/-- The Hessian row of a compact smooth scalar function, as an actual L2 class. -/
def smoothHessianRow (μ : Measure E) [IsFiniteMeasure μ]
    (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (b : E) : Lp E 2 μ :=
  (compact_gradient_memLp μ ((directional_smooth hφ b).of_le (by simp))
    (directional_compact hc b)).toLp (gradient (directional φ b))

theorem smoothHessianRow_coeFn (μ : Measure E) [IsFiniteMeasure μ]
    (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (b : E) :
    smoothHessianRow μ φ hφ hc b =ᵐ[μ] gradient (directional φ b) :=
  MemLp.coeFn_toLp _

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
private theorem norm_sq_Lp {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (μ : Measure E) (v : Lp F 2 μ) : ‖v‖ ^ 2 = ∫ x, ‖v x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

/-- The full normalized compact Bochner equality, with its Hessian term retained. -/
theorem smooth_bochner_identity (μ : Measure E) [IsFiniteMeasure μ]
    (V : E → ℝ) (hV : ContDiff ℝ 2 V)
    (hμ : μ = volume.tilted (fun x => -V x))
    (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (a : Lp ℝ 2 μ)
    (ha : a =ᵐ[μ] (fun x => inner ℝ (gradient V x) (gradient φ x) - Laplacian.laplacian φ x)) :
    ‖a‖ ^ 2 =
      (∑ i, ‖smoothHessianRow μ φ hφ hc ((stdOrthonormalBasis ℝ E) i)‖ ^ 2) +
      ∫ x, fderiv ℝ (fderiv ℝ V) x (gradient φ x) (gradient φ x) ∂μ := by
  obtain ⟨_, _, _, _, hid, _⟩ := WeightedBochner.integrated_bochner_identity V φ hV hφ hc
  have htilt (g : E → ℝ) : (∫ x, g x ∂μ) =
      (∫ x, Real.exp (-V x))⁻¹ * ∫ x, Real.exp (-V x) * g x := by
    rw [hμ, integral_tilted, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [smul_eq_mul, div_eq_mul_inv]
    ring
  have hnorm : ‖a‖ ^ 2 = ∫ x,
      (Laplacian.laplacian φ x - inner ℝ (gradient V x) (gradient φ x)) ^ 2 ∂μ := by
    rw [norm_sq_Lp]
    apply integral_congr_ae
    filter_upwards [ha] with x hx
    rw [hx, Real.norm_eq_abs, sq_abs]
    ring
  have hrows : (∑ i, ‖smoothHessianRow μ φ hφ hc ((stdOrthonormalBasis ℝ E) i)‖ ^ 2) =
      ∫ x, ∑ i, ‖gradient (directional φ ((stdOrthonormalBasis ℝ E) i)) x‖ ^ 2 ∂μ := by
    have hi (i : Fin (Module.finrank ℝ E)) :
        Integrable (fun x => ‖gradient (directional φ ((stdOrthonormalBasis ℝ E) i)) x‖ ^ 2) μ :=
      (memLp_two_iff_integrable_sq_norm
        (compact_gradient_memLp μ ((directional_smooth hφ _).of_le (by simp))
          (directional_compact hc _)).aestronglyMeasurable).mp
        (compact_gradient_memLp μ ((directional_smooth hφ _).of_le (by simp))
          (directional_compact hc _))
    rw [integral_finsetSum _ (fun i _ => hi i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [norm_sq_Lp]
    apply integral_congr_ae
    filter_upwards [smoothHessianRow_coeFn μ φ hφ hc ((stdOrthonormalBasis ℝ E) i)] with x hx
    rw [hx]
  rw [hnorm, hrows, htilt, htilt, htilt, hid]
  change (∫ x, Real.exp (-V x))⁻¹ * (_ + _) =
    (∫ x, Real.exp (-V x))⁻¹ * (∫ x, Real.exp (-V x) *
      ∑ i, ‖gradient (fun z => fderiv ℝ φ z ((stdOrthonormalBasis ℝ E) i)) x‖ ^ 2) +
    (∫ x, Real.exp (-V x))⁻¹ * (∫ x, Real.exp (-V x) *
      fderiv ℝ (fderiv ℝ V) x (gradient φ x) (gradient φ x))
  ring

/-- Each Hessian row is controlled by the generator, without a spectral-gap
factor. This estimate also applies to differences of compact smooth functions. -/
theorem smoothHessianRow_norm_le (μ : Measure E) [IsFiniteMeasure μ]
    (V : E → ℝ) (hV : ContDiff ℝ 2 V)
    (hμ : μ = volume.tilted (fun x => -V x))
    (hlower : ∀ x v, 0 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (a : Lp ℝ 2 μ)
    (ha : a =ᵐ[μ] (fun x => inner ℝ (gradient V x) (gradient φ x) - Laplacian.laplacian φ x))
    (i : Fin (Module.finrank ℝ E)) :
    ‖smoothHessianRow μ φ hφ hc ((stdOrthonormalBasis ℝ E) i)‖ ≤ ‖a‖ := by
  have he := smooth_bochner_identity μ V hV hμ φ hφ hc a ha
  have hsum : ‖smoothHessianRow μ φ hφ hc ((stdOrthonormalBasis ℝ E) i)‖ ^ 2 ≤
      ∑ j, ‖smoothHessianRow μ φ hφ hc ((stdOrthonormalBasis ℝ E) j)‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖smoothHessianRow μ φ hφ hc ((stdOrthonormalBasis ℝ E) j)‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hcurv : 0 ≤ ∫ x, fderiv ℝ (fderiv ℝ V) x (gradient φ x) (gradient φ x) ∂μ :=
    integral_nonneg (fun x => hlower x (gradient φ x))
  nlinarith [norm_nonneg a, norm_nonneg (smoothHessianRow μ φ hφ hc ((stdOrthonormalBasis ℝ E) i))]

omit [MeasurableSpace E] [BorelSpace E] in
private theorem gradient_sub_eq {φ ψ : E → ℝ}
    (hφ : Differentiable ℝ φ) (hψ : Differentiable ℝ ψ) :
    gradient (φ - ψ) = fun x => gradient φ x - gradient ψ x := by
  funext x
  simp only [gradient, fderiv_sub (hφ x) (hψ x), map_sub]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem directional_sub_eq {φ ψ : E → ℝ}
    (hφ : Differentiable ℝ φ) (hψ : Differentiable ℝ ψ) (b : E) :
    directional (φ - ψ) b = directional φ b - directional ψ b := by
  funext x
  simp only [directional, fderiv_sub (hφ x) (hψ x), Pi.sub_apply]
  rfl

/-- Hessian rows respect subtraction as L2 equivalence classes. -/
theorem smoothHessianRow_sub (μ : Measure E) [IsFiniteMeasure μ]
    (φ ψ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ)
    (hcφ : HasCompactSupport φ) (hcψ : HasCompactSupport ψ) (b : E) :
    smoothHessianRow μ (φ - ψ) (hφ.sub hψ) (hcφ.sub hcψ) b =
      smoothHessianRow μ φ hφ hcφ b - smoothHessianRow μ ψ hψ hcψ b := by
  apply Lp.ext
  filter_upwards [smoothHessianRow_coeFn μ (φ - ψ) (hφ.sub hψ) (hcφ.sub hcψ) b,
    smoothHessianRow_coeFn μ φ hφ hcφ b, smoothHessianRow_coeFn μ ψ hψ hcψ b,
    Lp.coeFn_sub (smoothHessianRow μ φ hφ hcφ b) (smoothHessianRow μ ψ hψ hcψ b)] with x hx hy hz hw
  rw [hx, hw, Pi.sub_apply, hy, hz, directional_sub_eq (hφ.differentiable (by simp)) (hψ.differentiable (by simp))]
  rw [gradient_sub_eq ((directional_smooth hφ b).differentiable (by simp))
    ((directional_smooth hψ b).differentiable (by simp))]

omit [BorelSpace E] in
/-- Generator representatives respect subtraction. -/
theorem generator_sub_ae (μ : Measure E) (V : E → ℝ)
    (φ ψ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ)
    (a b : Lp ℝ 2 μ)
    (ha : a =ᵐ[μ] (fun x => inner ℝ (gradient V x) (gradient φ x) - Laplacian.laplacian φ x))
    (hb : b =ᵐ[μ] (fun x => inner ℝ (gradient V x) (gradient ψ x) - Laplacian.laplacian ψ x)) :
    a - b =ᵐ[μ] (fun x => inner ℝ (gradient V x) (gradient (φ - ψ) x) -
      Laplacian.laplacian (φ - ψ) x) := by
  filter_upwards [Lp.coeFn_sub a b, ha, hb] with x hx hy hz
  rw [hx, Pi.sub_apply, hy, hz, gradient_sub_eq (hφ.differentiable (by simp)) (hψ.differentiable (by simp))]
  rw [((hφ.of_le (by simp) : ContDiff ℝ 2 φ).contDiffAt).laplacian_sub
    ((hψ.of_le (by simp) : ContDiff ℝ 2 ψ).contDiffAt), inner_sub_right]
  ring

/-- Every generator-core approximation has convergent genuine Hessian rows.
The limit rows are closed gradients of the directional components of `G`. -/
theorem hessian_rows_of_generator_closure (μ : Measure E) [IsFiniteMeasure μ]
    (V : E → ℝ) (hV : ContDiff ℝ 2 V)
    (hI : Integrable (fun x => Real.exp (-V x)))
    (hμ : μ = volume.tilted (fun x => -V x))
    (hlower : ∀ x v, 0 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (u : Lp ℝ 2 μ) (G : Lp E 2 μ) (a : Lp ℝ 2 μ)
    (hcore : (u, G, a) ∈ closure (smoothGeneratorGraph μ V)) :
    ∃ p : ℕ → Lp ℝ 2 μ × Lp E 2 μ × Lp ℝ 2 μ,
      ∃ φ : ℕ → E → ℝ, ∃ hφ : ∀ n, ContDiff ℝ ∞ (φ n),
      ∃ hc : ∀ n, HasCompactSupport (φ n),
      (∀ n, (p n).1 =ᵐ[μ] φ n ∧ (p n).2.1 =ᵐ[μ] gradient (φ n) ∧
        (p n).2.2 =ᵐ[μ] (fun x => inner ℝ (gradient V x) (gradient (φ n) x) - Laplacian.laplacian (φ n) x)) ∧
      Tendsto p atTop (𝓝 (u, G, a)) ∧
      ∃ R : Fin (Module.finrank ℝ E) → Lp E 2 μ,
        (∀ i, Tendsto (fun n => smoothHessianRow μ (φ n) (hφ n) (hc n)
          ((stdOrthonormalBasis ℝ E) i)) atTop (𝓝 (R i))) ∧
        ∀ i, ((innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).compLp G, R i) ∈
          (closedGradient μ V (hV.of_le (by norm_num)) hI hμ).graph := by
  classical
  obtain ⟨p, hp, hpt⟩ := mem_closure_iff_seq_limit.mp hcore
  choose φ hφ hc hpφ hpG hpA using hp
  let r := fun n i => smoothHessianRow μ (φ n) (hφ n) (hc n) ((stdOrthonormalBasis ℝ E) i)
  have hAt : Tendsto (fun n => (p n).2.2) atTop (𝓝 a) :=
    ((continuous_snd.comp continuous_snd).tendsto _).comp hpt
  have hGt : Tendsto (fun n => (p n).2.1) atTop (𝓝 G) :=
    ((continuous_fst.comp continuous_snd).tendsto _).comp hpt
  have hA : CauchySeq (fun n => (p n).2.2) := hAt.cauchySeq
  have hR (i : Fin (Module.finrank ℝ E)) : CauchySeq (fun n => r n i) := by
    rw [Metric.cauchySeq_iff] at hA ⊢
    intro ε hε
    obtain ⟨N,hN⟩ := hA ε hε
    refine ⟨N, fun n hn k hk => ?_⟩
    have hb := smoothHessianRow_norm_le μ V hV hμ hlower (φ n - φ k)
      ((hφ n).sub (hφ k)) ((hc n).sub (hc k)) ((p n).2.2 - (p k).2.2)
      (generator_sub_ae μ V (φ n) (φ k) (hφ n) (hφ k) _ _ (hpA n) (hpA k)) i
    rw [smoothHessianRow_sub] at hb
    exact lt_of_le_of_lt (by simpa only [dist_eq_norm, r] using hb) (hN n hn k hk)
  choose R hRt using fun i => cauchySeq_tendsto_of_complete (hR i)
  refine ⟨p, φ, hφ, hc, fun n => ⟨hpφ n, hpG n, hpA n⟩, hpt, R, hRt, ?_⟩
  intro i
  let b := (stdOrthonormalBasis ℝ E) i
  have hq : Tendsto (fun n => (innerSL ℝ b).compLp ((p n).2.1)) atTop
      (𝓝 ((innerSL ℝ b).compLp G)) :=
    ((innerSL ℝ b).compLpL 2 μ).continuous.tendsto G |>.comp hGt
  apply (closedGradient_isClosed μ V (hV.of_le (by norm_num)) hI hμ).mem_of_tendsto
    (hq.prodMk_nhds (hRt i))
  filter_upwards [] with n
  rw [closedGradient_graph_eq]
  apply (compactGradient μ V (hV.of_le (by norm_num)) hI hμ).graph.le_topologicalClosure
  apply (mem_compactGradient_graph μ V (hV.of_le (by norm_num)) hI hμ _ _).mpr
  refine ⟨directional (φ n) b, directional_smooth (hφ n) b,
    directional_compact (hc n) b, ?_, smoothHessianRow_coeFn μ (φ n) (hφ n) (hc n) b⟩
  filter_upwards [(innerSL ℝ b).coeFn_compLp ((p n).2.1), hpG n] with x hx hy
  rw [hx, hy]
  exact inner_gradient_right

/-- Full Bochner identity on the closure of the genuine generator graph.
The Hessian rows are the closed gradients of the components of the actual
first gradient. No derivative of the forcing is required. -/
theorem bochner_of_generator_closure (μ : Measure E) [IsFiniteMeasure μ]
    (V : E → ℝ) (hV : ContDiff ℝ 2 V)
    (hI : Integrable (fun x => Real.exp (-V x)))
    (hμ : μ = volume.tilted (fun x => -V x))
    (m L : ℝ) (hm : 0 ≤ m)
    (hlower : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hupper : ∀ x v, fderiv ℝ (fderiv ℝ V) x v v ≤ L * ‖v‖ ^ 2)
    (u : Lp ℝ 2 μ) (G : Lp E 2 μ) (a : Lp ℝ 2 μ)
    (hcore : (u, G, a) ∈ closure (smoothGeneratorGraph μ V)) :
    ∃ R : Fin (Module.finrank ℝ E) → Lp E 2 μ,
      (∀ i, ((innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).compLp G, R i) ∈
        (closedGradient μ V (hV.of_le (by norm_num)) hI hμ).graph) ∧
      ‖a‖ ^ 2 = (∑ i, ‖R i‖ ^ 2) +
        inner ℝ (hessianMultiplier μ V hV m L hlower hupper G) G := by
  classical
  have hpos : ∀ x v, 0 ≤ fderiv ℝ (fderiv ℝ V) x v v :=
    fun x v => (mul_nonneg hm (sq_nonneg _)).trans (hlower x v)
  obtain ⟨p, φ, hφ, hc, hp, ht, R, hR, hgraph⟩ :=
    hessian_rows_of_generator_closure μ V hV hI hμ hpos u G a hcore
  refine ⟨R, hgraph, ?_⟩
  have hAt : Tendsto (fun n => (p n).2.2) atTop (𝓝 a) :=
    ((continuous_snd.comp continuous_snd).tendsto _).comp ht
  have hGt : Tendsto (fun n => (p n).2.1) atTop (𝓝 G) :=
    ((continuous_fst.comp continuous_snd).tendsto _).comp ht
  have hrows := tendsto_finsetSum Finset.univ (fun i _ => (hR i).norm.pow 2)
  have hcurv : Tendsto (fun n => inner ℝ
      (hessianMultiplier μ V hV m L hlower hupper ((p n).2.1)) ((p n).2.1)) atTop
      (𝓝 (inner ℝ (hessianMultiplier μ V hV m L hlower hupper G) G)) :=
    (((hessianMultiplier μ V hV m L hlower hupper).continuous.tendsto G).comp hGt).inner hGt
  have hids (n : ℕ) : ‖(p n).2.2‖ ^ 2 =
      (∑ i, ‖smoothHessianRow μ (φ n) (hφ n) (hc n) ((stdOrthonormalBasis ℝ E) i)‖ ^ 2) +
      inner ℝ (hessianMultiplier μ V hV m L hlower hupper ((p n).2.1)) ((p n).2.1) := by
    rw [smooth_bochner_identity μ V hV hμ (φ n) (hφ n) (hc n) _ (hp n).2.2,
      inner_hessianMultiplier]
    congr 1
    apply integral_congr_ae
    filter_upwards [(hp n).2.1] with x hx
    rw [hx]
  exact tendsto_nhds_unique (hAt.norm.pow 2) ((hrows.add hcurv).congr (fun n => (hids n).symm))

/-- Full Bochner equality for the actual weighted Poisson solution, with C2
potential and arbitrary centered or noncentered L2 forcing satisfying its weak
Poisson equation. Centering is only needed for existence and uniqueness. -/
theorem weak_poisson_bochner (μ : Measure E)
    (V : E → ℝ) (hV : ContDiff ℝ 2 V)
    (hI : Integrable (fun x => Real.exp (-V x)))
    (hμ : μ = volume.tilted (fun x => -V x))
    (m L : ℝ) (hm : 0 < m)
    (hlower : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hupper : ∀ x v, fderiv ℝ (fderiv ℝ V) x v v ≤ L * ‖v‖ ^ 2)
    (u : Sobolev μ V (hV.of_le (by norm_num)) hI hμ) (g : Lp ℝ 2 μ)
    (hu : ∀ v : Sobolev μ V (hV.of_le (by norm_num)) hI hμ,
      inner ℝ (closedGradient μ V (hV.of_le (by norm_num)) hI hμ u)
        (closedGradient μ V (hV.of_le (by norm_num)) hI hμ v) =
      inner ℝ g (v : Lp ℝ 2 μ)) :
    ∃ R : Fin (Module.finrank ℝ E) → Lp E 2 μ,
      (∀ i, ((innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).compLp
        (closedGradient μ V (hV.of_le (by norm_num)) hI hμ u), R i) ∈
        (closedGradient μ V (hV.of_le (by norm_num)) hI hμ).graph) ∧
      ‖g‖ ^ 2 = (∑ i, ‖R i‖ ^ 2) +
        inner ℝ (hessianMultiplier μ V hV m L hlower hupper
          (closedGradient μ V (hV.of_le (by norm_num)) hI hμ u))
            (closedGradient μ V (hV.of_le (by norm_num)) hI hμ u) := by
  let : IsProbabilityMeasure μ := hμ ▸ isProbabilityMeasure_tilted hI
  exact bochner_of_generator_closure μ V hV hI hμ m L hm.le hlower hupper _ _ _
    (weak_poisson_mem_generator_graph_closure μ V hV hI hμ m L hm hlower hupper u g hu)

/-- The curvature-weighted gradient of the actual Poisson solution has norm
at most the forcing norm when the upper Hessian bound is one. There is no
inverse power of the lower curvature in this estimate. -/
theorem weak_poisson_hessianGradient_norm_le (μ : Measure E)
    (V : E → ℝ) (hV : ContDiff ℝ 2 V)
    (hI : Integrable (fun x => Real.exp (-V x)))
    (hμ : μ = volume.tilted (fun x => -V x))
    (m : ℝ) (hm : 0 < m)
    (hlower : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hupper : ∀ x v, fderiv ℝ (fderiv ℝ V) x v v ≤ 1 * ‖v‖ ^ 2)
    (u : Sobolev μ V (hV.of_le (by norm_num)) hI hμ) (g : Lp ℝ 2 μ)
    (hu : ∀ v : Sobolev μ V (hV.of_le (by norm_num)) hI hμ,
      inner ℝ (closedGradient μ V (hV.of_le (by norm_num)) hI hμ u)
        (closedGradient μ V (hV.of_le (by norm_num)) hI hμ v) =
      inner ℝ g (v : Lp ℝ 2 μ)) :
    ‖hessianMultiplier μ V hV m 1 hlower hupper
      (closedGradient μ V (hV.of_le (by norm_num)) hI hμ u)‖ ≤ ‖g‖ := by
  obtain ⟨R, _, he⟩ := weak_poisson_bochner μ V hV hI hμ m 1 hm hlower hupper u g hu
  have hb := hessianMultiplier_norm_sq_le_curvature_of_bounds μ V hV m 1 hlower hupper
    (fun x v => (mul_nonneg hm.le (sq_nonneg _)).trans (hlower x v))
    (fun x v => by simpa only [one_mul] using hupper x v)
    (closedGradient μ V (hV.of_le (by norm_num)) hI hμ u)
  have hs : 0 ≤ ∑ i, ‖R i‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  nlinarith [norm_nonneg g,
    norm_nonneg (hessianMultiplier μ V hV m 1 hlower hupper
      (closedGradient μ V (hV.of_le (by norm_num)) hI hμ u))]

end AcceleratedLogConcave.Analysis.Poisson
