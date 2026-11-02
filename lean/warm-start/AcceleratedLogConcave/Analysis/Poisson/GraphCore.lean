import AcceleratedLogConcave.Analysis.Poisson.Realization
import AcceleratedLogConcave.External.Samplinglib.TechnicalLemmas.FunctionalInequalities.GlobalWeightedResolventCoercivity

/-!
# A smooth core for the actual weighted generator

This retains the simultaneous value, gradient, and generator approximation
constructed inside the attributed Samplinglib compact/localization proofs.
The original proof provenance is recorded in the adjacent External/Samplinglib
NOTICE and PROVENANCE; only helper visibility was changed in those files.
-/
noncomputable section
open MeasureTheory Filter InnerProductSpace
open scoped ContDiff Topology RealInnerProductSpace Laplacian

namespace AcceleratedLogConcave.Analysis.Poisson
open WeightedGradient
open AutoSamplingTheory.TechnicalLemmas.FunctionalInequalities
open CompactWeightedPoissonCoercivity GlobalWeightedResolventCoercivity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Triples of compact smooth functions, their actual gradients, and their
positive weighted Laplacians. All entries are L2 equivalence classes. -/
def smoothGeneratorGraph (μ : Measure E) (V : E → ℝ) :
    Set (Lp ℝ 2 μ × Lp E 2 μ × Lp ℝ 2 μ) :=
  {p | ∃ φ : E → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
    p.1 =ᵐ[μ] φ ∧ p.2.1 =ᵐ[μ] gradient φ ∧
    p.2.2 =ᵐ[μ] (fun x => inner ℝ (gradient V x) (gradient φ x) - Laplacian.laplacian φ x)}

/-- Compactly supported genuine ordinary weak Poisson data admit simultaneous
weighted smooth approximation of value, gradient, and generator. -/
theorem compact_mem_generator_graph_closure
    (W : E → ℝ) (hW : ContDiff ℝ 2 W)
    (μ : Measure E) (hμ : μ = (volume : Measure E).tilted (fun x => -W x))
    (v F : E → ℝ) (G : E → E) (K : Set E) (hK : IsCompact K)
    (hv : tsupport v ⊆ K) (hF : tsupport F ⊆ K) (hG : tsupport G ⊆ K)
    (hv2 : MemLp v 2 volume) (hF2 : MemLp F 2 volume) (hG2 : MemLp G 2 volume)
    (hd : ∀ ψ : E → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∀ a : E,
      Integrable (fun x => ψ x * inner ℝ (G x) a) volume ∧
      Integrable (fun x => v x * fderiv ℝ ψ x a) volume ∧
      (∫ x, ψ x * inner ℝ (G x) a) = -∫ x, v x * fderiv ℝ ψ x a)
    (hweak : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      Integrable (fun x => v x * Laplacian.laplacian ψ x) volume ∧
      Integrable (fun x => F x * ψ x) volume ∧
      (∫ x, v x * Laplacian.laplacian ψ x) = ∫ x, F x * ψ x) :
    let A := fun x => inner ℝ (gradient W x) (G x)-F x
    ∃ hvW : MemLp v 2 μ, ∃ hGW : MemLp G 2 μ, ∃ hAW : MemLp A 2 μ,
      (hvW.toLp v, hGW.toLp G, hAW.toLp A) ∈ closure (smoothGeneratorGraph μ W) := by
  subst μ
  let μ := (volume : Measure E).tilted (fun x => -W x)
  obtain ⟨K',hK',φ,hφs,hφv,hφG,hφgrad,hφF⟩ :=
    CompactPoissonSmoothGraph.compact_weak_poisson_smooth_graph_approximation
      v F G K hK hv hF hG hv2 hF2 hG2 hd hweak
  let Kbar := K ∪ K'
  have hKb : IsCompact Kbar := hK.union hK'
  obtain ⟨c,hc,hdom⟩ := compact_weight_bound W hW.continuous Kbar hKb
  obtain ⟨M,hM,hMb⟩ := compact_drift_bound W hW Kbar hKb
  have hvs : Function.support v ⊆ Kbar := (subset_tsupport v).trans (hv.trans Set.subset_union_left)
  have hFs : Function.support F ⊆ Kbar := (subset_tsupport F).trans (hF.trans Set.subset_union_left)
  have hGs : Function.support G ⊆ Kbar := (subset_tsupport G).trans (hG.trans Set.subset_union_left)
  have hps (n : ℕ) : Function.support (φ n : E → ℝ) ⊆ Kbar :=
    (subset_tsupport _).trans ((hφs n).trans Set.subset_union_right)
  have hpgs (n : ℕ) : Function.support (gradient (φ n : E → ℝ)) ⊆ Kbar :=
    (gradient_support _).trans ((hφs n).trans Set.subset_union_right)
  have hpls (n : ℕ) : Function.support (Laplacian.laplacian (φ n : E → ℝ)) ⊆ Kbar :=
    (laplacian_support _).trans ((hφs n).trans Set.subset_union_right)
  have hpl2 (n : ℕ) : MemLp (Laplacian.laplacian (φ n : E → ℝ)) 2 volume := by
    have he : ((Δ (φ n) : SchwartzMap E ℝ) : E → ℝ) =
        Laplacian.laplacian (φ n : E → ℝ) := by
      funext x; exact SchwartzMap.laplacian_apply (φ n) x
    rw [← he]
    exact (Δ (φ n)).memLp 2 volume
  have hplT : Tendsto (fun n => (hpl2 n).toLp _) atTop (𝓝 (hF2.toLp F)) := by
    have he (n : ℕ) : (hpl2 n).toLp _ = (Δ (φ n)).toLp 2 volume := by
      apply Lp.ext
      filter_upwards [(hpl2 n).coeFn_toLp,(Δ (φ n)).coeFn_toLp 2 volume] with x hx hy
      rw [hx,hy,SchwartzMap.laplacian_apply]
    simpa only [he] using hφF
  obtain ⟨hvW,hpW,hpT⟩ := compact_convergence μ volume Kbar hKb.measurableSet c hc hdom
    v (fun n => (φ n : E → ℝ)) hvs hps hv2 (fun n => (φ n).memLp 2 volume) hφv
  obtain ⟨hGW,hpgW,hpgT⟩ := compact_convergence μ volume Kbar hKb.measurableSet c hc hdom
    G (fun n => gradient (φ n : E → ℝ)) hGs hpgs hG2 hφG hφgrad
  obtain ⟨hFW,hplW,hplWT⟩ := compact_convergence μ volume Kbar hKb.measurableSet c hc hdom
    F (fun n => Laplacian.laplacian (φ n : E → ℝ)) hFs hpls hF2 hpl2 hplT
  obtain ⟨hB,hBn,hBT⟩ := drift_convergence μ W hW Kbar M hM hMb
    G (fun n => gradient (φ n : E → ℝ)) hGs hpgs hGW hpgW hpgT
  have hAW : MemLp (fun x => inner ℝ (gradient W x) (G x)-F x) 2 μ := hB.sub hFW
  have hAn (n : ℕ) : MemLp (fun x => inner ℝ (gradient W x) (gradient (φ n : E → ℝ) x)-
      Laplacian.laplacian (φ n : E → ℝ) x) 2 μ := (hBn n).sub (hplW n)
  have hAT : Tendsto (fun n => (hAn n).toLp _) atTop (𝓝 (hAW.toLp _)) := by
    change Tendsto (fun n => (hBn n).toLp _-(hplW n).toLp _) atTop
      (𝓝 (hB.toLp _-hFW.toLp _))
    exact hBT.sub hplWT
  refine ⟨hvW, hGW, hAW, ?_⟩
  apply isClosed_closure.mem_of_tendsto (hpT.prodMk_nhds (hpgT.prodMk_nhds hAT))
  filter_upwards [] with n
  apply subset_closure
  exact ⟨φ n, (φ n).smooth ⊤, HasCompactSupport.of_support_subset_isCompact
    hK' ((subset_tsupport _).trans (hφs n)), (hpW n).coeFn_toLp,
    (hpgW n).coeFn_toLp, (hAn n).coeFn_toLp⟩

/-- Cutoff exhaustion promotes the local compact approximation to a global
generator graph approximation. The local data are the genuine localized PDE. -/
theorem mem_generator_graph_closure_of_localization [Nontrivial E]
    (W : E → ℝ) (hW : ContDiff ℝ 2 W)
    (m M : ℝ) (hm : 0 < m) (hmM : m ≤ M)
    (hl : ∀ x a, m*‖a‖^2 ≤ fderiv ℝ (fderiv ℝ W) x a a)
    (hu : ∀ x a, fderiv ℝ (fderiv ℝ W) x a a ≤ M*‖a‖^2)
    (μ : Measure E) (hμ : μ = (volume : Measure E).tilted (fun x => -W x))
    (u a : E → ℝ) (G : E → E)
    (hu2 : MemLp u 2 μ) (ha2 : MemLp a 2 μ) (hG2 : MemLp G 2 μ)
    (hlocal : ∀ χ : E → ℝ, ContDiff ℝ 2 χ → HasCompactSupport χ →
      let v := fun x => χ x*u x
      let Gχ := fun x => χ x • G x+u x • gradient χ x
      let Fχ := fun x => χ x*(inner ℝ (gradient W x) (G x)-a x)+
        2*inner ℝ (gradient χ x) (G x)+u x*Laplacian.laplacian χ x
      MemLp v 2 volume ∧ MemLp Gχ 2 volume ∧ MemLp Fχ 2 volume ∧
      tsupport v ⊆ tsupport χ ∧ tsupport Gχ ⊆ tsupport χ ∧ tsupport Fχ ⊆ tsupport χ ∧
      (∀ ψ : E → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∀ b : E,
        Integrable (fun x => ψ x * inner ℝ (Gχ x) b) volume ∧
        Integrable (fun x => v x * fderiv ℝ ψ x b) volume ∧
        (∫ x, ψ x * inner ℝ (Gχ x) b) = -∫ x, v x * fderiv ℝ ψ x b) ∧
      ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
        Integrable (fun x => v x * Laplacian.laplacian ψ x) volume ∧
        Integrable (fun x => Fχ x * ψ x) volume ∧
        (∫ x, v x * Laplacian.laplacian ψ x) = ∫ x, Fχ x * ψ x) :
    (hu2.toLp u, hG2.toLp G, ha2.toLp a) ∈ closure (smoothGeneratorGraph μ W) := by
  let χ := fun n : ℕ =>
    (AutoSamplingTheory.TechnicalLemmas.Analysis.Calculus.Cutoff.radialSmoothCutoff
      ((n:ℝ)+1) : E → ℝ)
  have hχ (n : ℕ) : ContDiff ℝ 2 (χ n) :=
    (AutoSamplingTheory.TechnicalLemmas.Analysis.Calculus.Cutoff.radialSmoothCutoff_contDiff
      (by positivity : (0:ℝ)<(n:ℝ)+1)).of_le
        (WithTop.coe_le_coe.mpr (le_top : (2:ℕ∞)≤⊤))
  have hc (n : ℕ) : HasCompactSupport (χ n) :=
    AutoSamplingTheory.TechnicalLemmas.Analysis.Calculus.Cutoff.radialSmoothCutoff_hasCompactSupport
      (by positivity)
  obtain ⟨hCU,hCUt⟩ := actual_cutoff_function_convergence μ u hu2
  obtain ⟨hCG,hCGt⟩ := actual_cutoff_function_convergence μ G hG2
  obtain ⟨hCA,hCAt⟩ := actual_cutoff_function_convergence μ a ha2
  obtain ⟨hGe,hAe,hAd,hGet,hAet,hAdt⟩ :=
    actual_cutoff_commutators μ W hW m M hm hmM hl hu u G hu2 hG2
  let hGn := fun n => (hCG n).add (hGe n)
  let hAn := fun n => ((hCA n).sub (hAe n)).add (hAd n)
  have hGt : Tendsto (fun n => (hGn n).toLp _) atTop (𝓝 (hG2.toLp G)) := by
    change Tendsto (fun n => (hCG n).toLp _+(hGe n).toLp _) atTop (𝓝 (hG2.toLp G))
    simpa only [add_zero] using hCGt.add hGet
  have hAt : Tendsto (fun n => (hAn n).toLp _) atTop (𝓝 (ha2.toLp a)) := by
    change Tendsto (fun n => ((hCA n).toLp _-(hAe n).toLp _)+(hAd n).toLp _)
      atTop (𝓝 (ha2.toLp a))
    simpa only [sub_zero,add_zero] using (hCAt.sub hAet).add hAdt
  apply isClosed_closure.mem_of_tendsto (hCUt.prodMk_nhds (hGt.prodMk_nhds hAt))
  filter_upwards [] with n
  obtain ⟨hv,hg,hF,hvs,hgs,hFs,hd,hp⟩ := hlocal (χ n) (hχ n) (hc n)
  obtain ⟨hUW,hGW,hAW,hcore⟩ := compact_mem_generator_graph_closure W hW μ hμ
    _ _ _ (tsupport (χ n)) (hc n) hvs hFs hgs hv hF hg hd hp
  have hUid : hUW.toLp _ = (hCU n).toLp _ := by
    apply Lp.ext
    filter_upwards [hUW.coeFn_toLp, (hCU n).coeFn_toLp] with x hx hy
    rw [hx, hy]
    rfl
  have hGid : hGW.toLp _ = (hGn n).toLp _ := by
    apply Lp.ext
    filter_upwards [hGW.coeFn_toLp, (hGn n).coeFn_toLp] with x hx hy
    rw [hx, hy]
    rfl
  have hAid : hAW.toLp _ = (hAn n).toLp _ := by
    apply Lp.ext
    filter_upwards [hAW.coeFn_toLp, (hAn n).coeFn_toLp] with x hx hy
    rw [hx,hy]
    simp only [Pi.add_apply,Pi.sub_apply,inner_add_right,real_inner_smul_right,
      smul_eq_mul]
    ring
  rwa [hUid, hGid, hAid] at hcore

/-- The actual weak Poisson solution belongs to the closure of the smooth
weighted generator graph. This auxiliary statement treats positive dimension. -/
theorem weak_poisson_mem_generator_graph_closure_of_nontrivial [Nontrivial E]
    (μ : Measure E) (V : E → ℝ) (hV : ContDiff ℝ 2 V)
    (hI : Integrable (fun x => Real.exp (-V x)))
    (hμ : μ = volume.tilted (fun x => -V x))
    (m L : ℝ) (hm : 0 < m)
    (hlower : ∀ x a, m * ‖a‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x a a)
    (hupper : ∀ x a, fderiv ℝ (fderiv ℝ V) x a a ≤ L * ‖a‖ ^ 2)
    (u : Sobolev μ V (hV.of_le (by norm_num)) hI hμ) (f : Lp ℝ 2 μ)
    (hu : ∀ v : Sobolev μ V (hV.of_le (by norm_num)) hI hμ,
      inner ℝ (closedGradient μ V (hV.of_le (by norm_num)) hI hμ u)
        (closedGradient μ V (hV.of_le (by norm_num)) hI hμ v) =
      inner ℝ f (v : Lp ℝ 2 μ)) :
    ((u : Lp ℝ 2 μ), closedGradient μ V (hV.of_le (by norm_num)) hI hμ u, f) ∈
      closure (smoothGeneratorGraph μ V) := by
  subst μ
  let μ := volume.tilted (fun x => -V x)
  let hV1 : ContDiff ℝ 1 V := hV.of_le (by norm_num)
  obtain ⟨w, hw, _, _, _, _, _, _, hcut⟩ :=
    LocalizedWeakResolvent.localized_weak_resolvent V hV1 hI
      (compactGradient μ V hV1 hI rfl) (compactGradient_closable μ V hV1 hI rfl)
      (mem_compactGradient_graph μ V hV1 hI rfl) 1 zero_lt_one (f + (u : Lp ℝ 2 μ))
  have hwu : w = u := by
    apply one_resolvent_unique (closedGradient μ V hV1 hI rfl) (f + (u : Lp ℝ 2 μ)) w u
    · intro v
      simpa only [one_mul, closedGradient] using hw v
    · intro v
      rw [inner_add_left, hu v, add_comm]
  subst w
  let a : E → ℝ := fun x => (f + (u : Lp ℝ 2 μ)) x - (u : Lp ℝ 2 μ) x
  have ha : MemLp a 2 μ := (Lp.memLp (f + (u : Lp ℝ 2 μ))).sub (Lp.memLp (u : Lp ℝ 2 μ))
  have haeq : ha.toLp a = f := by
    apply Lp.ext
    filter_upwards [ha.coeFn_toLp, Lp.coeFn_add f (u : Lp ℝ 2 μ)] with x hx hy
    rw [hx]
    change (f + (u : Lp ℝ 2 μ)) x - (u : Lp ℝ 2 μ) x = f x
    rw [hy]
    simp
  have hcore := mem_generator_graph_closure_of_localization V hV m (max m L) hm
    (le_max_left _ _) hlower
    (fun x a => (hupper x a).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))) μ rfl
    (fun x => (u : Lp ℝ 2 μ) x) a (fun x => closedGradient μ V hV1 hI rfl u x)
    (Lp.memLp (u : Lp ℝ 2 μ)) ha (Lp.memLp (closedGradient μ V hV1 hI rfl u)) (by
      intro χ hχ hc
      have heq : (fun x => inner ℝ (gradient V x) (closedGradient μ V hV1 hI rfl u x) - a x) =
          (fun x => 1 * (u : Lp ℝ 2 μ) x +
            inner ℝ (gradient V x) (closedGradient μ V hV1 hI rfl u x) -
              (f + (u : Lp ℝ 2 μ)) x) := by
        funext x
        dsimp [a]
        ring
      dsimp only
      simp_rw [show ∀ x, inner ℝ (gradient V x) (closedGradient μ V hV1 hI rfl u x) - a x =
        1 * (u : Lp ℝ 2 μ) x + inner ℝ (gradient V x)
          (closedGradient μ V hV1 hI rfl u x) - (f + (u : Lp ℝ 2 μ)) x from congrFun heq]
      exact hcut χ hχ hc)
  have huLp : (Lp.memLp (u : Lp ℝ 2 μ)).toLp (fun x => (u : Lp ℝ 2 μ) x) = u :=
    Lp.ext (Lp.memLp (u : Lp ℝ 2 μ)).coeFn_toLp
  have hGLp : (Lp.memLp (closedGradient μ V hV1 hI rfl u)).toLp
      (fun x => closedGradient μ V hV1 hI rfl u x) = closedGradient μ V hV1 hI rfl u :=
    Lp.ext (Lp.memLp (closedGradient μ V hV1 hI rfl u)).coeFn_toLp
  rwa [huLp, hGLp, haeq] at hcore

/-- Global smooth generator-core approximation for the actual weak solution,
including dimension zero. -/
theorem weak_poisson_mem_generator_graph_closure
    (μ : Measure E) (V : E → ℝ) (hV : ContDiff ℝ 2 V)
    (hI : Integrable (fun x => Real.exp (-V x)))
    (hμ : μ = volume.tilted (fun x => -V x))
    (m L : ℝ) (hm : 0 < m)
    (hlower : ∀ x a, m * ‖a‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x a a)
    (hupper : ∀ x a, fderiv ℝ (fderiv ℝ V) x a a ≤ L * ‖a‖ ^ 2)
    (u : Sobolev μ V (hV.of_le (by norm_num)) hI hμ) (f : Lp ℝ 2 μ)
    (hu : ∀ v : Sobolev μ V (hV.of_le (by norm_num)) hI hμ,
      inner ℝ (closedGradient μ V (hV.of_le (by norm_num)) hI hμ u)
        (closedGradient μ V (hV.of_le (by norm_num)) hI hμ v) =
      inner ℝ f (v : Lp ℝ 2 μ)) :
    ((u : Lp ℝ 2 μ), closedGradient μ V (hV.of_le (by norm_num)) hI hμ u, f) ∈
      closure (smoothGeneratorGraph μ V) := by
  classical
  cases subsingleton_or_nontrivial E with
  | inr hE =>
    let := hE
    exact weak_poisson_mem_generator_graph_closure_of_nontrivial μ V hV hI hμ m L hm hlower hupper u f hu
  | inl hE =>
    let := hE
    have hG (v : Sobolev μ V (hV.of_le (by norm_num)) hI hμ) :
        closedGradient μ V (hV.of_le (by norm_num)) hI hμ v = 0 := by
      apply Lp.ext
      exact Filter.Eventually.of_forall (fun _ => Subsingleton.elim _ _)
    have hfzero : f = 0 := by
      have hp : ∀ z : Lp ℝ 2 μ, inner ℝ f z = 0 :=
        (closedGradient_dense μ V (hV.of_le (by norm_num)) hI hμ).induction (by
            intro z hz
            have he := hu ⟨z, hz⟩
            rw [hG u, inner_zero_left] at he
            exact he.symm) (isClosed_eq (innerSL ℝ f).continuous continuous_const)
      exact (inner_self_eq_zero.mp (hp f))
    rw [hfzero, hG u]
    apply subset_closure
    refine ⟨fun _ => (u : Lp ℝ 2 μ) 0, contDiff_const, ?_, ?_, ?_, ?_⟩
    · exact HasCompactSupport.of_support_subset_isCompact (Set.finite_univ.isCompact)
        (Set.subset_univ _)
    · exact Filter.Eventually.of_forall (fun x => congrArg (fun x => (u : Lp ℝ 2 μ) x) (Subsingleton.elim x 0))
    · filter_upwards [Lp.coeFn_zero E 2 μ] with x hx
      simpa using hx
    · filter_upwards [Lp.coeFn_zero ℝ 2 μ] with x hx
      simpa using hx

end AcceleratedLogConcave.Analysis.Poisson
