import DirectW12.GaussianHessianVector
import AcceleratedLogConcave.Kinetic.ReferenceFlow.GaussianDensity
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace Set Function
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.DirectW12
open Analysis.WeightedGradient Analysis.Poisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Gaussian Stein identity on the actual standard Gaussian, not a hypothesis. -/
theorem gaussian_compact_fderiv (f : E → ℝ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (v : E) :
    (∫ x, fderiv ℝ f x v ∂stdGaussian E) =
      ∫ x, inner ℝ v x * f x ∂stdGaussian E := by
  let d : E → ℝ := standardGaussianDensity
  have hd : ContDiff ℝ 1 d := standardGaussianDensity_contDiff
  have hi1 : Integrable (fun x => fderiv ℝ d x v * f x) :=
    (((hd.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul hf.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hi2 : Integrable (fun x => d x * fderiv ℝ f x v) :=
    (hd.continuous.mul ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const)).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ v).mul_left
  have hi3 : Integrable (fun x => d x * f x) :=
    (hd.continuous.mul hf.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi1 hi2 hi3
    (fun x _ => hd.differentiable_one x) (fun x _ => hf.differentiable_one x)
  have hdv (x : E) : fderiv ℝ d x v = -d x * inner ℝ v x := by
    rw [(standardGaussianDensity_hasFDerivAt x).fderiv]
    simp [d, real_inner_comm]
  simp_rw [hdv] at hh
  have integral_density (g : E → ℝ) :
      (∫ x, g x ∂stdGaussian E) = ∫ x, d x * g x := by
    rw [stdGaussian_eq_volume_density,
      integral_withDensity_eq_integral_toReal_smul hd.continuous.measurable.ennreal_ofReal
        (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (le_of_lt (standardGaussianDensity_pos _)), smul_eq_mul, d]
  rw [integral_density, integral_density, hh, ← integral_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by ring

/-- Compact pair coefficients justify all products even for an L² position field. -/
theorem pair_compact_position_integrable (μ : Measure E) [IsProbabilityMeasure μ]
    (a : Lp ℝ 2 μ) (c : E → ℝ) (hc : Continuous c)
    (F : E × E → ℝ) (hF : Continuous F) (hK : HasCompactSupport F) :
    Integrable (fun z => a z.1 * c z.1 * F z) (μ.prod (stdGaussian E)) := by
  have ha := (Lp.memLp a).comp_measurePreserving
    (measurePreserving_fst (μ := μ) (ν := stdGaussian E))
  have hb : MemLp (fun z : E × E => c z.1 * F z) 2 (μ.prod (stdGaussian E)) :=
    ((hc.comp continuous_fst).mul hF).memLp_of_hasCompactSupport hK.mul_left
  convert ha.integrable_mul hb using 1
  funext z
  dsimp only [Pi.mul_apply, Function.comp_apply]
  ring

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem momentum_slice_compact {φ : E × E → ℝ}
    (hc : HasCompactSupport φ) (x : E) : HasCompactSupport (fun p => φ (x,p)) := by
  apply HasCompactSupport.of_support_subset_isCompact (hc.image continuous_snd)
  intro p hp
  exact ⟨(x,p), subset_tsupport _ hp, rfl⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem momentum_slice_fderiv {φ : E × E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (x p v : E) :
    fderiv ℝ (fun y => φ (x,y)) p v = fderiv ℝ φ (x,p) (0,v) := by
  have hi := (hasFDerivAt_const x p).prodMk (hasFDerivAt_id (𝕜 := ℝ) p)
  exact congrArg (fun L : E →L[ℝ] ℝ => L v)
    (((hφ.differentiable one_ne_zero (x,p)).hasFDerivAt).comp p hi).fderiv

/-- The Gaussian part of Hamiltonian score cancellation on the actual pair law. -/
theorem pair_momentum_ibp (μ : Measure E) [IsProbabilityMeasure μ]
    (a : Lp ℝ 2 μ) (c : E → ℝ) (hc : Continuous c) (v : E)
    (φ : E × E → ℝ) (hφ : ContDiff ℝ 1 φ) (hK : HasCompactSupport φ) :
    Integrable (fun z => a z.1 * c z.1 * fderiv ℝ φ z (0,v)) (μ.prod (stdGaussian E)) ∧
    Integrable (fun z => a z.1 * c z.1 * (inner ℝ v z.2 * φ z)) (μ.prod (stdGaussian E)) ∧
    (∫ z, a z.1 * c z.1 * fderiv ℝ φ z (0,v) ∂μ.prod (stdGaussian E)) =
      ∫ z, a z.1 * c z.1 * (inner ℝ v z.2 * φ z) ∂μ.prod (stdGaussian E) := by
  have hl := pair_compact_position_integrable μ a c hc _
    ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const) (hK.fderiv_apply ℝ (0,v))
  have hr := pair_compact_position_integrable μ a c hc (fun z => inner ℝ v z.2 * φ z)
    ((continuous_const.inner continuous_snd).mul hφ.continuous) hK.mul_left
  refine ⟨hl, hr, ?_⟩
  rw [integral_prod _ hl, integral_prod _ hr]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [integral_const_mul, integral_const_mul]
    congr 1
    have hs : ContDiff ℝ 1 (fun p => φ (x,p)) :=
      hφ.comp (contDiff_const.prodMk contDiff_id)
    simpa only [momentum_slice_fderiv hφ] using
      gaussian_compact_fderiv _ hs (momentum_slice_compact hK x) v

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem position_slice_compact {φ : E × E → ℝ}
    (hc : HasCompactSupport φ) (p : E) : HasCompactSupport (fun x => φ (x,p)) := by
  apply HasCompactSupport.of_support_subset_isCompact (hc.image continuous_fst)
  intro x hx
  exact ⟨(x,p), subset_tsupport _ hx, rfl⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem position_slice_fderiv {φ : E × E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (x p v : E) :
    fderiv ℝ (fun y => φ (y,p)) x v = fderiv ℝ φ (x,p) (v,0) := by
  have hi := (hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const p x)
  exact congrArg (fun L : E →L[ℝ] ℝ => L v)
    (((hφ.differentiable one_ne_zero (x,p)).hasFDerivAt).comp x hi).fderiv

/-- Weighted position IBP for arbitrary compact C¹ pair tests, with integrability. -/
theorem pair_position_ibp (μ : Measure E) [IsProbabilityMeasure μ]
    (V : E → ℝ) (hV : ContDiff ℝ 1 V)
    (hI : Integrable (fun x => Real.exp (-V x)))
    (hμ : μ = volume.tilted (fun x => -V x))
    (u : Sobolev μ V hV hI hμ) (v : E)
    (φ : E × E → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    Integrable (fun z => φ z * inner ℝ (closedGradient μ V hV hI hμ u z.1) v)
      (μ.prod (stdGaussian E)) ∧
    Integrable (fun z => (u : Lp ℝ 2 μ) z.1 *
      (fderiv ℝ φ z (v,0) - φ z * fderiv ℝ V z.1 v)) (μ.prod (stdGaussian E)) ∧
    (∫ z, φ z * inner ℝ (closedGradient μ V hV hI hμ u z.1) v ∂μ.prod (stdGaussian E)) =
      -∫ z, (u : Lp ℝ 2 μ) z.1 *
        (fderiv ℝ φ z (v,0) - φ z * fderiv ℝ V z.1 v) ∂μ.prod (stdGaussian E) := by
  have hA : MemLp φ 2 (μ.prod (stdGaussian E)) := hφ.continuous.memLp_of_hasCompactSupport hc
  have hB : MemLp (fun z : E × E =>
      fderiv ℝ φ z (v,0) - φ z * fderiv ℝ V z.1 v) 2 (μ.prod (stdGaussian E)) := by
    apply Continuous.memLp_of_hasCompactSupport
    · exact ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const).sub
        (hφ.continuous.mul (((hV.continuous_fderiv one_ne_zero).comp continuous_fst).clm_apply continuous_const))
    · exact (hc.fderiv_apply ℝ (v,0)).sub hc.mul_right
  have hu := (Lp.memLp (u : Lp ℝ 2 μ)).comp_measurePreserving
    (measurePreserving_fst (μ := μ) (ν := stdGaussian E))
  have hD : MemLp (fun z : E × E => inner ℝ (closedGradient μ V hV hI hμ u z.1) v) 2 (μ.prod (stdGaussian E)) := ((Lp.memLp (closedGradient μ V hV hI hμ u)).inner_const v).comp_measurePreserving
    (measurePreserving_fst (μ := μ) (ν := stdGaussian E))
  have hf := hA.integrable_mul hD
  have hg := hu.integrable_mul hB
  change Integrable (fun z => φ z * inner ℝ (closedGradient μ V hV hI hμ u z.1) v) _ at hf
  change Integrable (fun z => (u : Lp ℝ 2 μ) z.1 * (fderiv ℝ φ z (v,0) - φ z * fderiv ℝ V z.1 v)) _ at hg
  refine ⟨hf, hg, ?_⟩
  rw [integral_prod_symm _ hf, integral_prod_symm _ hg, ← integral_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p => by
    have hs : ContDiff ℝ 1 (fun x => φ (x,p)) := hφ.comp (contDiff_id.prodMk contDiff_const)
    have hi := (closedGradient_integrationByParts μ V hV hI hμ u
      (fun x => φ (x,p)) hs (position_slice_compact hc p) v).2.2
    simpa only [position_slice_fderiv hφ] using hi


/-- Actual weighted/Gaussian score cancellation in a single orthonormal direction.
No spatial differentiability of the L² representative is assumed. -/
theorem pair_hamiltonian_component_ibp (μ : Measure E) [IsProbabilityMeasure μ]
    (V : E → ℝ) (hV : ContDiff ℝ 1 V)
    (hI : Integrable (fun x => Real.exp (-V x))) (hμ : μ = volume.tilted (fun x => -V x))
    (u : Sobolev μ V hV hI hμ) (v : E)
    (φ : E × E → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    Integrable (fun z => (u : Lp ℝ 2 μ) z.1 *
      (inner ℝ v z.2 * fderiv ℝ φ z (v,0) - fderiv ℝ V z.1 v * fderiv ℝ φ z (0,v)))
      (μ.prod (stdGaussian E)) ∧
    (∫ z, (u : Lp ℝ 2 μ) z.1 *
      (inner ℝ v z.2 * fderiv ℝ φ z (v,0) - fderiv ℝ V z.1 v * fderiv ℝ φ z (0,v))
      ∂μ.prod (stdGaussian E)) =
      -(∫ z, φ z * inner ℝ (closedGradient μ V hV hI hμ u z.1) v *
        inner ℝ v z.2 ∂μ.prod (stdGaussian E)) := by
  let c : E → ℝ := fun x => fderiv ℝ V x v
  have hcont : Continuous c := (hV.continuous_fderiv one_ne_zero).clm_apply continuous_const
  let l : E × E →L[ℝ] ℝ := (innerSL ℝ v).comp (ContinuousLinearMap.snd ℝ E E)
  let ψ : E × E → ℝ := fun z => l z * φ z
  have hd (z : E × E) : fderiv ℝ ψ z (v,0) =
      inner ℝ v z.2 * fderiv ℝ φ z (v,0) := by
    change (fderiv ℝ (⇑l * φ) z) _ = _
    rw [((l.hasFDerivAt).mul (hφ.differentiable_one z).hasFDerivAt).fderiv]
    simp [l]
  let S : E × E → ℝ := fun z => (u : Lp ℝ 2 μ) z.1 *
    (inner ℝ v z.2 * fderiv ℝ φ z (v,0))
  have hp := pair_momentum_ibp μ (u : Lp ℝ 2 μ) c hcont v φ hφ hc
  have hS : Integrable S (μ.prod (stdGaussian E)) := by
    have hh := pair_compact_position_integrable μ (u : Lp ℝ 2 μ) (fun _ => 1) continuous_const
      (fun z => l z * fderiv ℝ φ z (v,0))
      (l.continuous.mul ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const))
      ((hc.fderiv_apply ℝ (v,0)).mul_left)
    simpa [S, l, mul_assoc] using hh
  have hs := pair_position_ibp μ V hV hI hμ u v ψ (l.contDiff.mul hφ) hc.mul_left
  have hleft : (fun z => ψ z * inner ℝ (closedGradient μ V hV hI hμ u z.1) v) =
      (fun z => φ z * inner ℝ (closedGradient μ V hV hI hμ u z.1) v * inner ℝ v z.2) := by
    funext z
    simp [ψ, l]
    ring
  have hright : (fun z => (u : Lp ℝ 2 μ) z.1 *
      (fderiv ℝ ψ z (v,0) - ψ z * fderiv ℝ V z.1 v)) =
      (fun z => S z - ((u : Lp ℝ 2 μ) z.1 * c z.1 * (inner ℝ v z.2 * φ z))) := by
    funext z
    rw [hd]
    simp [S, ψ, l, c]
    ring
  rw [hleft, hright] at hs
  have ht := hs.2.2
  rw [integral_sub hS hp.2.1] at ht
  have heq : (fun z => (u : Lp ℝ 2 μ) z.1 *
      (inner ℝ v z.2 * fderiv ℝ φ z (v,0) - fderiv ℝ V z.1 v * fderiv ℝ φ z (0,v))) =
      (fun z => S z - ((u : Lp ℝ 2 μ) z.1 * c z.1 * fderiv ℝ φ z (0,v))) := by
    funext z
    dsimp [S,c]
    ring
  rw [heq]
  refine ⟨hS.sub hp.1, ?_⟩
  rw [integral_sub hS hp.1, hp.2.2]
  linarith


/-- Coordinate expression of the actual Hamiltonian derivative on E × E. -/
def pairHamiltonianTest (V : E → ℝ) (φ : E × E → ℝ) (z : E × E) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    (inner ℝ ((stdOrthonormalBasis ℝ E) i) z.2 *
      fderiv ℝ φ z ((stdOrthonormalBasis ℝ E) i,0) -
    fderiv ℝ V z.1 ((stdOrthonormalBasis ℝ E) i) *
      fderiv ℝ φ z (0,(stdOrthonormalBasis ℝ E) i))

omit [MeasurableSpace E] [BorelSpace E] in
theorem pairHamiltonianTest_eq_fderiv (V : E → ℝ) (φ : E × E → ℝ) (z : E × E) :
    pairHamiltonianTest V φ z = fderiv ℝ φ z (z.2, -gradient V z.1) := by
  let b := stdOrthonormalBasis ℝ E
  let L := fderiv ℝ φ z
  have hd (J : E →L[ℝ] E × E) (x : E) :
      (∑ i, inner ℝ (b i) x * L (J (b i))) = L (J x) := by
    simpa only [map_sum, map_smul, smul_eq_mul, ContinuousLinearMap.comp_apply] using
      congrArg (L.comp J) (b.sum_repr' x)
  have hp := hd (ContinuousLinearMap.inl ℝ E E) z.2
  have hg := hd (ContinuousLinearMap.inr ℝ E E) (gradient V z.1)
  simp only [inner_gradient_right, conj_trivial] at hg
  change (∑ i, (inner ℝ (b i) z.2 * L (b i,0) - fderiv ℝ V z.1 (b i) * L (0,b i))) = _
  rw [Finset.sum_sub_distrib]
  change (∑ i, inner ℝ (b i) z.2 * L ((ContinuousLinearMap.inl ℝ E E) (b i))) -
    (∑ i, fderiv ℝ V z.1 (b i) * L ((ContinuousLinearMap.inr ℝ E E) (b i))) = _
  rw [hp, hg]
  change L (z.2,0) - L (0,gradient V z.1) = _
  rw [← map_sub]
  simp [L, Prod.sub_def]

/-- Full weak Hamiltonian identity on the actual pair law; both sides integrable.
The proof sums the proved weighted/Gaussian cancellations and reconstructs the
actual Gaussian momentum embedding of the closed gradient. -/
theorem pair_hamiltonian_ibp (μ : Measure E) [IsProbabilityMeasure μ]
    (V : E → ℝ) (hV : ContDiff ℝ 1 V)
    (hI : Integrable (fun x => Real.exp (-V x))) (hμ : μ = volume.tilted (fun x => -V x))
    (u : Sobolev μ V hV hI hμ)
    (φ : E × E → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    Integrable (fun z => (u : Lp ℝ 2 μ) z.1 * pairHamiltonianTest V φ z)
      (μ.prod (stdGaussian E)) ∧
    Integrable (fun z => φ z * momentumEmbedding μ (closedGradient μ V hV hI hμ u) z)
      (μ.prod (stdGaussian E)) ∧
    (∫ z, (u : Lp ℝ 2 μ) z.1 * pairHamiltonianTest V φ z ∂μ.prod (stdGaussian E)) =
      -(∫ z, φ z * momentumEmbedding μ (closedGradient μ V hV hI hμ u) z
        ∂μ.prod (stdGaussian E)) := by
  classical
  let b := stdOrthonormalBasis ℝ E
  let G := closedGradient μ V hV hI hμ u
  let W (i : Fin (Module.finrank ℝ E)) (z : E × E) :=
    (u : Lp ℝ 2 μ) z.1 * (inner ℝ (b i) z.2 * fderiv ℝ φ z (b i,0) -
      fderiv ℝ V z.1 (b i) * fderiv ℝ φ z (0,b i))
  let F (i : Fin (Module.finrank ℝ E)) (z : E × E) :=
    φ z * inner ℝ (G z.1) (b i) * inner ℝ (b i) z.2
  have hi (i : Fin (Module.finrank ℝ E)) : Integrable (W i) (μ.prod (stdGaussian E)) ∧
      (∫ z, W i z ∂μ.prod (stdGaussian E)) = -(∫ z, F i z ∂μ.prod (stdGaussian E)) :=
    pair_hamiltonian_component_ibp μ V hV hI hμ u (b i) φ hφ hc
  have hF (i : Fin (Module.finrank ℝ E)) : Integrable (F i) (μ.prod (stdGaussian E)) := by
    have hcF : MemLp (fun z : E × E => φ z * inner ℝ (b i) z.2) 2 (μ.prod (stdGaussian E)) := by
      apply Continuous.memLp_of_hasCompactSupport
      · fun_prop
      · exact hc.mul_right
    have hG : MemLp (fun z : E × E => inner ℝ (G z.1) (b i)) 2 (μ.prod (stdGaussian E)) :=
      ((Lp.memLp G).inner_const (b i)).comp_measurePreserving measurePreserving_fst
    convert hcF.integrable_mul hG using 1
    funext z
    dsimp [F]
    ring
  have hW : (fun z => ∑ i, W i z) =
      (fun z => (u : Lp ℝ 2 μ) z.1 * pairHamiltonianTest V φ z) := by
    funext z
    simp only [W, pairHamiltonianTest, b, Finset.mul_sum]
  have hsumF : (fun z => ∑ i, F i z) =ᵐ[μ.prod (stdGaussian E)]
      fun z => φ z * momentumEmbedding μ G z := by
    filter_upwards [momentumEmbedding_coe μ G] with z hz
    rw [hz]
    simp only [F, mul_assoc, ← Finset.mul_sum]
    congr 1
    have heq := congrArg (innerSL ℝ (G z.1)) (b.sum_repr' z.2)
    simpa only [map_sum, map_smul, innerSL_apply_apply, smul_eq_mul, mul_comm] using heq
  refine ⟨?_, (integrable_finsetSum Finset.univ (fun i _ => hF i)).congr hsumF, ?_⟩
  · rw [← hW]
    exact integrable_finsetSum Finset.univ (fun i _ => (hi i).1)
  · rw [← hW, ← integral_congr_ae hsumF,
      integral_finsetSum Finset.univ (fun i _ => (hi i).1),
      integral_finsetSum Finset.univ (fun i _ => hF i)]
    simp only [fun i => (hi i).2, Finset.sum_neg_distrib]


/-- Graph-pair form, retaining the genuine closed derivative rather than choosing
an unrelated weak field. -/
theorem graph_pair_hamiltonian_ibp (μ : Measure E) [IsProbabilityMeasure μ]
    (V : E → ℝ) (hV : ContDiff ℝ 1 V)
    (hI : Integrable (fun x => Real.exp (-V x))) (hμ : μ = volume.tilted (fun x => -V x))
    (u : Lp ℝ 2 μ) (G : Lp E 2 μ)
    (hG : (u,G) ∈ (closedGradient μ V hV hI hμ).graph)
    (φ : E × E → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    Integrable (fun z => u z.1 * fderiv ℝ φ z (z.2, -gradient V z.1))
      (μ.prod (stdGaussian E)) ∧
    Integrable (fun z => φ z * momentumEmbedding μ G z) (μ.prod (stdGaussian E)) ∧
    (∫ z, u z.1 * fderiv ℝ φ z (z.2, -gradient V z.1) ∂μ.prod (stdGaussian E)) =
      -(∫ z, φ z * momentumEmbedding μ G z ∂μ.prod (stdGaussian E)) := by
  obtain ⟨u0, hu, hg⟩ := (LinearPMap.mem_graph_iff _).mp hG
  have h := pair_hamiltonian_ibp μ V hV hI hμ u0 φ hφ hc
  simpa only [hu, hg, pairHamiltonianTest_eq_fderiv] using h

end AcceleratedLogConcave.Kinetic.DirectW12
