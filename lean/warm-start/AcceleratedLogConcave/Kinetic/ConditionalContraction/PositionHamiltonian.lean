import AcceleratedLogConcave.Kinetic.ConditionalContraction.HamiltonianRows
import AcceleratedLogConcave.Kinetic.MomentumSplit

/-! Actual Hamiltonian derivatives of position observables. -/
noncomputable section
open MeasureTheory InnerProductSpace ProbabilityTheory
open scoped ContDiff RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.ConditionalContraction
open Analysis.WeightedGradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual velocity `s P - n E` lift is an isometry when the split is orthogonal. -/
def velocityEmbedding (μ : Measure E) [IsProbabilityMeasure μ] (s n : ℝ)
    (hsn : s ^ 2 + n ^ 2 = 1) : Lp E 2 μ →ₗᵢ[ℝ] Lp ℝ 2 (gaussianPhaseMeasure μ) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (phaseSplit s (-n) (by simpa using hsn))
    (phaseSplit_measurePreserving μ s (-n) (by simpa using hsn))).comp (gaussianMomentumEmbedding μ)

theorem velocityEmbedding_coe (μ : Measure E) [IsProbabilityMeasure μ] (s n : ℝ)
    (hsn : s ^ 2 + n ^ 2 = 1) (G : Lp E 2 μ) :
    velocityEmbedding μ s n hsn G =ᵐ[gaussianPhaseMeasure μ]
      fun z => inner ℝ (G z.1.1) (s • z.1.2 - n • z.2) := by
  have h := (Lp.coeFn_compMeasurePreserving (gaussianMomentumEmbedding μ G)
    (phaseSplit_measurePreserving μ s (-n) (by simpa using hsn))).trans
    ((phaseSplit_measurePreserving μ s (-n) (by simpa using hsn)).quasiMeasurePreserving.ae
      (gaussianMomentumEmbedding_coe μ G))
  convert h using 1
  simp only [velocityEmbedding, LinearIsometry.coe_comp, Function.comp_apply]
  rfl
  funext z
  change inner ℝ (G z.1.1) (s • z.1.2 - n • z.2) = inner ℝ (G z.1.1) (s • z.1.2 + (-n) • z.2)
  rw [neg_smul, sub_eq_add_neg]

/-- Weighted position IBP and Gaussian Stein identities cancel the entire
score contribution for an arbitrary compact C1 phase test. -/
theorem phase_hamiltonian_position_component_ibp (μ : Measure E) [IsProbabilityMeasure μ]
    (V : E → ℝ) (hV : ContDiff ℝ 1 V)
    (hI : Integrable (fun x => Real.exp (-V x))) (hμ : μ = volume.tilted (fun x => -V x))
    (u : Sobolev μ V hV hI hμ) (v : E) (s n : ℝ)
    (φ : GaussianPhase E → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    Integrable (fun z => (u : Lp ℝ 2 μ) z.1.1 *
      ((s * inner ℝ v z.1.2 - n * inner ℝ v z.2) * fderiv ℝ φ z ((v,0),0) -
        fderiv ℝ V z.1.1 v * (s * fderiv ℝ φ z ((0,v),0) - n * fderiv ℝ φ z ((0,0),v))))
      (gaussianPhaseMeasure μ) ∧
    (∫ z, (u : Lp ℝ 2 μ) z.1.1 *
      ((s * inner ℝ v z.1.2 - n * inner ℝ v z.2) * fderiv ℝ φ z ((v,0),0) -
        fderiv ℝ V z.1.1 v * (s * fderiv ℝ φ z ((0,v),0) - n * fderiv ℝ φ z ((0,0),v)))
      ∂gaussianPhaseMeasure μ) =
      -(∫ z, φ z * inner ℝ (closedGradient μ V hV hI hμ u z.1.1) v *
        (s * inner ℝ v z.1.2 - n * inner ℝ v z.2) ∂gaussianPhaseMeasure μ) := by
  let c : E → ℝ := fun x => fderiv ℝ V x v
  have hcont : Continuous c := (hV.continuous_fderiv one_ne_zero).clm_apply continuous_const
  let pL : GaussianPhase E →L[ℝ] ℝ := (innerSL ℝ v).comp
    ((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.fst ℝ (E×E) E))
  let eL : GaussianPhase E →L[ℝ] ℝ := (innerSL ℝ v).comp (ContinuousLinearMap.snd ℝ (E×E) E)
  let l := s • pL - n • eL
  let ψ : GaussianPhase E → ℝ := fun z => l z * φ z
  have hd (z : GaussianPhase E) : fderiv ℝ ψ z ((v,0),0) =
      (s * inner ℝ v z.1.2 - n * inner ℝ v z.2) * fderiv ℝ φ z ((v,0),0) := by
    change (fderiv ℝ (⇑l * φ) z) _ = _
    rw [((l.hasFDerivAt).mul (hφ.differentiable_one z).hasFDerivAt).fderiv]
    simp [l, pL, eL]
  let S : GaussianPhase E → ℝ := fun z => (u : Lp ℝ 2 μ) z.1.1 *
    ((s * inner ℝ v z.1.2 - n * inner ℝ v z.2) * fderiv ℝ φ z ((v,0),0))
  have hp := phase_momentum_ibp μ (u : Lp ℝ 2 μ) c hcont v φ hφ hc
  have he := phase_auxiliary_ibp μ (u : Lp ℝ 2 μ) c hcont v φ hφ hc
  have hS : Integrable S (gaussianPhaseMeasure μ) := by
    have hh := phase_compact_position_integrable μ (u : Lp ℝ 2 μ) (fun _ => 1) continuous_const
      (fun z => l z * fderiv ℝ φ z ((v,0),0))
      (l.continuous.mul ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const))
      ((hc.fderiv_apply ℝ ((v,0),0)).mul_left)
    simpa [S, l, pL, eL, mul_assoc] using hh
  have hs := phase_test_weighted_ibp_position μ V hV hI hμ u v ψ (l.contDiff.mul hφ) hc.mul_left
  have hleft : (fun z => ψ z * inner ℝ (closedGradient μ V hV hI hμ u z.1.1) v) =
      (fun z => φ z * inner ℝ (closedGradient μ V hV hI hμ u z.1.1) v *
        (s * inner ℝ v z.1.2 - n * inner ℝ v z.2)) := by
    funext z
    simp [ψ, l, pL, eL]
    ring
  have hright : (fun z => (u : Lp ℝ 2 μ) z.1.1 *
      (fderiv ℝ ψ z ((v,0),0) - ψ z * fderiv ℝ V z.1.1 v)) =
      (fun z => S z - s * ((u : Lp ℝ 2 μ) z.1.1 * c z.1.1 * (inner ℝ v z.1.2 * φ z)) +
        n * ((u : Lp ℝ 2 μ) z.1.1 * c z.1.1 * (inner ℝ v z.2 * φ z))) := by
    funext z
    rw [hd]
    simp [S, ψ, l, pL, eL, c]
    ring
  rw [hleft, hright] at hs
  have ht := hs.2.2
  have ha := integral_add (hS.sub (hp.2.1.const_mul s)) (he.2.1.const_mul n)
  have hb := integral_sub hS (hp.2.1.const_mul s)
  simp only [Pi.sub_apply] at ha hb
  rw [ha, hb, integral_const_mul, integral_const_mul] at ht
  have heq : (fun z => (u : Lp ℝ 2 μ) z.1.1 *
      ((s * inner ℝ v z.1.2 - n * inner ℝ v z.2) * fderiv ℝ φ z ((v,0),0) -
        fderiv ℝ V z.1.1 v * (s * fderiv ℝ φ z ((0,v),0) - n * fderiv ℝ φ z ((0,0),v)))) =
      (fun z => S z - s * ((u : Lp ℝ 2 μ) z.1.1 * c z.1.1 * fderiv ℝ φ z ((0,v),0)) +
        n * ((u : Lp ℝ 2 μ) z.1.1 * c z.1.1 * fderiv ℝ φ z ((0,0),v))) := by
    funext z
    dsimp [S,c]
    ring
  rw [heq]
  refine ⟨(hS.sub (hp.1.const_mul s)).add (he.1.const_mul n), ?_⟩
  have hia := integral_add (hS.sub (hp.1.const_mul s)) (he.1.const_mul n)
  have hib := integral_sub hS (hp.1.const_mul s)
  simp only [Pi.sub_apply] at hia hib
  rw [hia, hib, integral_const_mul, integral_const_mul, hp.2.2, he.2.2]
  linarith

/-- The full Hamiltonian image of a genuine closed-gradient position function
is exactly its Gaussian velocity lift. -/
theorem phase_hamiltonian_position_ibp (μ : Measure E) [IsProbabilityMeasure μ]
    (V : E → ℝ) (hV : ContDiff ℝ 1 V)
    (hI : Integrable (fun x => Real.exp (-V x))) (hμ : μ = volume.tilted (fun x => -V x))
    (u : Sobolev μ V hV hI hμ) (s n : ℝ) (hsn : s ^ 2 + n ^ 2 = 1)
    (φ : GaussianPhase E → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    Integrable (fun z => positionEmbedding μ (u : Lp ℝ 2 μ) z * hamiltonianTestDerivative V s n φ z)
      (gaussianPhaseMeasure μ) ∧
    (∫ z, positionEmbedding μ (u : Lp ℝ 2 μ) z * hamiltonianTestDerivative V s n φ z
      ∂gaussianPhaseMeasure μ) =
      -(∫ z, φ z * velocityEmbedding μ s n hsn (closedGradient μ V hV hI hμ u) z
        ∂gaussianPhaseMeasure μ) := by
  classical
  let b := stdOrthonormalBasis ℝ E
  let G := closedGradient μ V hV hI hμ u
  let W (i : Fin (Module.finrank ℝ E)) (z : GaussianPhase E) :=
    (u : Lp ℝ 2 μ) z.1.1 *
      ((s * inner ℝ (b i) z.1.2 - n * inner ℝ (b i) z.2) * fderiv ℝ φ z ((b i,0),0) -
        fderiv ℝ V z.1.1 (b i) * (s * fderiv ℝ φ z ((0,b i),0) - n * fderiv ℝ φ z ((0,0),b i)))
  let F (i : Fin (Module.finrank ℝ E)) (z : GaussianPhase E) :=
    φ z * inner ℝ (G z.1.1) (b i) * (s * inner ℝ (b i) z.1.2 - n * inner ℝ (b i) z.2)
  have hi (i : Fin (Module.finrank ℝ E)) : Integrable (W i) (gaussianPhaseMeasure μ) ∧
      (∫ z, W i z ∂gaussianPhaseMeasure μ) = -(∫ z, F i z ∂gaussianPhaseMeasure μ) :=
    phase_hamiltonian_position_component_ibp μ V hV hI hμ u (b i) s n φ hφ hc
  have hpos : MeasurePreserving (fun z : GaussianPhase E => z.1.1) (gaussianPhaseMeasure μ) μ :=
    measurePreserving_fst.comp measurePreserving_fst
  have hF (i : Fin (Module.finrank ℝ E)) : Integrable (F i) (gaussianPhaseMeasure μ) := by
    have hcF : MemLp (fun z : GaussianPhase E => φ z *
        (s * inner ℝ (b i) z.1.2 - n * inner ℝ (b i) z.2)) 2 (gaussianPhaseMeasure μ) := by
      apply Continuous.memLp_of_hasCompactSupport
      · fun_prop
      · exact hc.mul_right
    have hh := hcF.integrable_mul (((Lp.memLp G).inner_const (b i)).comp_measurePreserving hpos)
    convert hh using 1
    funext z
    dsimp [F]
    ring
  have hW : (fun z => ∑ i, W i z) =ᵐ[gaussianPhaseMeasure μ]
      fun z => positionEmbedding μ (u : Lp ℝ 2 μ) z * hamiltonianTestDerivative V s n φ z := by
    filter_upwards [positionEmbedding_coe μ (u : Lp ℝ 2 μ)] with z hz
    simp only [hz, W, hamiltonianTestDerivative, b, Finset.mul_sum]
  have hsumF : (fun z => ∑ i, F i z) =ᵐ[gaussianPhaseMeasure μ]
      fun z => φ z * velocityEmbedding μ s n hsn G z := by
    filter_upwards [velocityEmbedding_coe μ s n hsn G] with z hz
    rw [hz]
    simp only [F, mul_assoc, ← Finset.mul_sum]
    congr 1
    have heq := congrArg (innerSL ℝ (G z.1.1)) (b.sum_repr' (s • z.1.2 - n • z.2))
    simpa only [map_sum, map_smul, innerSL_apply_apply, inner_sub_right,
      inner_smul_right, smul_eq_mul, mul_comm] using heq
  refine ⟨(integrable_finsetSum Finset.univ (fun i _ => (hi i).1)).congr hW, ?_⟩
  rw [← integral_congr_ae hW, ← integral_congr_ae hsumF,
    integral_finsetSum Finset.univ (fun i _ => (hi i).1),
    integral_finsetSum Finset.univ (fun i _ => hF i)]
  simp only [fun i => (hi i).2, Finset.sum_neg_distrib]

/-- A velocity lift is genuinely microscopic for the actual position projection. -/
theorem gaussianPositionProjection_velocityEmbedding (μ : Measure E) [IsProbabilityMeasure μ]
    (s n : ℝ) (hsn : s ^ 2 + n ^ 2 = 1) (G : Lp E 2 μ) :
    gaussianPositionProjection μ (velocityEmbedding μ s n hsn G) = 0 := by
  let U : Lp ℝ 2 (gaussianPhaseMeasure μ) →ₗᵢ[ℝ] Lp ℝ 2 (gaussianPhaseMeasure μ) :=
    Lp.compMeasurePreservingₗᵢ ℝ (phaseSplit s (-n) (by simpa using hsn))
    (phaseSplit_measurePreserving μ s (-n) (by simpa using hsn))
  have hfix (g : Lp ℝ 2 μ) : U (positionEmbedding μ g) = positionEmbedding μ g := by
    apply Lp.ext
    have h := (Lp.coeFn_compMeasurePreserving (positionEmbedding μ g)
      (phaseSplit_measurePreserving μ s (-n) (by simpa using hsn))).trans
      ((phaseSplit_measurePreserving μ s (-n) (by simpa using hsn)).quasiMeasurePreserving.ae
        (positionEmbedding_coe μ g))
    exact h.trans (positionEmbedding_coe μ g).symm
  have havg : gaussianAverage μ (velocityEmbedding μ s n hsn G) = 0 := by
    apply ext_inner_left ℝ
    intro g
    change inner ℝ g ((positionEmbedding μ).toContinuousLinearMap.adjoint (U (gaussianMomentumEmbedding μ G))) = _
    rw [ContinuousLinearMap.adjoint_inner_right]
    change inner ℝ (positionEmbedding μ g) (U (gaussianMomentumEmbedding μ G)) = _
    rw [← hfix g, U.inner_map_map]
    change inner ℝ ((positionEmbedding μ).toContinuousLinearMap g) (gaussianMomentumEmbedding μ G) = _
    rw [← ContinuousLinearMap.adjoint_inner_right]
    change inner ℝ g (gaussianAverage μ (gaussianMomentumEmbedding μ G)) = _
    rw [gaussianAverage_momentumEmbedding, inner_zero_right]
  change positionEmbedding μ (gaussianAverage μ (velocityEmbedding μ s n hsn G)) = 0
  rw [havg, map_zero]

open Analysis.Poisson
/-- The actual Hamiltonian image of the corrector is a microscopic contraction.
Its distributional identity is proved against every compact C1 phase test. -/
theorem gaussianCorrector_hamiltonian_image
    (μ : Measure E) [IsProbabilityMeasure μ] (V : E → ℝ)
    (hV : ContDiff ℝ 2 V) (hI : Integrable (fun x => Real.exp (-V x)))
    (hμ : μ = volume.tilted (fun x => -V x)) (m L : ℝ) (hm : 0 < m)
    (hlower : ∀ x a, m * ‖a‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x a a)
    (hupper : ∀ x a, fderiv ℝ (fderiv ℝ V) x a a ≤ L * ‖a‖ ^ 2)
    (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) (s n : ℝ) (hsn : s ^ 2 + n ^ 2 = 1) :
    ∃ B : Lp ℝ 2 (gaussianPhaseMeasure μ),
      gaussianPositionProjection μ B = 0 ∧
      ‖B‖ ≤ ‖f - gaussianPositionProjection μ f‖ ∧
      ∀ (φ : GaussianPhase E → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
        Integrable (fun z => gaussianCorrector μ V hV hI hμ m L hm hlower hupper f z *
          hamiltonianTestDerivative V s n φ z) (gaussianPhaseMeasure μ) ∧
        (∫ z, gaussianCorrector μ V hV hI hμ m L hm hlower hupper f z *
          hamiltonianTestDerivative V s n φ z ∂gaussianPhaseMeasure μ) =
          -(∫ z, φ z * B z ∂gaussianPhaseMeasure μ) := by
  let D := gaussianCorrectorPositionGradient μ V hV hI hμ m L hm hlower hupper
  refine ⟨velocityEmbedding μ s n hsn (D f), gaussianPositionProjection_velocityEmbedding μ s n hsn _, ?_, ?_⟩
  · rw [(velocityEmbedding μ s n hsn).norm_map]
    have hz : D (gaussianPositionProjection μ f) = 0 := by
      change weightedGradientProjection μ V hV hI hμ m L hm hlower hupper
        (gaussianMomentumAdjoint μ (positionEmbedding μ (gaussianAverage μ f))) = 0
      rw [gaussianMomentumAdjoint_positionEmbedding, map_zero]
    have hb := D.le_opNorm (f - gaussianPositionProjection μ f)
    rw [map_sub, hz, sub_zero] at hb
    have hn := mul_le_mul_of_nonneg_right
      (gaussianCorrectorPositionGradient_norm_le μ V hV hI hμ m L hm hlower hupper)
      (norm_nonneg (f - gaussianPositionProjection μ f))
    exact hb.trans (by simpa only [one_mul] using hn)
  · intro φ hφ hc
    exact phase_hamiltonian_position_ibp μ V (hV.of_le (by norm_num)) hI hμ
      (vectorPoissonSolution μ V hV hI hμ m L hm hlower hupper (gaussianMomentumAdjoint μ f))
      s n hsn φ hφ hc

end AcceleratedLogConcave.Kinetic.ConditionalContraction
