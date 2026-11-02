import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.PhaseCurrentCalculus
import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.PhaseTransport

/-! The genuine ordinary heat-current derivative on the compact joint phase core. -/
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory ProbabilityTheory Set InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Actual heat evolution, Poisson Green identities, and the material corrector
bound give the source current estimate, without a current estimate premise. -/
theorem phaseHeatCurrent_derivative_bound {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
    (hscale : ∀ t ∈ Ioo a b, F.scale t = -(1/2:ℝ))
    (t : ℝ) (ht : t ∈ Ioo a b) :
    ∃ d : ℝ, HasDerivAt (phaseHeatCurrent F hf hc hheat) d t ∧
      |d| ≤ ‖compactTestL2 ((F.law a).prod (stdGaussian E)) f hf.continuous hc‖ *
        Real.sqrt (phaseHeatDissipation F hf hc hheat t) +
        ‖compactTestL2 ((F.law a).prod (stdGaussian E)) f hf.continuous hc‖^2/4 := by
  let τ : Icc a b := ⟨t,ht.1.le,ht.2.le⟩
  let q := (compactPhaseHeatQuotient_memLp F hf hc hheat t τ.property).1.toLp _
  let k := phaseHeatGeneratorLp F hf hc hheat t τ.property
  let A := phaseVisibleCorrector F t τ.property
  let qref := Kinetic.hiddenEmbedding (F.law a) (phaseHeatMovingCoreLp F hf hc hheat t)
  let dref := Kinetic.hiddenEmbedding (F.law a) (phaseHeatMovingGeneratorLp F hf hc hheat t)
  let N := ‖compactTestL2 ((F.law a).prod (stdGaussian E)) f hf.continuous hc‖
  let G := ‖phaseHeatGradientLp F hf hc hheat t τ.property‖
  have hq : qref = F.phaseUnitary τ (Kinetic.hiddenEmbedding (F.law t) q) := by
    dsimp only [qref]
    rw [phaseHeatMovingCoreLp_eq_pullback F hf hc hheat t τ.property,
      phaseHeatPullback_hiddenEmbedding]
  have hd : dref = -(1/2:ℝ) • F.phaseUnitary τ (Kinetic.hiddenEmbedding (F.law t) k) := by
    dsimp only [dref]
    rw [phaseHeatMovingGeneratorLp_eq_pullback F hf hc hheat t τ.property,
      map_smul, phaseHeatPullback_hiddenEmbedding]
    rfl
  have hn : ‖q‖ ≤ N := by
    have he : ‖q‖ = ‖phaseHeatMovingCoreLp F hf hc hheat t‖ := by
      rw [phaseHeatMovingCoreLp_eq_pullback F hf hc hheat t τ.property,
        (phaseHeatPullback F τ).norm_map]
    rw [he, phaseHeatMovingCoreLp_norm_eq_ordinaryHeatDensity F hf hc hheat t τ.property]
    simpa only [one_mul] using ContinuousLinearMap.le_of_opNorm_le _
      (ordinaryHeatDensity_norm_le (F.law a) (t-a))
      (compactTestL2 ((F.law a).prod (stdGaussian E)) f hf.continuous hc)
  have hnref : ‖qref‖ = ‖q‖ := by
    rw [hq, (F.phaseUnitary τ).norm_map, (Kinetic.hiddenEmbedding (F.law t)).norm_map]
  have h1 : inner ℝ dref (F.corrector t qref) = -(1/2:ℝ)*inner ℝ k (A q) := by
    rw [hd,hq,real_inner_smul_left]
    congr 1
    exact phaseHeat_corrector_pullback_pairing F t ht k q
  have h2 : inner ℝ qref (F.corrector t dref) = -(1/2:ℝ)*inner ℝ k (A.adjoint q) := by
    rw [hd,hq,map_smul,inner_smul_right]
    congr 1
    rw [phaseHeat_corrector_pullback_pairing F t ht q k]
    exact (real_inner_comm (A k) q).trans (A.adjoint_inner_right k q).symm
  have hb1 : |inner ℝ k (A q)| ≤ G*‖q‖ := phaseHeat_corrector_pairing_bound F hf hc hheat t τ.property q
  have hb2 : |inner ℝ k (A.adjoint q)| ≤ G*‖q‖ := phaseHeat_corrector_adjoint_pairing_bound F hf hc hheat t τ.property q
  have hm := phaseHeat_materialCorrector_pairing_bound F t ht (hscale t ht) qref
  rw [hnref] at hm
  have hG : Real.sqrt (phaseHeatDissipation F hf hc hheat t) = G := by
    rw [phaseHeatDissipation_eq_norm_sq F hf hc hheat t τ.property, Real.sqrt_sq (norm_nonneg _)]
  refine ⟨_,phaseHeatCurrent_hasDerivAt F hf hc hheat hscale t ht,?_⟩
  change |inner ℝ dref (F.corrector t qref) + inner ℝ qref (F.corrector t dref) +
    inner ℝ qref (F.materialCorrector t ht qref)| ≤ N*Real.sqrt (phaseHeatDissipation F hf hc hheat t)+N^2/4
  rw [h1,h2,hG]
  have htriangle := (abs_add_le (-(1/2:ℝ)*inner ℝ k (A q) + -(1/2:ℝ)*inner ℝ k (A.adjoint q))
    (inner ℝ qref (F.materialCorrector t ht qref))).trans
    (add_le_add (abs_add_le _ _) le_rfl)
  simp only [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)] at htriangle
  have hGN := mul_le_mul_of_nonneg_left hn (norm_nonneg (phaseHeatGradientLp F hf hc hheat t τ.property))
  have hN : 0 ≤ N := norm_nonneg _
  have hn0 := norm_nonneg q
  nlinarith

end AcceleratedLogConcave.Kinetic.Reheating
