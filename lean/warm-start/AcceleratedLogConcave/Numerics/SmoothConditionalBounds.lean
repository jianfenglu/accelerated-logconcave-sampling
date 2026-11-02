import AcceleratedLogConcave.Numerics.SamplingCenterLp
import AcceleratedLogConcave.Conditional.SourcePosteriorParameters
import AcceleratedLogConcave.Conditional.Tilt.GaussianTimePolynomial
import AcceleratedLogConcave.Analysis.CoupledVelocityPolynomial

/-!
Polynomial bounds for the conditional coefficient with unrestricted center
and state. The potential and observable are the original potential and its
gradient. Compactness is used only in probability time, never in the center.
These qualitative bounds are intended for time differentiation along a path;
they give no numerical derivative budget or transported-Jacobian estimate.
-/
noncomputable section
open Set Function MeasureTheory
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Numerics.ConditionalSmoothing
open Conditional Conditional.Tilt Analysis.PositiveVarianceSlab
open Analysis.CoupledVelocityPolynomial

private theorem polynomialJetBound_add
    {P G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {U S : Set P} (hU : UniqueDiffOn ℝ U) (hSU : S ⊆ U)
    {f g : P → G} (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (n : ℕ) (hfb : PolynomialJetBound U S f n) (hgb : PolynomialJetBound U S g n) :
    PolynomialJetBound U S (fun p => f p + g p) n := by
  obtain ⟨C,hC,N,hfb⟩ := hfb
  obtain ⟨D,hD,M,hgb⟩ := hgb
  refine ⟨C+D, add_nonneg hC hD, N+M, ?_⟩
  intro p hp
  have hR : 1 ≤ 1+‖p‖ := le_add_of_nonneg_right (norm_nonneg p)
  rw [fun_iteratedFDerivWithin_add_apply
    ((hf p (hSU hp)).of_le (by simp : (n : ℕ∞ω) ≤ ∞))
    ((hg p (hSU hp)).of_le (by simp : (n : ℕ∞ω) ≤ ∞)) hU (hSU hp)]
  calc
    _ ≤ ‖iteratedFDerivWithin ℝ n f U p‖ + ‖iteratedFDerivWithin ℝ n g U p‖ := norm_add_le _ _
    _ ≤ C*(1+‖p‖)^N + D*(1+‖p‖)^M := add_le_add (hfb p hp) (hgb p hp)
    _ ≤ C*(1+‖p‖)^(N+M) + D*(1+‖p‖)^(N+M) := add_le_add
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR (Nat.le_add_right N M)) hC)
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR (Nat.le_add_left M N)) hD)
    _ = _ := by ring

variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "P" => ℝ × (E × E)
variable (d : SamplingCenterLp.Data ι)

def physicalPrecision (t : ℝ) : ℝ := (2*(d.r^2*conditionalVariance t))⁻¹
def physicalInverseVariance (t : ℝ) : ℝ := (d.r^2*conditionalVariance t)⁻¹
def physicalTiltScale (t : ℝ) : ℝ := physicalInverseVariance d t * (d.r*t)

theorem contDiffOn_physicalPrecision : ContDiffOn ℝ ∞ (physicalPrecision d) (Ioo (-1) 1) := by
  apply (contDiffOn_const.mul (contDiffOn_const.mul
    (contDiffOn_const.sub (contDiffOn_id.pow 2)))).inv
  intro t ht
  exact (mul_pos (by norm_num) (mul_pos (sq_pos_of_pos d.hr)
    (conditionalVariance_pos ht.1 ht.2))).ne'

theorem contDiffOn_physicalInverseVariance :
    ContDiffOn ℝ ∞ (physicalInverseVariance d) (Ioo (-1) 1) := by
  apply (contDiffOn_const.mul (contDiffOn_const.sub (contDiffOn_id.pow 2))).inv
  intro t ht
  exact (mul_pos (sq_pos_of_pos d.hr) (conditionalVariance_pos ht.1 ht.2)).ne'

theorem contDiffOn_physicalTiltScale : ContDiffOn ℝ ∞ (physicalTiltScale d) (Ioo (-1) 1) :=
  (contDiffOn_physicalInverseVariance d).mul (contDiffOn_const.mul contDiffOn_id)

def centerParameters (p : P) : ℝ × E :=
  (physicalPrecision d p.1,
    physicalInverseVariance d p.1 • p.2.1 + physicalTiltScale d p.1 • p.2.2)

theorem centerParameters_eq_posterior (p : P) :
    centerParameters d p = posteriorParameters
      (d.r^2*conditionalVariance p.1, p.2.1 + (d.r*p.1) • p.2.2) := by
  simp only [centerParameters, posteriorParameters, physicalPrecision,
    physicalInverseVariance, physicalTiltScale, smul_add, smul_smul]

private def centerProjection : P →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ E E).comp (ContinuousLinearMap.snd ℝ ℝ (E × E))
private def stateProjection : P →L[ℝ] E :=
  (ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.snd ℝ ℝ (E × E))

theorem contDiffOn_centerParameters :
    ContDiffOn ℝ ∞ (centerParameters d) (openDomain (E × E)) := by
  exact ((contDiffOn_physicalPrecision d).comp_continuousLinearMap
    (ContinuousLinearMap.fst ℝ ℝ (E × E))).prodMk
    ((((contDiffOn_physicalInverseVariance d).comp_continuousLinearMap
      (ContinuousLinearMap.fst ℝ ℝ (E × E))).smul
      (centerProjection (ι := ι)).contDiff.contDiffOn).add
    (((contDiffOn_physicalTiltScale d).comp_continuousLinearMap
      (ContinuousLinearMap.fst ℝ ℝ (E × E))).smul
      (stateProjection (ι := ι)).contDiff.contDiffOn))

theorem centerParameters_mem {p : P} (hp : p ∈ openDomain (E × E)) :
    centerParameters d p ∈ gaussianDomain :=
  inv_pos.mpr (mul_pos (by norm_num) (mul_pos (sq_pos_of_pos d.hr)
    (conditionalVariance_pos hp.1 hp.2)))

private theorem scalar_polynomial_bound {φ : ℝ → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ (Ioo (-1) 1)) (n : ℕ) :
    PolynomialJetBound (openDomain (E × E)) (closedSlab (E × E) d.b)
      (fun p : P => φ p.1) n := by
  obtain ⟨C,hC,h⟩ := Analysis.CompactScalarJets.exists_uniform_jet_comp_linear_bound
    isOpen_Ioo isCompact_Icc (construction_subset d.hb d.hb1) hφ
    (ContinuousLinearMap.fst ℝ ℝ (E × E)) (ContinuousLinearMap.norm_fst_le ℝ ℝ (E × E)) n
  exact ⟨C,hC,0,fun p hp => by simpa only [pow_zero, mul_one, ContinuousLinearMap.coe_fst',
    Function.comp_def, openDomain] using h p hp⟩

theorem polynomialJetBound_centerParameters (n : ℕ) :
    PolynomialJetBound (openDomain (E × E)) (closedSlab (E × E) d.b)
      (centerParameters d) n := by
  have hU : UniqueDiffOn ℝ (openDomain (E × E)) := (isOpen_openDomain (E × E)).uniqueDiffOn
  have hSU := closedSlab_subset_openDomain (E × E) d.hb d.hb1
  have ha := (contDiffOn_physicalPrecision d).comp_continuousLinearMap
    (ContinuousLinearMap.fst ℝ ℝ (E × E))
  have hb := (contDiffOn_physicalInverseVariance d).comp_continuousLinearMap
    (ContinuousLinearMap.fst ℝ ℝ (E × E))
  have hc := (contDiffOn_physicalTiltScale d).comp_continuousLinearMap
    (ContinuousLinearMap.fst ℝ ℝ (E × E))
  have hx : ContDiffOn ℝ ∞ (centerProjection (ι := ι)) (openDomain (E × E)) :=
    (centerProjection (ι := ι)).contDiff.contDiffOn
  have hy : ContDiffOn ℝ ∞ (stateProjection (ι := ι)) (openDomain (E × E)) :=
    (stateProjection (ι := ι)).contDiff.contDiffOn
  exact polynomialJetBound_prod hU hSU ha ((hb.smul hx).add (hc.smul hy)) n
    (scalar_polynomial_bound d (contDiffOn_physicalPrecision d) n)
    (polynomialJetBound_add hU hSU (hb.smul hx) (hc.smul hy) n
      (polynomialJetBound_smul hU hSU hb hx n
        (fun i _ => scalar_polynomial_bound d (contDiffOn_physicalInverseVariance d) i)
        (fun i _ => polynomialJetBound_linear hU hSU _ i))
      (polynomialJetBound_smul hU hSU hc hy n
        (fun i _ => scalar_polynomial_bound d (contDiffOn_physicalTiltScale d) i)
        (fun i _ => polynomialJetBound_linear hU hSU _ i)))

theorem exists_physicalPrecision_interval :
    ∃ a₀ a₁ : ℝ, 0 < a₀ ∧ a₀ ≤ a₁ ∧
      ∀ t ∈ Icc (left d.b) (right d.b), physicalPrecision d t ∈ Icc a₀ a₁ := by
  have hzero : (0 : ℝ) ∈ Icc (left d.b) (right d.b) := by
    dsimp [left, right]; constructor <;> linarith [d.hb, d.hb1]
  have hc := (contDiffOn_physicalPrecision d).continuousOn.mono
    (construction_subset d.hb d.hb1)
  obtain ⟨s,hs,hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0,hzero⟩ hc
  obtain ⟨t,ht,hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0,hzero⟩ hc
  have hs' := construction_subset d.hb d.hb1 hs
  refine ⟨physicalPrecision d s,physicalPrecision d t,?_,hmin ht,fun u hu => ⟨hmin hu,hmax hu⟩⟩
  exact inv_pos.mpr (mul_pos (by norm_num) (mul_pos (sq_pos_of_pos d.hr)
    (conditionalVariance_pos hs'.1 hs'.2)))

theorem conditionalMean_eq_natural {p : P} (hp : p ∈ openDomain (E × E)) :
    conditionalMean d.F p.2.1 d.r p.1 p.2.2 =
      normalizedGaussianIntegral d.F (gradient d.F) (centerParameters d p) := by
  rw [conditionalMean_eq_integral_heatPosterior d.hF d.hr hp.1 hp.2,
    integral_heatPosterior_eq_normalizedGaussianIntegral d.hF (le_refl 0)
      (mul_pos (sq_pos_of_pos d.hr) (conditionalVariance_pos hp.1 hp.2))
      (by simpa only [zero_mul] using d.hlo), centerParameters_eq_posterior]

/-- Uniform polynomial jets of the actual coefficient, with no bound on the
center or state and no derivatives of the original potential above order two. -/
theorem polynomialJetBound_conditionalMean (n : ℕ) :
    PolynomialJetBound (openDomain (E × E)) (closedSlab (E × E) d.b)
      (fun p : P => conditionalMean d.F p.2.1 d.r p.1 p.2.2) n := by
  have hg : Continuous (gradient d.F) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp
      (d.hF.continuous_fderiv (by norm_num))
  let A := ‖gradient d.F (0 : E)‖ + |d.ell|
  have hA : 0 ≤ A := add_nonneg (norm_nonneg _) (abs_nonneg _)
  have hgrowth (z : E) : ‖gradient d.F z‖ ≤ A*(1+‖z‖)^1 := by
    have h := Gibbs.norm_gradient_le_affine_of_hessian_bounds d.hF (m := 0)
      (by simpa only [zero_mul] using d.hlo) d.hup z
    simp only [abs_zero, max_eq_right (abs_nonneg d.ell)] at h
    dsimp [A]; rw [pow_one]
    nlinarith [norm_nonneg (gradient d.F (0 : E)), norm_nonneg z, abs_nonneg d.ell]
  have hQ := contDiffOn_natural_mean d.hF d.hlo hg hA 1 hgrowth
  obtain ⟨a₀,a₁,ha₀,ha,hprec⟩ := exists_physicalPrecision_interval d
  obtain ⟨B,hB,M,hparam⟩ := polynomialJetBound_centerParameters d 0
  have hweight (p : P) (hp : p ∈ closedSlab (E × E) d.b) :
      1+‖(centerParameters d p).2‖ ≤ (1+B)*(1+‖p‖)^M := by
    have hn := (norm_snd_le (centerParameters d p)).trans (by
      simpa only [norm_iteratedFDerivWithin_zero] using hparam p hp)
    have hpw := one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg p)) (n := M)
    nlinarith
  obtain ⟨C,hC,N,hbound⟩ := Analysis.PolynomialEnvelope.exists_polynomial_comp_jet_bound
    (isOpen_openDomain (E × E)).uniqueDiffOn isOpen_gaussianDomain.uniqueDiffOn
    (closedSlab_subset_openDomain (E × E) d.hb d.hb1) (contDiffOn_centerParameters d) hQ
    (fun _ hp => centerParameters_mem d hp)
    (fun p _ => le_add_of_nonneg_right (norm_nonneg p)) n
    (fun i _ => by
      obtain ⟨C,hC,N,h⟩ := exists_polynomial_normalizedGaussian_jet_bound
        d.hF d.hlo d.hup ha₀ ha hg hA 1 i hgrowth
      refine ⟨C*(1+B)^N, mul_nonneg hC (pow_nonneg (by linarith) _), M*N, ?_⟩
      intro p hp
      calc
        _ ≤ C*(1+‖(centerParameters d p).2‖)^N := h _ (hprec _ hp) _
        _ ≤ C*((1+B)*(1+‖p‖)^M)^N := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) (hweight p hp) N) hC
        _ = _ := by rw [mul_pow, ← pow_mul]; ring)
    (fun i _ => polynomialJetBound_centerParameters d i)
  refine ⟨C,hC,N,fun p hp => ?_⟩
  rw [iteratedFDerivWithin_congr (fun q hq => conditionalMean_eq_natural d hq)
    (closedSlab_subset_openDomain (E × E) d.hb d.hb1 hp) n]
  exact hbound p hp

end AcceleratedLogConcave.Numerics.ConditionalSmoothing
