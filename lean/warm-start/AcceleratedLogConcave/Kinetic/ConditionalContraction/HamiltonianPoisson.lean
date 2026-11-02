import AcceleratedLogConcave.Kinetic.ConditionalContraction.HamiltonianRows
import AcceleratedLogConcave.Kinetic.ConditionalContraction.PhasePoissonTrace

/-! The genuine L2 Hamiltonian image of the Poisson momentum lift. -/
noncomputable section
open MeasureTheory InnerProductSpace ProbabilityTheory
open scoped ContDiff RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.ConditionalContraction
open Analysis.WeightedGradient Analysis.Poisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual row-chaos representative, with its trace correction exposed. -/
theorem hamiltonianField_rows_coe (μ : Measure E) [IsProbabilityMeasure μ]
    (R : Fin (Module.finrank ℝ E) → Lp E 2 μ) (s n : ℝ) :
    hamiltonianField μ (stdOrthonormalBasis ℝ E) (rowCoefficients μ R) s n =ᵐ[gaussianPhaseMeasure μ]
      fun z => -(∑ i, ∑ j, inner ℝ (R i z.1.1) ((stdOrthonormalBasis ℝ E) j) *
        inner ℝ ((stdOrthonormalBasis ℝ E) i) z.1.2 *
        (s * inner ℝ ((stdOrthonormalBasis ℝ E) j) z.1.2 - n * inner ℝ ((stdOrthonormalBasis ℝ E) j) z.2)) +
        s * ∑ i, inner ℝ (R i z.1.1) ((stdOrthonormalBasis ℝ E) i) := by
  classical
  let b := stdOrthonormalBasis ℝ E
  let B := rowCoefficients μ R
  let Q := quadraticField μ b B
  let M := mixedField μ b B
  have hpos : MeasurePreserving (fun z : GaussianPhase E => z.1.1) (gaussianPhaseMeasure μ) μ :=
    measurePreserving_fst.comp measurePreserving_fst
  filter_upwards [Lp.coeFn_add (-s • Q) (n • M), Lp.coeFn_smul (-s) Q, Lp.coeFn_smul n M,
    quadraticField_coe μ b B, mixedField_coe μ b B,
    hpos.quasiMeasurePreserving.ae (ae_all_iff.mpr (fun i => ae_all_iff.mpr
      (fun j => (innerSL ℝ (b j)).coeFn_compLp (R i))))] with z ha hs hn hq hm hb
  change (-s • Q + n • M) z = _
  rw [ha, Pi.add_apply, hs, hn, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, hq, hm]
  have hB (i j) : B i j z.1.1 = inner ℝ (R i z.1.1) (b j) := by
    exact (hb i j).trans (real_inner_comm _ _)
  simp_rw [hB]
  calc
    _ = ∑ i, ∑ j, (-(inner ℝ (R i z.1.1) (b j) * inner ℝ (b i) z.1.2 *
        (s * inner ℝ (b j) z.1.2 - n * inner ℝ (b j) z.2)) +
        s * inner ℝ (R i z.1.1) (b j) * inner ℝ (b i) (b j)) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, b.inner_eq_ite]
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      rw [← Finset.mul_sum]

/-- Genuine distributional Hamiltonian action of a Poisson gradient lift.
The macroscopic forcing and microscopic chaos are both actual L2 functions;
the score term has cancelled before the resulting identity is stated. -/
theorem phase_hamiltonian_poisson_ibp (μ : Measure E) [IsProbabilityMeasure μ]
    (V : E → ℝ) (hV : ContDiff ℝ 1 V)
    (hI : Integrable (fun x => Real.exp (-V x))) (hμ : μ = volume.tilted (fun x => -V x))
    (G : Lp E 2 μ) (g : Lp ℝ 2 μ)
    (hweak : ∀ v : Sobolev μ V hV hI hμ,
      inner ℝ G (closedGradient μ V hV hI hμ v) = inner ℝ g (v : Lp ℝ 2 μ))
    (R : Fin (Module.finrank ℝ E) → Lp E 2 μ)
    (hR : ∀ i, ((innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).compLp G, R i) ∈
      (closedGradient μ V hV hI hμ).graph) (s n : ℝ)
    (φ : GaussianPhase E → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    Integrable (fun z => gaussianMomentumEmbedding μ G z * hamiltonianTestDerivative V s n φ z)
      (gaussianPhaseMeasure μ) ∧
    (∫ z, gaussianMomentumEmbedding μ G z * hamiltonianTestDerivative V s n φ z
      ∂gaussianPhaseMeasure μ) =
      (∫ z, φ z * hamiltonianField μ (stdOrthonormalBasis ℝ E) (rowCoefficients μ R) s n z
        ∂gaussianPhaseMeasure μ) + s * ∫ z, φ z * g z.1.1 ∂gaussianPhaseMeasure μ := by
  classical
  let b := stdOrthonormalBasis ℝ E
  let K := hamiltonianField μ b (rowCoefficients μ R) s n
  let F : GaussianPhase E → ℝ := fun z => ∑ i, ∑ j,
    inner ℝ (R i z.1.1) (b j) * inner ℝ (b i) z.1.2 *
      (s * inner ℝ (b j) z.1.2 - n * inner ℝ (b j) z.2)
  let T : GaussianPhase E → ℝ := fun z => ∑ i, inner ℝ (R i z.1.1) (b i)
  let S : GaussianPhase E → ℝ := fun z => fderiv ℝ V z.1.1 (G z.1.1)
  have hpos : MeasurePreserving (fun z : GaussianPhase E => z.1.1) (gaussianPhaseMeasure μ) μ :=
    measurePreserving_fst.comp measurePreserving_fst
  have hφLp : MemLp φ 2 (gaussianPhaseMeasure μ) := hφ.continuous.memLp_of_hasCompactSupport hc
  have hK : Integrable (fun z => φ z * K z) (gaussianPhaseMeasure μ) := hφLp.integrable_mul (Lp.memLp K)
  have hT : Integrable (fun z => φ z * T z) (gaussianPhaseMeasure μ) := by
    have hh := integrable_finsetSum Finset.univ (fun i _ =>
      hφLp.integrable_mul (((Lp.memLp (R i)).inner_const (b i)).comp_measurePreserving hpos))
    simpa only [T, Finset.mul_sum, Pi.mul_apply, Function.comp_apply] using hh
  have htrace := phase_weak_poisson_trace_test μ V hV hI hμ G g hweak R hR φ hφ hc
  have hS : Integrable (fun z => φ z * S z) (gaussianPhaseMeasure μ) := by
    have hh := hT.sub htrace.1
    convert hh using 1
    funext z
    dsimp [T, S, b]
    ring
  have hcoef : (fun z => φ z * K z) =ᵐ[gaussianPhaseMeasure μ]
      fun z => -(φ z * F z) + s * (φ z * T z) := by
    filter_upwards [hamiltonianField_rows_coe μ R s n] with z hz
    rw [show K z = -F z + s * T z from hz]
    ring
  have hF : Integrable (fun z => φ z * F z) (gaussianPhaseMeasure μ) := by
    have hh := (hT.const_mul s).sub hK
    apply hh.congr
    filter_upwards [hcoef] with z hz
    dsimp only [Pi.sub_apply]
    linarith
  have hKi : (∫ z, φ z * K z ∂gaussianPhaseMeasure μ) =
      -(∫ z, φ z * F z ∂gaussianPhaseMeasure μ) +
        s * ∫ z, φ z * T z ∂gaussianPhaseMeasure μ := by
    have hadd := integral_add hF.neg (hT.const_mul s)
    simp only [Pi.neg_apply] at hadd
    rw [integral_congr_ae hcoef, hadd, integral_neg, integral_const_mul]
  have hTi : (∫ z, φ z * S z ∂gaussianPhaseMeasure μ) =
      (∫ z, φ z * T z ∂gaussianPhaseMeasure μ) + ∫ z, φ z * g z.1.1 ∂gaussianPhaseMeasure μ := by
    have hh := htrace.2
    have he : (fun z => φ z * (∑ i, inner ℝ (R i z.1.1) ((stdOrthonormalBasis ℝ E) i) -
        fderiv ℝ V z.1.1 (G z.1.1))) = (fun z => φ z * T z - φ z * S z) := by
      funext z
      exact mul_sub _ _ _
    rw [he, integral_sub hT hS] at hh
    linarith
  have hrows := phase_hamiltonian_rows_ibp μ V hV hI hμ G R hR s n φ hφ hc
  refine ⟨hrows.1, ?_⟩
  rw [hrows.2]
  change -(∫ z, ∑ i, ∑ j, _ ∂gaussianPhaseMeasure μ) + s * (∫ z, φ z * S z ∂gaussianPhaseMeasure μ) =
    (∫ z, φ z * K z ∂gaussianPhaseMeasure μ) + s * ∫ z, φ z * g z.1.1 ∂gaussianPhaseMeasure μ
  have he : (fun z : GaussianPhase E => ∑ i, ∑ j, φ z * inner ℝ (R i z.1.1) (b j) *
      inner ℝ (b i) z.1.2 * (s * inner ℝ (b j) z.1.2 - n * inner ℝ (b j) z.2)) =
      (fun z => φ z * F z) := by
    funext z
    simp only [F, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, hKi, hTi]
  ring

end AcceleratedLogConcave.Kinetic.ConditionalContraction
