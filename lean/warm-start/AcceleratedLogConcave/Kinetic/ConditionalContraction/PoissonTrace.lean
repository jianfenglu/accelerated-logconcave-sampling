import AcceleratedLogConcave.Analysis.Bochner
import AcceleratedLogConcave.Kinetic.PhaseTestSlicing

/-!
# Distributional Poisson trace cancellation

Only compact C1 tests are used. In particular, no global L2 premise is made
on the product of the score and the weak Poisson gradient.
-/
noncomputable section
open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.ConditionalContraction
open Analysis.WeightedGradient Analysis.Poisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [IsProbabilityMeasure μ]
  (V : E → ℝ) (hV : ContDiff ℝ 1 V)
  (hI : Integrable (fun x => Real.exp (-V x))) (hμ : μ = volume.tilted (fun x => -V x))

/-- The actual variational equation tested against an arbitrary compact C1 function. -/
theorem weak_poisson_compact_test (G : Lp E 2 μ) (g : Lp ℝ 2 μ)
    (hweak : ∀ v : Sobolev μ V hV hI hμ,
      inner ℝ G (closedGradient μ V hV hI hμ v) = inner ℝ g (v : Lp ℝ 2 μ))
    (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    Integrable (fun x => fderiv ℝ φ x (G x)) μ ∧
    Integrable (fun x => φ x * g x) μ ∧
    (∫ x, fderiv ℝ φ x (G x) ∂μ) = ∫ x, φ x * g x ∂μ := by
  have hv : MemLp φ 2 μ := hφ.continuous.memLp_of_hasCompactSupport hc
  have hD := compact_gradient_memLp μ hφ hc
  obtain ⟨v, hval, hgrad⟩ := (LinearPMap.mem_graph_iff _).mp
    (c1_mem_closedGradient_graph μ V hV hI hμ hφ hv hD)
  have haeD : (fun x => inner ℝ (G x) (closedGradient μ V hV hI hμ v x)) =ᵐ[μ]
      fun x => fderiv ℝ φ x (G x) := by
    filter_upwards [hD.coeFn_toLp] with x hx
    rw [hgrad, hx, inner_gradient_right]
    rfl
  have haev : (fun x => inner ℝ (g x) ((v : Lp ℝ 2 μ) x)) =ᵐ[μ]
      fun x => φ x * g x := by
    filter_upwards [hv.coeFn_toLp] with x hx
    rw [hval, hx]
    rfl
  refine ⟨(L2.integrable_inner G _).congr haeD, (L2.integrable_inner g _).congr haev, ?_⟩
  have hh := hweak v
  rw [L2.inner_def, L2.inner_def, integral_congr_ae haeD, integral_congr_ae haev] at hh
  exact hh

omit [MeasurableSpace E] [BorelSpace E] in
private theorem basis_apply_sum (G : E) (L : E →L[ℝ] ℝ) :
    (∑ i : Fin (Module.finrank ℝ E), inner ℝ ((stdOrthonormalBasis ℝ E) i) G *
      L ((stdOrthonormalBasis ℝ E) i)) = L G := by
  simpa only [map_sum, map_smul, smul_eq_mul] using
    congrArg L ((stdOrthonormalBasis ℝ E).sum_repr' G)

/-- Distributional trace minus score cancellation for genuine closed Hessian
rows. The combined score integrand is integrable because the test is compact. -/
theorem weak_poisson_trace_test (G : Lp E 2 μ) (g : Lp ℝ 2 μ)
    (hweak : ∀ v : Sobolev μ V hV hI hμ,
      inner ℝ G (closedGradient μ V hV hI hμ v) = inner ℝ g (v : Lp ℝ 2 μ))
    (R : Fin (Module.finrank ℝ E) → Lp E 2 μ)
    (hR : ∀ i, ((innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).compLp G, R i) ∈
      (closedGradient μ V hV hI hμ).graph)
    (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    Integrable (fun x => φ x * (∑ i, inner ℝ (R i x) ((stdOrthonormalBasis ℝ E) i) -
      fderiv ℝ V x (G x))) μ ∧
    (∫ x, φ x * (∑ i, inner ℝ (R i x) ((stdOrthonormalBasis ℝ E) i) -
      fderiv ℝ V x (G x)) ∂μ) = -∫ x, φ x * g x ∂μ := by
  classical
  let b := stdOrthonormalBasis ℝ E
  let C (i : Fin (Module.finrank ℝ E)) := (innerSL ℝ (b i)).compLp G
  let F (i : Fin (Module.finrank ℝ E)) (x : E) := φ x * inner ℝ (R i x) (b i)
  let K (i : Fin (Module.finrank ℝ E)) (x : E) :=
    C i x * (fderiv ℝ φ x (b i) - φ x * fderiv ℝ V x (b i))
  have hi (i : Fin (Module.finrank ℝ E)) :
      Integrable (F i) μ ∧ Integrable (K i) μ ∧ (∫ x, F i x ∂μ) = -∫ x, K i x ∂μ := by
    obtain ⟨u, hu, hDu⟩ := (LinearPMap.mem_graph_iff _).mp (hR i)
    simpa only [F, K, C, b, hu, hDu] using
      closedGradient_integrationByParts μ V hV hI hμ u φ hφ hc (b i)
  have hF := integrable_finsetSum Finset.univ (fun i _ => (hi i).1)
  have hK := integrable_finsetSum Finset.univ (fun i _ => (hi i).2.1)
  have hsum : (∫ x, ∑ i, F i x ∂μ) = -∫ x, ∑ i, K i x ∂μ := by
    rw [integral_finsetSum Finset.univ (fun i _ => (hi i).1),
      integral_finsetSum Finset.univ (fun i _ => (hi i).2.1), ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i _ => (hi i).2.2)
  have hKae : (fun x => ∑ i, K i x) =ᵐ[μ]
      fun x => fderiv ℝ φ x (G x) - φ x * fderiv ℝ V x (G x) := by
    filter_upwards [ae_all_iff.mpr (fun i => (innerSL ℝ (b i)).coeFn_compLp G)] with x hx
    simp only [K]
    simp_rw [show ∀ i, C i x = inner ℝ (b i) (G x) from hx]
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [basis_apply_sum]
    have hh := basis_apply_sum (G x) (fderiv ℝ V x)
    have he : (∑ i, inner ℝ (b i) (G x) * (φ x * fderiv ℝ V x (b i))) =
        φ x * ∑ i, inner ℝ (b i) (G x) * fderiv ℝ V x (b i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he, hh]
  have htest := weak_poisson_compact_test μ V hV hI hμ G g hweak φ hφ hc
  have hscore : Integrable (fun x => φ x * fderiv ℝ V x (G x)) μ := by
    have hh := htest.1.sub (hK.congr hKae)
    convert hh using 1
    funext x
    dsimp
    ring
  have hleft : (fun x => φ x * (∑ i, inner ℝ (R i x) (b i) - fderiv ℝ V x (G x))) =
      (fun x => (∑ i, F i x) - φ x * fderiv ℝ V x (G x)) := by
    funext x
    simp only [F, mul_sub, Finset.mul_sum]
  rw [hleft]
  refine ⟨hF.sub hscore, ?_⟩
  have hsub := integral_sub hF hscore
  rw [hsub, hsum, integral_congr_ae hKae, integral_sub htest.1 hscore, htest.2.2]
  ring

end AcceleratedLogConcave.Kinetic.ConditionalContraction
