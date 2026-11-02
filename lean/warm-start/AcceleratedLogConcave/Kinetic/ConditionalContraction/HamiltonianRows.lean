import AcceleratedLogConcave.Kinetic.ConditionalContraction.HamiltonianIBP
import AcceleratedLogConcave.Kinetic.PositionGradient

/-! Summed actual Hamiltonian integration by parts for the genuine closed
Hessian rows, before the Poisson trace cancellation. -/
noncomputable section
open MeasureTheory InnerProductSpace ProbabilityTheory
open scoped ContDiff RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.ConditionalContraction
open Analysis.WeightedGradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual Hamiltonian derivative in orthonormal coordinates. -/
def hamiltonianTestDerivative (V : E → ℝ) (s n : ℝ)
    (φ : GaussianPhase E → ℝ) (z : GaussianPhase E) : ℝ :=
  ∑ j : Fin (Module.finrank ℝ E),
    ((s * inner ℝ ((stdOrthonormalBasis ℝ E) j) z.1.2 -
      n * inner ℝ ((stdOrthonormalBasis ℝ E) j) z.2) *
      fderiv ℝ φ z ((((stdOrthonormalBasis ℝ E) j),0),0) -
    fderiv ℝ V z.1.1 ((stdOrthonormalBasis ℝ E) j) *
      (s * fderiv ℝ φ z ((0,((stdOrthonormalBasis ℝ E) j)),0) -
        n * fderiv ℝ φ z ((0,0),((stdOrthonormalBasis ℝ E) j))))

omit [MeasurableSpace E] [BorelSpace E] in
/-- The coordinate definition is the derivative along the actual source
Hamiltonian vector field `s T_P - n T_E`. -/
theorem hamiltonianTestDerivative_eq_fderiv (V : E → ℝ) (s n : ℝ)
    (φ : GaussianPhase E → ℝ) (z : GaussianPhase E) :
    hamiltonianTestDerivative V s n φ z =
      fderiv ℝ φ z ((s • z.1.2 - n • z.2, -s • gradient V z.1.1), n • gradient V z.1.1) := by
  let b := stdOrthonormalBasis ℝ E
  let L := fderiv ℝ φ z
  let dx : E →L[ℝ] GaussianPhase E :=
    (ContinuousLinearMap.inl ℝ (E×E) E).comp (ContinuousLinearMap.inl ℝ E E)
  let dp : E →L[ℝ] GaussianPhase E :=
    (ContinuousLinearMap.inl ℝ (E×E) E).comp (ContinuousLinearMap.inr ℝ E E)
  let de : E →L[ℝ] GaussianPhase E := ContinuousLinearMap.inr ℝ (E×E) E
  have hd (J : E →L[ℝ] GaussianPhase E) (x : E) :
      (∑ i, inner ℝ (b i) x * L (J (b i))) = L (J x) := by
    simpa only [map_sum, map_smul, smul_eq_mul, ContinuousLinearMap.comp_apply] using
      congrArg (L.comp J) (b.sum_repr' x)
  have hx (i : Fin (Module.finrank ℝ E)) :
      (s * inner ℝ (b i) z.1.2 - n * inner ℝ (b i) z.2) * L ((b i,0),0) -
        fderiv ℝ V z.1.1 (b i) * (s * L ((0,b i),0) - n * L ((0,0),b i)) =
      s * (inner ℝ (b i) z.1.2 * L (dx (b i))) -
        n * (inner ℝ (b i) z.2 * L (dx (b i))) -
        s * (inner ℝ (b i) (gradient V z.1.1) * L (dp (b i))) +
        n * (inner ℝ (b i) (gradient V z.1.1) * L (de (b i))) := by
    simp only [inner_gradient_right, conj_trivial]
    change _ = s * (inner ℝ (b i) z.1.2 * L ((b i,0),0)) -
      n * (inner ℝ (b i) z.2 * L ((b i,0),0)) -
      s * (fderiv ℝ V z.1.1 (b i) * L ((0,b i),0)) +
      n * (fderiv ℝ V z.1.1 (b i) * L ((0,0),b i))
    ring
  change (∑ i, ((s * inner ℝ (b i) z.1.2 - n * inner ℝ (b i) z.2) * L ((b i,0),0) -
    fderiv ℝ V z.1.1 (b i) * (s * L ((0,b i),0) - n * L ((0,0),b i)))) = _
  simp_rw [hx]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hd]
  change s * L ((z.1.2,0),0) - n * L ((z.2,0),0) - s * L ((0,gradient V z.1.1),0) +
    n * L ((0,0),gradient V z.1.1) = _
  have he : ((s • z.1.2 - n • z.2, -s • gradient V z.1.1), n • gradient V z.1.1) =
      s • ((z.1.2,0),0) - n • ((z.2,0),0) - s • ((0,gradient V z.1.1),0) +
        n • ((0,0),gradient V z.1.1) := by
    ext <;> simp [sub_eq_add_neg, neg_smul]
  rw [he]
  simp only [map_add, map_sub, map_smul, smul_eq_mul]
  rfl

/-- Full arbitrary-test Hamiltonian identity for the first momentum chaos.
The score product occurs only under a compact test. -/
theorem phase_hamiltonian_rows_ibp (μ : Measure E) [IsProbabilityMeasure μ]
    (V : E → ℝ) (hV : ContDiff ℝ 1 V)
    (hI : Integrable (fun x => Real.exp (-V x))) (hμ : μ = volume.tilted (fun x => -V x))
    (G : Lp E 2 μ) (R : Fin (Module.finrank ℝ E) → Lp E 2 μ)
    (hR : ∀ i, ((innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).compLp G, R i) ∈
      (closedGradient μ V hV hI hμ).graph) (s n : ℝ)
    (φ : GaussianPhase E → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    Integrable (fun z => gaussianMomentumEmbedding μ G z * hamiltonianTestDerivative V s n φ z)
      (gaussianPhaseMeasure μ) ∧
    (∫ z, gaussianMomentumEmbedding μ G z * hamiltonianTestDerivative V s n φ z
      ∂gaussianPhaseMeasure μ) =
      -(∫ z, ∑ i, ∑ j, φ z * inner ℝ (R i z.1.1) ((stdOrthonormalBasis ℝ E) j) *
        inner ℝ ((stdOrthonormalBasis ℝ E) i) z.1.2 *
        (s * inner ℝ ((stdOrthonormalBasis ℝ E) j) z.1.2 -
          n * inner ℝ ((stdOrthonormalBasis ℝ E) j) z.2) ∂gaussianPhaseMeasure μ) +
      s * ∫ z, φ z * fderiv ℝ V z.1.1 (G z.1.1) ∂gaussianPhaseMeasure μ := by
  classical
  let b := stdOrthonormalBasis ℝ E
  let C (i : Fin (Module.finrank ℝ E)) := (innerSL ℝ (b i)).compLp G
  let W (i j : Fin (Module.finrank ℝ E)) (z : GaussianPhase E) :=
    C i z.1.1 * inner ℝ (b i) z.1.2 *
      ((s * inner ℝ (b j) z.1.2 - n * inner ℝ (b j) z.2) * fderiv ℝ φ z ((b j,0),0) -
        fderiv ℝ V z.1.1 (b j) * (s * fderiv ℝ φ z ((0,b j),0) - n * fderiv ℝ φ z ((0,0),b j)))
  let F (i j : Fin (Module.finrank ℝ E)) (z : GaussianPhase E) :=
    φ z * inner ℝ (R i z.1.1) (b j) * inner ℝ (b i) z.1.2 *
      (s * inner ℝ (b j) z.1.2 - n * inner ℝ (b j) z.2)
  let H (i j : Fin (Module.finrank ℝ E)) (z : GaussianPhase E) :=
    C i z.1.1 * fderiv ℝ V z.1.1 (b j) * φ z
  have hi (i j : Fin (Module.finrank ℝ E)) : Integrable (W i j) (gaussianPhaseMeasure μ) ∧
      (∫ z, W i j z ∂gaussianPhaseMeasure μ) =
      -(∫ z, F i j z ∂gaussianPhaseMeasure μ) + s * inner ℝ (b i) (b j) *
        ∫ z, H i j z ∂gaussianPhaseMeasure μ := by
    obtain ⟨u, hu, hDu⟩ := (LinearPMap.mem_graph_iff _).mp (hR i)
    simpa only [W, F, H, C, b, hu, hDu] using
      phase_hamiltonian_component_ibp μ V hV hI hμ u (b i) (b j) s n φ hφ hc
  have hpos : MeasurePreserving (fun z : GaussianPhase E => z.1.1) (gaussianPhaseMeasure μ) μ :=
    measurePreserving_fst.comp measurePreserving_fst
  have hF (i j : Fin (Module.finrank ℝ E)) : Integrable (F i j) (gaussianPhaseMeasure μ) := by
    have hcF : MemLp (fun z : GaussianPhase E => φ z * inner ℝ (b i) z.1.2 *
        (s * inner ℝ (b j) z.1.2 - n * inner ℝ (b j) z.2)) 2 (gaussianPhaseMeasure μ) := by
      apply Continuous.memLp_of_hasCompactSupport
      · fun_prop
      · exact hc.mul_right.mul_right
    have hh := hcF.integrable_mul (((Lp.memLp (R i)).inner_const (b j)).comp_measurePreserving hpos)
    convert hh using 1
    funext z
    dsimp [F]
    ring
  have hH (i : Fin (Module.finrank ℝ E)) : Integrable (H i i) (gaussianPhaseMeasure μ) :=
    phase_compact_position_integrable μ (C i) (fun x => fderiv ℝ V x (b i))
      ((hV.continuous_fderiv one_ne_zero).clm_apply continuous_const) φ hφ.continuous hc
  have hsumW := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => (hi i j).1))
  have hsumF := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hF i j))
  have hae : (fun z => ∑ i, ∑ j, W i j z) =ᵐ[gaussianPhaseMeasure μ]
      fun z => gaussianMomentumEmbedding μ G z * hamiltonianTestDerivative V s n φ z := by
    filter_upwards [gaussianMomentumEmbedding_coe_components μ G] with z hz
    rw [hz]
    simp only [W, hamiltonianTestDerivative, C, b, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  have hscore : (fun z => ∑ i, H i i z) =ᵐ[gaussianPhaseMeasure μ]
      fun z => φ z * fderiv ℝ V z.1.1 (G z.1.1) := by
    filter_upwards [hpos.quasiMeasurePreserving.ae
      (ae_all_iff.mpr (fun i => (innerSL ℝ (b i)).coeFn_compLp G))] with z hz
    simp only [H, C]
    simp_rw [hz]
    simp only [innerSL_apply_apply]
    rw [← Finset.sum_mul]
    have hlin := congrArg (fderiv ℝ V z.1.1) (b.sum_repr' (G z.1.1))
    simp only [map_sum, map_smul, smul_eq_mul] at hlin
    rw [hlin, mul_comm]
  refine ⟨hsumW.congr hae, ?_⟩
  rw [← integral_congr_ae hae]
  change (∫ z, ∑ i, ∑ j, W i j z ∂gaussianPhaseMeasure μ) =
    -(∫ z, ∑ i, ∑ j, F i j z ∂gaussianPhaseMeasure μ) +
      s * ∫ z, φ z * fderiv ℝ V z.1.1 (G z.1.1) ∂gaussianPhaseMeasure μ
  rw [integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => (hi i j).1))]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => (hi _ j).1), fun i j => (hi i j).2]
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, b.inner_eq_ite]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]
  rw [← Finset.mul_sum, ← integral_finsetSum Finset.univ (fun i _ => hH i),
    integral_congr_ae hscore]
  congr 2
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hF i j))]
  apply Finset.sum_congr rfl
  intro i _
  exact (integral_finsetSum Finset.univ (fun j _ => hF i j)).symm

end AcceleratedLogConcave.Kinetic.ConditionalContraction
