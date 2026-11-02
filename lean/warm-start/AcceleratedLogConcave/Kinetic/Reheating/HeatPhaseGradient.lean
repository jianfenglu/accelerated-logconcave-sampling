import AcceleratedLogConcave.Kinetic.Reheating.HeatGradient
import AcceleratedLogConcave.Kinetic.GaussianRows

/-! Lifting the genuine weak heat-displacement bound to visible position and
first momentum-chaos functions. Gaussian covariance preserves the sharp constant. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace ContDiff
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.WeightedGradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Reorder phase coordinates to integrate momentum last. -/
def phaseSwap (z : GaussianPhase E) : GaussianPhase E := ((z.1.1,z.2),z.1.2)

omit [BorelSpace E] in
theorem phaseSwap_measurePreserving (μ : Measure E) [IsProbabilityMeasure μ] :
    MeasurePreserving (phaseSwap (E := E)) (gaussianPhaseMeasure μ) (gaussianPhaseMeasure μ) := by
  exact ((measurePreserving_prodAssoc μ (stdGaussian E) (stdGaussian E)).symm
    MeasurableEquiv.prodAssoc).comp
    (((MeasurePreserving.id μ).prod (Measure.measurePreserving_swap
      (μ := stdGaussian E) (ν := stdGaussian E))).comp
      (measurePreserving_prodAssoc μ (stdGaussian E) (stdGaussian E)))

private theorem gaussian_inner_sq (v : E) :
    (∫ p, (inner ℝ v p)^2 ∂stdGaussian E) = ‖v‖^2 := by
  have h := covarianceBilin_apply (IsGaussian.memLp_two_id (μ := stdGaussian E)) v v
  rw [covarianceBilin_stdGaussian] at h
  change inner ℝ v v = _ at h
  simpa only [integral_id_stdGaussian, id_eq, sub_zero, ← pow_two,
    real_inner_self_eq_norm_sq] using h.symm

private theorem gaussian_basis_sum_sq (a : Fin (Module.finrank ℝ E) → ℝ) :
    (∫ p, (∑ i, a i * inner ℝ ((stdOrthonormalBasis ℝ E) i) p)^2 ∂stdGaussian E) =
      ∑ i, (a i)^2 := by
  let b := stdOrthonormalBasis ℝ E
  let v := ∑ i, a i • b i
  have he : (fun p => ∑ i, a i * inner ℝ (b i) p) = fun p => inner ℝ v p := by
    funext p
    simp [v, sum_inner, real_inner_smul_left]
  change (∫ p, (∑ i, a i * inner ℝ (b i) p)^2 ∂stdGaussian E) = _
  simp_rw [congrFun he]
  rw [gaussian_inner_sq, ← b.sum_sq_inner_right v]
  have hv (i) : inner ℝ (b i) v = a i := by
    simp [v, inner_sum, inner_smul_right, b.inner_eq_ite]
  simp only [hv]

private theorem lp_norm_sq {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] {ν : Measure X} (f : Lp F 2 ν) :
    ‖f‖^2 = ∫ x, ‖f x‖^2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

/-- Actual Gaussian covariance for phase fields with arbitrary joint `(x,e)` coefficients. -/
theorem phase_firstChaos_norm_sq (μ : Measure E) [IsProbabilityMeasure μ]
    (F : Lp ℝ 2 (gaussianPhaseMeasure μ))
    (r : Fin (Module.finrank ℝ E) → Lp ℝ 2 (μ.prod (stdGaussian E)))
    (hF : F =ᵐ[gaussianPhaseMeasure μ] fun z =>
      ∑ i, r i (z.1.1,z.2) * inner ℝ ((stdOrthonormalBasis ℝ E) i) z.1.2) :
    ‖F‖^2 = ∑ i, ‖r i‖^2 := by
  let S : Lp ℝ 2 (gaussianPhaseMeasure μ) →ₗᵢ[ℝ] Lp ℝ 2 (gaussianPhaseMeasure μ) :=
    Lp.compMeasurePreservingₗᵢ ℝ phaseSwap (phaseSwap_measurePreserving μ)
  have hS : S F =ᵐ[gaussianPhaseMeasure μ] fun z =>
      ∑ i, r i z.1 * inner ℝ ((stdOrthonormalBasis ℝ E) i) z.2 :=
    (Lp.coeFn_compMeasurePreserving F (phaseSwap_measurePreserving μ)).trans
      ((phaseSwap_measurePreserving μ).quasiMeasurePreserving.ae hF)
  have hi : Integrable (fun z : GaussianPhase E =>
      (∑ i, r i z.1 * inner ℝ ((stdOrthonormalBasis ℝ E) i) z.2)^2) (gaussianPhaseMeasure μ) := by
    apply (Lp.memLp (S F)).integrable_sq.congr
    filter_upwards [hS] with z hz
    rw [hz]
  rw [← S.norm_map F, lp_norm_sq]
  have he : (∫ z, ‖S F z‖^2 ∂gaussianPhaseMeasure μ) =
      ∫ z, (∑ i, r i z.1 * inner ℝ ((stdOrthonormalBasis ℝ E) i) z.2)^2 ∂gaussianPhaseMeasure μ := by
    apply integral_congr_ae
    filter_upwards [hS] with z hz
    rw [hz, Real.norm_eq_abs, sq_abs]
  rw [he]
  change (∫ z, _ ∂(μ.prod (stdGaussian E)).prod (stdGaussian E)) = _
  rw [integral_prod _ hi]
  simp_rw [gaussian_basis_sum_sq]
  rw [integral_finsetSum _ (fun i _ => (Lp.memLp (r i)).integrable_sq)]
  apply Finset.sum_congr rfl
  intro i _
  rw [lp_norm_sq]
  simp only [Real.norm_eq_abs, sq_abs]

omit [BorelSpace E] in
/-- The analogous exact norm identity for a phase field constant in momentum. -/
theorem phase_position_norm_sq (μ : Measure E) [IsProbabilityMeasure μ]
    (F : Lp ℝ 2 (gaussianPhaseMeasure μ)) (r : Lp ℝ 2 (μ.prod (stdGaussian E)))
    (hF : F =ᵐ[gaussianPhaseMeasure μ] fun z => r (z.1.1,z.2)) : ‖F‖^2 = ‖r‖^2 := by
  let S : Lp ℝ 2 (gaussianPhaseMeasure μ) →ₗᵢ[ℝ] Lp ℝ 2 (gaussianPhaseMeasure μ) :=
    Lp.compMeasurePreservingₗᵢ ℝ phaseSwap (phaseSwap_measurePreserving μ)
  have hS : S F =ᵐ[gaussianPhaseMeasure μ] fun z => r z.1 :=
    (Lp.coeFn_compMeasurePreserving F (phaseSwap_measurePreserving μ)).trans
      ((phaseSwap_measurePreserving μ).quasiMeasurePreserving.ae hF)
  have he : S F = Kinetic.hiddenEmbedding μ r := by
    apply Lp.ext
    exact hS.trans (Lp.coeFn_compMeasurePreserving r measurePreserving_fst).symm
  rw [← S.norm_map F, he, (Kinetic.hiddenEmbedding μ).norm_map]

variable (μ : Measure E) [IsProbabilityMeasure μ]

/-- Actual conditional hidden averaging with the phase measure kept explicit. -/
def phaseHiddenAverage : Lp ℝ 2 (gaussianPhaseMeasure μ) →L[ℝ]
    Lp ℝ 2 (μ.prod (stdGaussian E)) := productAverage _ _

/-- Center the actual phase heat observation over its old hidden coordinate. -/
def phaseHeatCenteredPullback (t : ℝ) :
    Lp ℝ 2 ((heatedLaw μ t).prod (stdGaussian E)) →L[ℝ] Lp ℝ 2 (gaussianPhaseMeasure μ) :=
  (heatPullback μ t).toContinuousLinearMap -
    (Kinetic.hiddenEmbedding μ).toContinuousLinearMap.comp
      ((phaseHiddenAverage μ).comp
        (heatPullback μ t).toContinuousLinearMap)

theorem phaseHeatCenteredPullback_coe_of_ae (t : ℝ)
    (F : Lp ℝ 2 ((heatedLaw μ t).prod (stdGaussian E))) (φ : E×E → ℝ)
    (hφ : F =ᵐ[(heatedLaw μ t).prod (stdGaussian E)] φ) :
    phaseHeatCenteredPullback μ t F =ᵐ[gaussianPhaseMeasure μ] fun z =>
      φ (z.1.1+Real.sqrt t•z.2,z.1.2) -
        ∫ y, φ (z.1.1+Real.sqrt t•y,z.1.2) ∂stdGaussian E := by
  have hB : heatPullback μ t F =ᵐ[gaussianPhaseMeasure μ]
      fun z => φ (z.1.1+Real.sqrt t•z.2,z.1.2) :=
    (heatPullback_coe μ t F).trans ((heatObservation_measurePreserving μ t).quasiMeasurePreserving.ae hφ)
  have hA : phaseHiddenAverage μ (heatPullback μ t F) =ᵐ[μ.prod (stdGaussian E)]
      fun xp => ∫ y, (heatPullback μ t F) (xp,y) ∂stdGaussian E :=
    productAverage_coe (μ.prod (stdGaussian E)) (stdGaussian E) (heatPullback μ t F)
  have hAE : phaseHiddenAverage μ (heatPullback μ t F)
      =ᵐ[μ.prod (stdGaussian E)] fun xp => ∫ y, φ (xp.1+Real.sqrt t•y,xp.2) ∂stdGaussian E := by
    filter_upwards [hA, Measure.ae_ae_of_ae_prod hB] with xp hx hy
    rw [hx, integral_congr_ae hy]
  have hI := Lp.coeFn_compMeasurePreserving
    (phaseHiddenAverage μ (heatPullback μ t F))
    (measurePreserving_fst (ν := stdGaussian E))
  filter_upwards [Lp.coeFn_sub (heatPullback μ t F)
    (Kinetic.hiddenEmbedding μ (phaseHiddenAverage μ (heatPullback μ t F))),
    hB, hI, measurePreserving_fst.quasiMeasurePreserving.ae hAE] with z hz hBz hIz hAz
  change (Kinetic.hiddenEmbedding μ
    (phaseHiddenAverage μ (heatPullback μ t F))) z = _ at hIz
  change (phaseHiddenAverage μ (heatPullback μ t F)) z.1 = _ at hAz
  change (heatPullback μ t F - Kinetic.hiddenEmbedding μ
    (phaseHiddenAverage μ (heatPullback μ t F))) z = _
  rw [hz]
  simp only [Pi.sub_apply, hBz, hIz, Function.comp_apply, hAz]

/-- The position sector has exactly the scalar heat-centered norm. -/
theorem phaseHeatCentered_position_norm (t : ℝ) (f : Lp ℝ 2 (heatedLaw μ t)) :
    ‖phaseHeatCenteredPullback μ t (productEmbedding (heatedLaw μ t) (stdGaussian E) f)‖^2 =
      ‖heatCenteredPullback μ t f‖^2 := by
  apply phase_position_norm_sq
  have hF := Lp.coeFn_compMeasurePreserving f (measurePreserving_fst (ν := stdGaussian E))
  have hp : MeasurePreserving (fun z : GaussianPhase E => (z.1.1,z.2))
      (gaussianPhaseMeasure μ) (μ.prod (stdGaussian E)) :=
    measurePreserving_fst.comp (phaseSwap_measurePreserving μ)
  have hr : (fun z : GaussianPhase E => heatCenteredPullback μ t f (z.1.1,z.2)) =ᵐ[gaussianPhaseMeasure μ]
      fun z => f (z.1.1+Real.sqrt t•z.2) - ∫ y, f (z.1.1+Real.sqrt t•y) ∂stdGaussian E :=
    hp.quasiMeasurePreserving.ae (heatCenteredPullback_coe_of_ae μ t f f (Filter.EventuallyEq.rfl))
  exact (phaseHeatCenteredPullback_coe_of_ae μ t
    (productEmbedding (heatedLaw μ t) (stdGaussian E) f) (fun z => f z.1) hF).trans hr.symm

/-- Position outputs of genuine target Sobolev functions obey the phase estimate. -/
theorem phaseHeatCentered_position_closedGradient (t : ℝ) (ht : 0 ≤ t)
    (V : E → ℝ) (hV : ContDiff ℝ 1 V)
    (hI : Integrable (fun x => Real.exp (-V x)))
    (hμ : heatedLaw μ t = volume.tilted (fun x => -V x))
    (u : Sobolev (heatedLaw μ t) V hV hI hμ) :
    ‖phaseHeatCenteredPullback μ t
      (productEmbedding (heatedLaw μ t) (stdGaussian E) (u : Lp ℝ 2 (heatedLaw μ t)))‖^2 ≤
      t*‖closedGradient (heatedLaw μ t) V hV hI hμ u‖^2 := by
  rw [phaseHeatCentered_position_norm]
  exact heatCenteredPullback_closedGradient μ t ht V hV hI hμ u

/-- The true phase heat residual acts on each first-chaos coefficient by the
scalar residual, with no independence assumption on the input function. -/
theorem phaseHeatCentered_components_coe (t : ℝ)
    (F : Lp ℝ 2 ((heatedLaw μ t).prod (stdGaussian E)))
    (f : Fin (Module.finrank ℝ E) → Lp ℝ 2 (heatedLaw μ t))
    (hF : F =ᵐ[(heatedLaw μ t).prod (stdGaussian E)] fun xp =>
      ∑ i, f i xp.1 * inner ℝ ((stdOrthonormalBasis ℝ E) i) xp.2) :
    phaseHeatCenteredPullback μ t F =ᵐ[gaussianPhaseMeasure μ] fun z =>
      ∑ i, heatCenteredPullback μ t (f i) (z.1.1,z.2) *
        inner ℝ ((stdOrthonormalBasis ℝ E) i) z.1.2 := by
  let hp : MeasurePreserving (fun z : E×E => z.1+Real.sqrt t•z.2)
      (μ.prod (stdGaussian E)) (heatedLaw μ t) :=
    (by fun_prop : Measurable (fun z : E×E => z.1+Real.sqrt t•z.2)).measurePreserving _
  have hi (i) : ∀ᵐ x ∂μ, Integrable (fun y => f i (x+Real.sqrt t•y)) (stdGaussian E) := by
    have hcoe : heatScalarPullback μ t (f i) =ᵐ[μ.prod (stdGaussian E)]
        fun z => f i (z.1+Real.sqrt t•z.2) := Lp.coeFn_compMeasurePreserving _ hp
    filter_upwards [((Lp.memLp (heatScalarPullback μ t (f i))).integrable (by norm_num)).prod_right_ae,
      Measure.ae_ae_of_ae_prod hcoe] with x hx hy
    exact hx.congr hy
  have hxmp : MeasurePreserving (fun z : GaussianPhase E => z.1.1) (gaussianPhaseMeasure μ) μ :=
    measurePreserving_fst.comp (measurePreserving_fst (ν := stdGaussian E))
  have hxemp : MeasurePreserving (fun z : GaussianPhase E => (z.1.1,z.2))
      (gaussianPhaseMeasure μ) (μ.prod (stdGaussian E)) :=
    measurePreserving_fst.comp (phaseSwap_measurePreserving μ)
  have hcoeff : ∀ᵐ z ∂gaussianPhaseMeasure μ, ∀ i,
      heatCenteredPullback μ t (f i) (z.1.1,z.2) =
        f i (z.1.1+Real.sqrt t•z.2) - ∫ y, f i (z.1.1+Real.sqrt t•y) ∂stdGaussian E :=
    hxemp.quasiMeasurePreserving.ae (ae_all_iff.mpr fun i =>
      heatCenteredPullback_coe_of_ae μ t (f i) (f i) Filter.EventuallyEq.rfl)
  filter_upwards [phaseHeatCenteredPullback_coe_of_ae μ t F _ hF,
    hxmp.quasiMeasurePreserving.ae (ae_all_iff.mpr hi), hcoeff] with z hz hix hc
  rw [hz]
  rw [integral_finsetSum _ (fun i _ => (hix i).mul_const _)]
  simp_rw [integral_mul_const, hc, sub_mul]
  rw [Finset.sum_sub_distrib]

/-- Exact first-chaos norm decomposition for the heat residual. -/
theorem phaseHeatCentered_momentum_norm (t : ℝ) (G : Lp E 2 (heatedLaw μ t)) :
    ‖phaseHeatCenteredPullback μ t (momentumEmbedding (heatedLaw μ t) G)‖^2 =
      ∑ i : Fin (Module.finrank ℝ E),
        ‖heatCenteredPullback μ t ((innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).compLp G)‖^2 := by
  apply phase_firstChaos_norm_sq
  apply phaseHeatCentered_components_coe
  have hc : ∀ᵐ x ∂heatedLaw μ t, ∀ i : Fin (Module.finrank ℝ E),
      ((innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).compLp G) x =
        inner ℝ ((stdOrthonormalBasis ℝ E) i) (G x) :=
    ae_all_iff.mpr fun i => (innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).coeFn_compLp G
  filter_upwards [momentumEmbedding_coe (heatedLaw μ t) G,
    measurePreserving_fst.quasiMeasurePreserving.ae hc] with xp hx hcx
  rw [hx]
  simp_rw [hcx]
  exact ((stdOrthonormalBasis ℝ E).sum_inner_mul_inner (G xp.1) xp.2).symm.trans
    (Finset.sum_congr rfl fun i _ => by rw [real_inner_comm (G xp.1)])

/-- Genuine weak Hessian rows control the first-chaos heat residual. -/
theorem phaseHeatCentered_momentum_rows (t : ℝ) (ht : 0 ≤ t)
    (V : E → ℝ) (hV : ContDiff ℝ 1 V)
    (hI : Integrable (fun x => Real.exp (-V x)))
    (hμ : heatedLaw μ t = volume.tilted (fun x => -V x))
    (G : Lp E 2 (heatedLaw μ t)) (R : Fin (Module.finrank ℝ E) → Lp E 2 (heatedLaw μ t))
    (hR : ∀ i, ((innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).compLp G, R i) ∈
      (closedGradient (heatedLaw μ t) V hV hI hμ).graph) :
    ‖phaseHeatCenteredPullback μ t (momentumEmbedding (heatedLaw μ t) G)‖^2 ≤
      t * ∑ i, ‖R i‖^2 := by
  rw [phaseHeatCentered_momentum_norm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  obtain ⟨u, hu, he⟩ := (LinearPMap.mem_graph_iff _).mp (hR i)
  have hb := heatCenteredPullback_closedGradient μ t ht V hV hI hμ u
  simpa only [hu, he] using hb

end AcceleratedLogConcave.Kinetic.Reheating
