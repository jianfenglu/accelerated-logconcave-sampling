import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.PhaseRows
import AcceleratedLogConcave.Kinetic.Reheating.Corrector

/-! Exact Green pairings and sharp bounds for both actual Poisson correctors
against the true phase heat generator. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson Analysis.WeightedGradient
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι


/-- The genuine weighted position gradient of the physical phase heat core. -/
def phaseHeatGradientLp {a b : ℝ} (F : ReferencePoissonFamily E a b)
  {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
  (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
  (t : ℝ) (ht : t ∈ Icc a b) : Lp E 2 ((F.law t).prod (stdGaussian E)) :=
  (compactPhaseHeatQuotient_memLp F hf hc hheat t ht).2.1.toLp _

/-- The genuine weighted generator of the physical phase heat core. -/
def phaseHeatGeneratorLp {a b : ℝ} (F : ReferencePoissonFamily E a b)
  {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
  (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
  (t : ℝ) (ht : t ∈ Icc a b) : Lp ℝ 2 ((F.law t).prod (stdGaussian E)) :=
  (compactPhaseHeatQuotient_memLp F hf hc hheat t ht).2.2.toLp _

/-- Green's identity for a position Sobolev test, in the actual product Hilbert space. -/
theorem phaseHeat_green_position {a b : ℝ} (F : ReferencePoissonFamily E a b)
  {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
  (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
  (t : ℝ) (ht : t ∈ Icc a b)
    (u : Sobolev (F.law t) (F.potential t) ((F.potential_C2 t).of_le (by norm_num))
      (F.integrable t ht) (F.gibbs_law t ht)) :
    inner ℝ (phaseHeatGeneratorLp F hf hc hheat t ht)
      (productEmbedding (F.law t) (stdGaussian E) (u : Lp ℝ 2 (F.law t))) =
    inner ℝ (phaseHeatGradientLp F hf hc hheat t ht)
      (Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst
        (closedGradient (F.law t) (F.potential t) ((F.potential_C2 t).of_le (by norm_num))
          (F.integrable t ht) (F.gibbs_law t ht) u)) := by
  let Du := closedGradient (F.law t) (F.potential t) ((F.potential_C2 t).of_le (by norm_num))
    (F.integrable t ht) (F.gibbs_law t ht) u
  let r := (memLp_const (1:ℝ) (μ := stdGaussian E) (p := 2)).toLp (fun _ => 1)
  have hr : r =ᵐ[stdGaussian E] fun _ => 1 := (memLp_const (1:ℝ)).coeFn_toLp
  have he := (compactPhaseHeatQuotient_green_tensor F hf hc hheat t ht u r).2.2
  have he' : (∫ z, inner ℝ (compactPhaseHeatGradient F f t z) (Du z.1)
      ∂(F.law t).prod (stdGaussian E)) =
      ∫ z, compactPhaseHeatGenerator F f t z * (u : Lp ℝ 2 (F.law t)) z.1
      ∂(F.law t).prod (stdGaussian E) := by
    convert he using 1 <;> apply integral_congr_ae
    · filter_upwards [measurePreserving_snd.quasiMeasurePreserving.ae hr] with z hz
      simp only [hz, one_smul]
      rfl
    · filter_upwards [measurePreserving_snd.quasiMeasurePreserving.ae hr] with z hz
      simp only [hz, one_mul]
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ z, compactPhaseHeatGenerator F f t z * (u : Lp ℝ 2 (F.law t)) z.1
        ∂(F.law t).prod (stdGaussian E) := by
      apply integral_congr_ae
      filter_upwards [(compactPhaseHeatQuotient_memLp F hf hc hheat t ht).2.2.coeFn_toLp,
        Lp.coeFn_compMeasurePreserving (u : Lp ℝ 2 (F.law t)) (measurePreserving_fst (ν := stdGaussian E))] with z hz hu
      change (productEmbedding (F.law t) (stdGaussian E) (u : Lp ℝ 2 (F.law t))) z *
        (phaseHeatGeneratorLp F hf hc hheat t ht) z = _
      change (phaseHeatGeneratorLp F hf hc hheat t ht) z = _ at hz
      change (productEmbedding (F.law t) (stdGaussian E) (u : Lp ℝ 2 (F.law t))) z = _ at hu
      rw [hz, hu, mul_comm]
      rfl
    _ = _ := he'.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [(compactPhaseHeatQuotient_memLp F hf hc hheat t ht).2.1.coeFn_toLp,
        Lp.coeFn_compMeasurePreserving Du (measurePreserving_fst (ν := stdGaussian E))] with z hz hu
      change (phaseHeatGradientLp F hf hc hheat t ht) z = _ at hz
      rw [hz]
      change inner ℝ (compactPhaseHeatGradient F f t z) (Du z.1) =
        inner ℝ (compactPhaseHeatGradient F f t z) ((Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst Du) z)
      change (Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst Du) z = Du z.1 at hu
      rw [hu]

/-- Both factors are genuine L2 objects, so the position Green bound is sharp. -/
theorem phaseHeat_green_position_bound {a b : ℝ} (F : ReferencePoissonFamily E a b)
  {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
  (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
  (t : ℝ) (ht : t ∈ Icc a b)
    (u : Sobolev (F.law t) (F.potential t) ((F.potential_C2 t).of_le (by norm_num))
      (F.integrable t ht) (F.gibbs_law t ht)) :
    |inner ℝ (phaseHeatGeneratorLp F hf hc hheat t ht)
      (productEmbedding (F.law t) (stdGaussian E) (u : Lp ℝ 2 (F.law t)))| ≤
      ‖phaseHeatGradientLp F hf hc hheat t ht‖ *
        ‖closedGradient (F.law t) (F.potential t) ((F.potential_C2 t).of_le (by norm_num))
          (F.integrable t ht) (F.gibbs_law t ht) u‖ := by
  rw [phaseHeat_green_position]
  simpa only [LinearIsometry.norm_map] using abs_real_inner_le_norm
    (phaseHeatGradientLp F hf hc hheat t ht)
    (Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst
      (closedGradient (F.law t) (F.potential t) ((F.potential_C2 t).of_le (by norm_num))
        (F.integrable t ht) (F.gibbs_law t ht) u))

/-- Green's identity with genuine weak Hessian rows and the actual momentum chaos. -/
theorem phaseHeat_green_rows {a b : ℝ} (F : ReferencePoissonFamily E a b)
  {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
  (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
  (t : ℝ) (ht : t ∈ Icc a b) (G : Lp E 2 (F.law t))
    (R : Fin (Module.finrank ℝ E) → Lp E 2 (F.law t))
    (hR : ∀ j, ((innerSL ℝ ((stdOrthonormalBasis ℝ E) j)).compLp G, R j) ∈
      (closedGradient (F.law t) (F.potential t) ((F.potential_C2 t).of_le (by norm_num))
        (F.integrable t ht) (F.gibbs_law t ht)).graph) :
    inner ℝ (phaseHeatGeneratorLp F hf hc hheat t ht) (momentumEmbedding (F.law t) G) =
    inner ℝ (phaseHeatGradientLp F hf hc hheat t ht) (momentumRowField (F.law t) R) := by
  classical
  let b := stdOrthonormalBasis ℝ E
  let D := closedGradient (F.law t) (F.potential t) ((F.potential_C2 t).of_le (by norm_num))
    (F.integrable t ht) (F.gibbs_law t ht)
  have hu : ∀ j, ∃ u : D.domain, (u : Lp ℝ 2 (F.law t)) = (innerSL ℝ (b j)).compLp G ∧ D u = R j :=
    fun j => (LinearPMap.mem_graph_iff _).mp (hR j)
  choose u hu hdu using hu
  let r := fun j => (IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ (b j)) 2 (by norm_num)).toLp _
  have hr (j) : r j =ᵐ[stdGaussian E] fun p => inner ℝ (b j) p :=
    (IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ (b j)) 2 (by norm_num)).coeFn_toLp
  have he (j) := compactPhaseHeatQuotient_green_tensor F hf hc hheat t ht (u j) (r j)
  let left := fun j (z : E×E) => inner ℝ (compactPhaseHeatGradient F f t z) (r j z.2 • D (u j) z.1)
  let right := fun j (z : E×E) => compactPhaseHeatGenerator F f t z * (r j z.2 * (u j : Lp ℝ 2 (F.law t)) z.1)
  have hleft (j) : Integrable (left j) ((F.law t).prod (stdGaussian E)) := (he j).1
  have hright (j) : Integrable (right j) ((F.law t).prod (stdGaussian E)) := (he j).2.1
  have hlef : (fun z => inner ℝ (phaseHeatGradientLp F hf hc hheat t ht z)
      (momentumRowField (F.law t) R z)) =ᵐ[(F.law t).prod (stdGaussian E)] fun z => ∑ j, left j z := by
    filter_upwards [(compactPhaseHeatQuotient_memLp F hf hc hheat t ht).2.1.coeFn_toLp,
      momentumRowField_coe (F.law t) R,
      measurePreserving_snd.quasiMeasurePreserving.ae (ae_all_iff.mpr hr)] with z hz hrow hrz
    change phaseHeatGradientLp F hf hc hheat t ht z = _ at hz
    rw [hz, hrow, inner_sum]
    apply Finset.sum_congr rfl
    intro j _
    change _ = inner ℝ (compactPhaseHeatGradient F f t z) (r j z.2 • D (u j) z.1)
    rw [hrz, hdu]
  have hcoord (j) : (u j : Lp ℝ 2 (F.law t)) =ᵐ[F.law t] fun x => inner ℝ (b j) (G x) := by
    rw [hu]
    exact (innerSL ℝ (b j)).coeFn_compLp G
  have hrig : (fun z => inner ℝ (phaseHeatGeneratorLp F hf hc hheat t ht z)
      (momentumEmbedding (F.law t) G z)) =ᵐ[(F.law t).prod (stdGaussian E)] fun z => ∑ j, right j z := by
    filter_upwards [(compactPhaseHeatQuotient_memLp F hf hc hheat t ht).2.2.coeFn_toLp,
      momentumEmbedding_coe (F.law t) G,
      measurePreserving_snd.quasiMeasurePreserving.ae (ae_all_iff.mpr hr),
      measurePreserving_fst.quasiMeasurePreserving.ae (ae_all_iff.mpr hcoord)] with z hz hG hrz huz
    change phaseHeatGeneratorLp F hf hc hheat t ht z = _ at hz
    change momentumEmbedding (F.law t) G z * phaseHeatGeneratorLp F hf hc hheat t ht z = _
    rw [hz, hG]
    have hGsum : inner ℝ (G z.1) z.2 = ∑ j, inner ℝ (b j) (G z.1) * inner ℝ (b j) z.2 := by
      conv_lhs => rw [← b.sum_repr' (G z.1)]
      simp only [sum_inner, real_inner_smul_left]
    rw [hGsum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    change _ = compactPhaseHeatGenerator F f t z * (r j z.2 * (u j : Lp ℝ 2 (F.law t)) z.1)
    rw [hrz, huz]
    ring
  rw [L2.inner_def, L2.inner_def, integral_congr_ae hrig, integral_congr_ae hlef,
    integral_finsetSum _ (fun j _ => hright j), integral_finsetSum _ (fun j _ => hleft j)]
  exact Finset.sum_congr rfl (fun j _ => (he j).2.2.symm)

/-- Sharp momentum Green bound, with the actual weak Hessian row energy. -/
theorem phaseHeat_green_rows_bound {a b : ℝ} (F : ReferencePoissonFamily E a b)
  {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
  (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
  (t : ℝ) (ht : t ∈ Icc a b) (G : Lp E 2 (F.law t))
    (R : Fin (Module.finrank ℝ E) → Lp E 2 (F.law t))
    (hR : ∀ j, ((innerSL ℝ ((stdOrthonormalBasis ℝ E) j)).compLp G, R j) ∈
      (closedGradient (F.law t) (F.potential t) ((F.potential_C2 t).of_le (by norm_num))
        (F.integrable t ht) (F.gibbs_law t ht)).graph) :
    |inner ℝ (phaseHeatGeneratorLp F hf hc hheat t ht) (momentumEmbedding (F.law t) G)| ≤
      ‖phaseHeatGradientLp F hf hc hheat t ht‖ * Real.sqrt (∑ j, ‖R j‖^2) := by
  rw [phaseHeat_green_rows F hf hc hheat t ht G R hR]
  have hn : ‖momentumRowField (F.law t) R‖ = Real.sqrt (∑ j, ‖R j‖^2) := by
    rw [← momentumRowField_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  simpa only [hn] using abs_real_inner_le_norm (phaseHeatGradientLp F hf hc hheat t ht)
    (momentumRowField (F.law t) R)

end AcceleratedLogConcave.Kinetic.Reheating
