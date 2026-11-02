import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution
import AcceleratedLogConcave.Kinetic.ReferenceFlow.GaussianDensity
import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.ReferenceHeat

/-! The actual heat transition carries a reference density to its Gaussian
convolution. This is a measure identity proved by translation invariance and
Tonelli; no heat marginal formula is an assumption. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace AcceleratedLogConcave.Kinetic.Reheating
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem heatedLaw_withDensity_lintegral (p : E → ℝ≥0∞) (hp : Measurable p)
    (t : ℝ) [SFinite (volume.withDensity p)] :
    heatedLaw (volume.withDensity p) t = volume.withDensity
      (fun y => ∫⁻ g, p (y - Real.sqrt t • g) ∂stdGaussian E) := by
  apply Measure.ext_of_lintegral
  intro φ hφ
  have hm : Measurable (fun z : E×E => p (z.1 - Real.sqrt t • z.2) * φ z.1) := by fun_prop
  rw [heatedLaw, lintegral_map hφ (by fun_prop), lintegral_prod _ (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ hp (by fun_prop)]
  simp only [Pi.mul_apply]
  have hl : (∫⁻ x, p x * ∫⁻ g, φ (x + Real.sqrt t • g) ∂stdGaussian E) =
      ∫⁻ g, (∫⁻ x, p x * φ (x + Real.sqrt t • g)) ∂stdGaussian E := by
    calc
      _ = ∫⁻ x, ∫⁻ g, p x * φ (x + Real.sqrt t • g) ∂stdGaussian E := by
        apply lintegral_congr
        intro x
        exact (lintegral_const_mul _ (by fun_prop : Measurable
          (fun g : E => φ (x + Real.sqrt t • g)))).symm
      _ = _ := lintegral_lintegral_swap (by fun_prop)
  rw [hl, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hφ]
  have hr : (∫⁻ y, (∫⁻ g, p (y - Real.sqrt t • g) ∂stdGaussian E) * φ y) =
      ∫⁻ g, (∫⁻ y, p (y - Real.sqrt t • g) * φ y) ∂stdGaussian E := by
    calc
      _ = ∫⁻ y, ∫⁻ g, p (y - Real.sqrt t • g) * φ y ∂stdGaussian E := by
        apply lintegral_congr
        intro y
        exact (lintegral_mul_const _ (by fun_prop : Measurable
          (fun g : E => p (y - Real.sqrt t • g)))).symm
      _ = _ := lintegral_lintegral_swap hm.aemeasurable
  simp only [Pi.mul_apply]
  rw [hr]
  apply lintegral_congr
  intro g
  simpa only [add_sub_cancel_right] using
    (lintegral_add_right_eq_self (fun y => p (y - Real.sqrt t • g) * φ y)
      (Real.sqrt t • g))

theorem heatAverage_eq_sub (p : E → ℝ) (t : ℝ) (y : E) :
    heatAverage p t y = ∫ g, p (y - Real.sqrt t • g) ∂stdGaussian E := by
  have hm : MeasurePreserving (fun g : E => -g) (stdGaussian E) (stdGaussian E) :=
    ⟨continuous_neg.measurable, stdGaussian_map (LinearIsometryEquiv.neg ℝ)⟩
  simpa [heatAverage, sub_eq_add_neg] using
    (hm.integral_comp (Homeomorph.neg E).measurableEmbedding (fun g => p (y + Real.sqrt t • g))).symm

/-- The convolution reference is the actual Gaussian average of its original density. -/
theorem heatedLaw_withDensity (p : E → ℝ) (hp : Continuous p) (hpos : ∀ x, 0 ≤ p x)
    {C : ℝ} (hC : ∀ x, ‖p x‖ ≤ C) (t : ℝ) :
    heatedLaw (volume.withDensity (fun x => ENNReal.ofReal (p x))) t =
      volume.withDensity (fun y => ENNReal.ofReal (heatAverage p t y)) := by
  rw [heatedLaw_withDensity_lintegral _ hp.measurable.ennreal_ofReal]
  congr 1
  funext y
  rw [heatAverage_eq_sub]
  symm
  apply ofReal_integral_eq_lintegral_ofReal
  · exact (integrable_const C).mono' (by fun_prop : Continuous (fun g : E =>
      p (y - Real.sqrt t • g))).aestronglyMeasurable (Filter.Eventually.of_forall fun g => hC _)
  · exact Filter.Eventually.of_forall fun g => hpos _

/-- Equality of the actual heat laws identifies the continuous densities everywhere. -/
theorem reference_density_eq_heatAverage {a b : ℝ}
    (F : Analysis.Poisson.ReferencePoissonFamily E a b) (t : ℝ) (ht : t ∈ Icc a b)
    (hheat : F.law t = heatedLaw (F.law a) (t-a)) :
    F.density t = heatAverage (F.density a) (t-a) := by
  have ha : a ∈ Icc a b := ⟨le_rfl,F.ordered⟩
  have hp := (reference_density_C2 F a ha).continuous
  obtain ⟨C,hC⟩ := reference_density_bounded F a ha
  have he : volume.withDensity (fun x => ENNReal.ofReal (F.density t x)) =
      volume.withDensity (fun x => ENNReal.ofReal (heatAverage (F.density a) (t-a) x)) := by
    rw [← F.density_law t ht, hheat, F.density_law a ha]
    exact heatedLaw_withDensity (F.density a) hp (F.density_nonneg a ha) hC (t-a)
  have havg : Continuous (heatAverage (F.density a) (t-a)) :=
    (heatAverage_continuous_of_bounded hp hC).comp (continuous_const.prodMk continuous_id)
  have hpt := (reference_density_C2 F t ht).continuous
  have hae := (withDensity_eq_iff_of_sigmaFinite hpt.measurable.ennreal_ofReal.aemeasurable
    havg.measurable.ennreal_ofReal.aemeasurable).mp he
  apply Measure.eq_of_ae_eq (μ := volume) _ hpt havg
  filter_upwards [hae] with x hx
  exact (ENNReal.ofReal_eq_ofReal_iff (F.density_nonneg t ht x)
    (integral_nonneg fun g => F.density_nonneg a ha _)).mp hx

end AcceleratedLogConcave.Kinetic.Reheating
