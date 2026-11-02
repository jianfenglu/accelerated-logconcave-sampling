import AcceleratedLogConcave.Analysis.Poisson.ReferencePoisson
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Measure.OpenPos

/-! The classical Gibbs score identity is derived from the actual law and its
continuous density, rather than assumed as an extra transport premise. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Function
open scoped Topology
namespace AcceleratedLogConcave.Kinetic
open Analysis.Poisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Uniqueness of continuous nonnegative densities identifies the Gibbs density pointwise. -/
theorem density_eq_normalized_gibbs (V r : E → ℝ) (hV : ContDiff ℝ 1 V)
    (hr : Continuous r) (hpos : ∀ x, 0 ≤ r x)
    (he : volume.withDensity (fun x => ENNReal.ofReal (r x)) = volume.tilted (fun x => -V x)) :
    r = fun x => Real.exp (-V x) / ∫ y, Real.exp (-V y) := by
  have hg : Continuous (fun x => Real.exp (-V x) / ∫ y, Real.exp (-V y)) :=
    (Real.continuous_exp.comp hV.continuous.neg).div_const _
  have hae := (withDensity_eq_iff_of_sigmaFinite
    hr.measurable.ennreal_ofReal.aemeasurable hg.measurable.ennreal_ofReal.aemeasurable).mp he
  apply Measure.eq_of_ae_eq (μ := volume) _ hr hg
  filter_upwards [hae] with x hx
  exact (ENNReal.ofReal_eq_ofReal_iff (hpos x)
    (div_nonneg (Real.exp_pos _).le (integral_nonneg (fun _ => (Real.exp_pos _).le)))).mp hx

theorem gibbs_density_hasFDerivAt (V r : E → ℝ) (hV : ContDiff ℝ 1 V)
    (hr : Continuous r) (hpos : ∀ x, 0 ≤ r x)
    (he : volume.withDensity (fun x => ENNReal.ofReal (r x)) = volume.tilted (fun x => -V x)) (x : E) :
    HasFDerivAt r ((-r x) • fderiv ℝ V x) x := by
  have heq := density_eq_normalized_gibbs V r hV hr hpos he
  have hd := ((hV.differentiable_one x).hasFDerivAt.neg.exp).mul_const
    (∫ y, Real.exp (-V y))⁻¹
  rw [heq]
  convert hd using 1 <;> ext v <;> simp [div_eq_mul_inv]
  all_goals ring

theorem reference_density_hasFDerivAt {a b : ℝ} (F : ReferencePoissonFamily E a b)
    (t : ℝ) (ht : t ∈ Icc a b) (x : E) :
    HasFDerivAt (F.density t) ((-F.density t x) • fderiv ℝ (F.potential t) x) x := by
  have hc : Continuous (F.density t) := F.density_continuous.comp_continuous
    (continuous_const.prodMk continuous_id) (fun x => ⟨ht, mem_univ x⟩)
  exact gibbs_density_hasFDerivAt (F.potential t) (F.density t)
    ((F.potential_C2 t).of_le (by norm_num)) hc (F.density_nonneg t ht)
    ((F.density_law t ht).symm.trans (F.gibbs_law t ht)) x

end AcceleratedLogConcave.Kinetic
