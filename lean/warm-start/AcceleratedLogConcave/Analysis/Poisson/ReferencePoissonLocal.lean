import AcceleratedLogConcave.Analysis.Poisson.ReferencePoisson
import AcceleratedLogConcave.Analysis.Poisson.ReferenceTimeExtension

/-! Source-local data for the actual moving Poisson theorem. The extension
supplies the generic ODE helper's global continuity requirements; it makes no
claim that the density continuity equation extends beyond the source interval. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Function
open scoped Topology NNReal
namespace AcceleratedLogConcave.Analysis.Poisson
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Only source data on a closed envelope are required. Moving estimates apply
on compact subintervals of its interior. -/
structure LocalReferencePoissonFamily (a b : ℝ) where
  ordered : a ≤ b
  potential : ℝ → E → ℝ
  scale : ℝ → ℝ
  potential_C2 : ∀ t ∈ Icc a b, ContDiff ℝ 2 (potential t)
  gradient_continuous : ContinuousOn (uncurry (fun t => gradient (potential t)))
    (Icc a b ×ˢ (univ : Set E))
  hessian_continuous : ContinuousOn (uncurry (fun t => hessianOperator (potential t)))
    (Icc a b ×ˢ (univ : Set E))
  scale_continuous : ContinuousOn scale (Icc a b)
  lower : ℝ → ℝ
  lower_pos : ∀ t ∈ Icc a b, 0 < lower t
  hessian_lower : ∀ t ∈ Icc a b, ∀ x v,
    lower t * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (potential t)) x v v
  hessian_upper : ∀ t ∈ Icc a b, ∀ x v,
    fderiv ℝ (fderiv ℝ (potential t)) x v v ≤ ‖v‖ ^ 2
  law : ℝ → Measure E
  probability : ∀ t ∈ Icc a b, IsProbabilityMeasure (law t)
  integrable : ∀ t ∈ Icc a b, Integrable (fun x => Real.exp (-potential t x))
  gibbs_law : ∀ t ∈ Icc a b, law t = volume.tilted (fun x => -potential t x)
  density : ℝ → E → ℝ
  densityVelocity : ℝ → E → ℝ
  density_continuous : ContinuousOn (uncurry density) (Icc a b ×ˢ (univ : Set E))
  densityVelocity_continuous : ContinuousOn (uncurry densityVelocity) (Ioo a b ×ˢ (univ : Set E))
  density_hasDerivAt : ∀ t ∈ Ioo a b, ∀ x,
    HasDerivAt (fun s => density s x) (densityVelocity t x) t
  density_C1 : ∀ t ∈ Ioo a b, ContDiff ℝ 1 (density t)
  continuity_equation : ∀ t ∈ Ioo a b, ∀ x,
    densityVelocity t x + fluxDivergence (fun y => density t y • referenceDrift potential scale t y) x = 0
  density_law : ∀ t ∈ Icc a b, law t = volume.withDensity (fun x => ENNReal.ofReal (density t x))
  density_nonneg : ∀ t ∈ Icc a b, ∀ x, 0 ≤ density t x

namespace LocalReferencePoissonFamily
variable {E} {a b : ℝ} (F : LocalReferencePoissonFamily E a b)

/-- The drift-scale bound follows from compactness and continuity. -/
theorem exists_scaleBound : ∃ C : ℝ≥0, ∀ t ∈ Icc a b, |F.scale t| ≤ C := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn F.scale_continuous
  refine ⟨⟨max M 0, le_max_right _ _⟩, ?_⟩
  intro t ht
  have hm : |F.scale t| ≤ M := by simpa only [Real.norm_eq_abs] using hM t ht
  exact hm.trans (le_max_left _ _)

def scaleBound : ℝ≥0 := Classical.choose F.exists_scaleBound

theorem scale_bounded : ∀ t ∈ Icc a b, |F.scale t| ≤ F.scaleBound :=
  Classical.choose_spec F.exists_scaleBound

/-- Every analytic conclusion of ReferencePoissonFamily is available from
source-local hypotheses, by an explicit clamped extension. -/
def toFamily : ReferencePoissonFamily E a b where
  ordered := F.ordered
  potential := timeExtend F.ordered F.potential
  scale := timeExtend F.ordered F.scale
  potential_C2 := timeExtend_contDiff F.ordered F.potential F.potential_C2
  gradient_continuous := timeExtend_gradient_continuous F.ordered F.potential F.gradient_continuous
  hessian_continuous := timeExtend_hessian_continuous F.ordered F.potential F.hessian_continuous
  scale_continuous := continuous_timeExtend F.ordered F.scale F.scale_continuous
  scaleBound := F.scaleBound
  scale_bounded := fun t ht => by simpa only [timeExtend_eq_of_mem _ _ ht] using F.scale_bounded t ht
  lower := F.lower
  lower_pos := F.lower_pos
  hessian_lower := fun t ht => by simpa only [timeExtend_eq_of_mem _ _ ht] using F.hessian_lower t ht
  hessian_upper := fun t ht => by simpa only [timeExtend_eq_of_mem _ _ ht] using F.hessian_upper t ht
  law := timeExtend F.ordered F.law
  probability := fun t => F.probability (projIcc a b F.ordered t) (projIcc a b F.ordered t).property
  integrable := fun t ht => by simpa only [timeExtend_eq_of_mem _ _ ht] using F.integrable t ht
  gibbs_law := fun t ht => by simpa only [timeExtend_eq_of_mem _ _ ht] using F.gibbs_law t ht
  density := F.density
  densityVelocity := F.densityVelocity
  density_continuous := F.density_continuous
  densityVelocity_continuous := F.densityVelocity_continuous
  density_hasDerivAt := F.density_hasDerivAt
  density_C1 := F.density_C1
  continuity_equation := fun t ht x => by
    simpa only [referenceDrift, timeExtend_eq_of_mem _ _ ⟨ht.1.le, ht.2.le⟩] using
      F.continuity_equation t ht x
  density_law := fun t ht => by simpa only [timeExtend_eq_of_mem _ _ ht] using F.density_law t ht
  density_nonneg := F.density_nonneg

@[simp] theorem toFamily_potential (t : ℝ) (ht : t ∈ Icc a b) :
    F.toFamily.potential t = F.potential t := timeExtend_eq_of_mem _ _ ht

@[simp] theorem toFamily_scale (t : ℝ) (ht : t ∈ Icc a b) :
    F.toFamily.scale t = F.scale t := timeExtend_eq_of_mem _ _ ht

@[simp] theorem toFamily_law (t : ℝ) (ht : t ∈ Icc a b) :
    F.toFamily.law t = F.law t := timeExtend_eq_of_mem _ _ ht

end LocalReferencePoissonFamily
end AcceleratedLogConcave.Analysis.Poisson
