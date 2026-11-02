import AcceleratedLogConcave.Analysis.Poisson.ReferencePoissonLocal
import AcceleratedLogConcave.Kinetic.Mixing.HeatMarginal

/-! A variance-indexed classical heat family gives the genuine forward reheating
family at every reverse clock. The envelope extends beyond the return variance.
The record contains only classical source data and the actual Gaussian law. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set InnerProductSpace Function
open scoped Topology NNReal
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Classical potential/density data for the actual Gaussian heat marginals.
No flow, inverse, current estimate or dissipation identity is record data. -/
structure VarianceHeatFamily (μ : Measure E) (vmin vmax : ℝ) where
  source : LocalReferencePoissonFamily E vmin vmax
  scale_eq : ∀ v ∈ Icc vmin vmax, source.scale v = -(1/2:ℝ)
  heat_law : ∀ v ∈ Icc vmin vmax, source.law v = heatedLaw μ v

namespace VarianceHeatFamily

/-- Affine variance translation preserves the classical continuity equation. -/
def shiftedLocal {μ : Measure E} {l r : ℝ} (H : VarianceHeatFamily μ l r)
    (s : ℝ) (hs : s ∈ Icc l r) : LocalReferencePoissonFamily E 0 (r-s) where
  ordered := sub_nonneg.mpr hs.2
  potential := fun u => H.source.potential (s+u)
  scale := fun _ => -(1/2:ℝ)
  potential_C2 := fun u hu => H.source.potential_C2 (s+u) ⟨by linarith [hs.1,hu.1],by linarith [hu.2]⟩
  gradient_continuous := H.source.gradient_continuous.comp
    (f := fun z : ℝ × E => (s + z.1, z.2))
    (((continuous_const (y := s)).add continuous_fst).prodMk continuous_snd).continuousOn
    (fun z hz => ⟨⟨by dsimp only [Pi.add_apply]; linarith [hs.1,hz.1.1],by dsimp only [Pi.add_apply]; linarith [hz.1.2]⟩,mem_univ _⟩)
  hessian_continuous := H.source.hessian_continuous.comp
    (f := fun z : ℝ × E => (s + z.1, z.2))
    (((continuous_const (y := s)).add continuous_fst).prodMk continuous_snd).continuousOn
    (fun z hz => ⟨⟨by dsimp only [Pi.add_apply]; linarith [hs.1,hz.1.1],by dsimp only [Pi.add_apply]; linarith [hz.1.2]⟩,mem_univ _⟩)
  scale_continuous := continuous_const.continuousOn
  lower := fun u => H.source.lower (s+u)
  lower_pos := fun u hu => H.source.lower_pos (s+u) ⟨by linarith [hs.1,hu.1],by linarith [hu.2]⟩
  hessian_lower := fun u hu => H.source.hessian_lower (s+u) ⟨by linarith [hs.1,hu.1],by linarith [hu.2]⟩
  hessian_upper := fun u hu => H.source.hessian_upper (s+u) ⟨by linarith [hs.1,hu.1],by linarith [hu.2]⟩
  law := fun u => H.source.law (s+u)
  probability := fun u hu => H.source.probability (s+u) ⟨by linarith [hs.1,hu.1],by linarith [hu.2]⟩
  integrable := fun u hu => H.source.integrable (s+u) ⟨by linarith [hs.1,hu.1],by linarith [hu.2]⟩
  gibbs_law := fun u hu => H.source.gibbs_law (s+u) ⟨by linarith [hs.1,hu.1],by linarith [hu.2]⟩
  density := fun u => H.source.density (s+u)
  densityVelocity := fun u => H.source.densityVelocity (s+u)
  density_continuous := H.source.density_continuous.comp
    (f := fun z : ℝ × E => (s + z.1, z.2))
    (((continuous_const (y := s)).add continuous_fst).prodMk continuous_snd).continuousOn
    (fun z hz => ⟨⟨by dsimp only [Pi.add_apply]; linarith [hs.1,hz.1.1],by dsimp only [Pi.add_apply]; linarith [hz.1.2]⟩,mem_univ _⟩)
  densityVelocity_continuous := H.source.densityVelocity_continuous.comp
    (f := fun z : ℝ × E => (s + z.1, z.2))
    (((continuous_const (y := s)).add continuous_fst).prodMk continuous_snd).continuousOn
    (fun z hz => ⟨⟨by dsimp only [Pi.add_apply]; linarith [hs.1,hz.1.1],by dsimp only [Pi.add_apply]; linarith [hz.1.2]⟩,mem_univ _⟩)
  density_hasDerivAt := fun u hu x => by
    have hd := (H.source.density_hasDerivAt (s+u)
      ⟨by linarith [hs.1,hu.1],by linarith [hu.2]⟩ x).comp u ((hasDerivAt_id u).const_add s)
    simpa only [mul_one, Function.comp_def] using hd
  density_C1 := fun u hu => H.source.density_C1 (s+u) ⟨by linarith [hs.1,hu.1],by linarith [hu.2]⟩
  continuity_equation := fun u hu x => by
    have hv : s+u ∈ Ioo l r := ⟨by linarith [hs.1,hu.1],by linarith [hu.2]⟩
    simpa only [referenceDrift, H.scale_eq (s+u) (Ioo_subset_Icc_self hv)] using
      H.source.continuity_equation (s+u) hv x
  density_law := fun u hu => H.source.density_law (s+u) ⟨by linarith [hs.1,hu.1],by linarith [hu.2]⟩
  density_nonneg := fun u hu => H.source.density_nonneg (s+u) ⟨by linarith [hs.1,hu.1],by linarith [hu.2]⟩

/-- The constructed source-local family is extended only for the ODE helper. -/
def shiftedFamily {μ : Measure E} {l r : ℝ} (H : VarianceHeatFamily μ l r)
    (s : ℝ) (hs : s ∈ Icc l r) : ReferencePoissonFamily E 0 (r-s) :=
  (H.shiftedLocal s hs).toFamily

theorem shiftedFamily_potential {μ : Measure E} {l r : ℝ} (H : VarianceHeatFamily μ l r)
    (s : ℝ) (hs : s ∈ Icc l r) (u : ℝ) (hu : u ∈ Icc 0 (r-s)) :
    (H.shiftedFamily s hs).potential u = H.source.potential (s+u) :=
  (H.shiftedLocal s hs).toFamily_potential u hu

theorem shiftedFamily_law {μ : Measure E} {l r : ℝ} (H : VarianceHeatFamily μ l r)
    (s : ℝ) (hs : s ∈ Icc l r) (u : ℝ) (hu : u ∈ Icc 0 (r-s)) :
    (H.shiftedFamily s hs).law u = H.source.law (s+u) :=
  (H.shiftedLocal s hs).toFamily_law u hu

theorem shiftedFamily_scale {μ : Measure E} {l r : ℝ} (H : VarianceHeatFamily μ l r)
    (s : ℝ) (hs : s ∈ Icc l r) (u : ℝ) (hu : u ∈ Icc 0 (r-s)) :
    (H.shiftedFamily s hs).scale u = -(1/2:ℝ) :=
  (H.shiftedLocal s hs).toFamily_scale u hu

/-- Gaussian semigroup composition supplies the actual forward heat marginals. -/
theorem shiftedFamily_heat {μ : Measure E} [IsProbabilityMeasure μ]
    {l r : ℝ} (H : VarianceHeatFamily μ l r)
    (s : ℝ) (hs : s ∈ Icc l r) (hs0 : 0 ≤ s)
    (u : ℝ) (hu : u ∈ Icc 0 (r-s)) :
    (H.shiftedFamily s hs).law u =
      heatedLaw ((H.shiftedFamily s hs).law 0) (u-0) := by
  classical
  have hs' : 0 ∈ Icc 0 (r-s) := ⟨le_rfl,sub_nonneg.mpr hs.2⟩
  rw [H.shiftedFamily_law s hs u hu, H.shiftedFamily_law s hs 0 hs', add_zero, sub_zero,
    H.heat_law s hs, H.heat_law (s+u) ⟨by linarith [hs.1,hu.1],by linarith [hu.2]⟩]
  exact (heatedLaw_add μ ⟨s,hs0⟩ ⟨u,hu.1⟩).symm

/-- Every prescribed reverse clock has a forward reheating segment inside
one common variance envelope extending strictly beyond the return variance. -/
theorem clock_segment {A R ρ : ℝ} (hA : 0 < A) (hR : A < R)
    (hρ : ρ ∈ Icc (0:ℝ) (1/2)) :
    A*(1-ρ^2) ∈ Icc (3*A/4) R ∧ 0 ≤ A*(1-ρ^2) ∧
      A*ρ^2 ∈ Ico 0 (R-A*(1-ρ^2)) ∧ A*(1-ρ^2)+A*ρ^2=A := by
  have hsq : ρ^2 ≤ 1/4 := by nlinarith [hρ.1,hρ.2]
  have hz := sq_nonneg ρ
  have hp := mul_nonneg hA.le hz
  have hquarter := mul_le_mul_of_nonneg_left hsq hA.le
  constructor
  · constructor <;> nlinarith
  constructor
  · nlinarith
  constructor
  · constructor <;> nlinarith
  · ring

end VarianceHeatFamily
end AcceleratedLogConcave.Kinetic.Reheating
