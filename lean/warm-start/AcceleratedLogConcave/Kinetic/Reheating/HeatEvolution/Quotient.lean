import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.Spatial
import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.ProductRule

/-! The classical signed heat quotient on the compact C2 input core. Every
numerator derivative is derived from its actual Gaussian average. The reference
denominator equation is derived from the genuine Gibbs continuity equation.
The subsequent measure-level identification is kept separate from this local
calculus calculation. -/
noncomputable section
open MeasureTheory InnerProductSpace Set
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson AcceleratedLogConcave.HeatCalculus
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
variable {a b : ℝ}

/-- The actual smoothed numerator of a compact signed input. -/
def compactHeatNumerator (F : ReferencePoissonFamily E a b) (f : E → ℝ)
    (t : ℝ) (x : E) : ℝ := heatAverage (fun y => f y * F.density a y) (t-a) x

/-- The classical quotient of the signed numerator by the moving reference density. -/
def compactHeatQuotient (F : ReferencePoissonFamily E a b) (f : E → ℝ)
    (t : ℝ) (x : E) : ℝ := compactHeatNumerator F f t x / F.density t x

theorem compactHeatNumerator_C2 (F : ReferencePoissonFamily E a b) {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) (t : ℝ) :
    ContDiff ℝ 2 (compactHeatNumerator F f t) :=
  heatAverage_contDiff_two (hf.mul (reference_density_C2 F a ⟨le_rfl,F.ordered⟩))
    hc.mul_right (t-a)

theorem compactHeatQuotient_C2 (F : ReferencePoissonFamily E a b) {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) (t : ℝ) (ht : t ∈ Icc a b) :
    ContDiff ℝ 2 (compactHeatQuotient F f t) :=
  (compactHeatNumerator_C2 F hf hc t).div (reference_density_C2 F t ht)
    (fun x => (reference_density_pos F t ht x).ne')

theorem compactHeatNumerator_eq_density_mul (F : ReferencePoissonFamily E a b)
    (f : E → ℝ) (t : ℝ) (ht : t ∈ Icc a b) :
    compactHeatNumerator F f t = fun x => F.density t x * compactHeatQuotient F f t x := by
  funext x
  dsimp [compactHeatQuotient]
  field_simp [(reference_density_pos F t ht x).ne']

theorem compactHeatNumerator_classical_heat (F : ReferencePoissonFamily E a b)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (t : ℝ) (ht : a < t) (x : E) :
    HasDerivAt (fun s => compactHeatNumerator F f s x)
      ((1/2:ℝ) * compactTestLaplacian (compactHeatNumerator F f t) x) t := by
  have hd := (heatAverage_classical_heat
    (hf.mul (reference_density_C2 F a ⟨le_rfl,F.ordered⟩)) hc.mul_right
    (sub_pos.mpr ht) x).comp t ((hasDerivAt_id t).sub_const a)
  rw [show compactHeatNumerator F f t = heatAverage (fun y => f y * F.density a y) (t-a) from rfl]
  simpa only [mul_one, Function.comp_def, id_eq, compactHeatNumerator] using hd

/-- On the core, the true quotient satisfies the source relative-density PDE. -/
theorem compactHeatQuotient_classical_heat (F : ReferencePoissonFamily E a b)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (t : ℝ) (ht : t ∈ Ioo a b) (hscale : F.scale t = -(1/2:ℝ)) (x : E) :
    HasDerivAt (fun s => compactHeatQuotient F f s x)
      ((1/2:ℝ) * compactTestLaplacian (compactHeatQuotient F f t) x -
        inner ℝ (gradient (F.potential t) x) (gradient (compactHeatQuotient F f t) x)) t := by
  have ht' := Ioo_subset_Icc_self ht
  have hp := reference_density_C2 F t ht'
  have hq := compactHeatQuotient_C2 F hf hc t ht'
  have hpos := (reference_density_pos F t ht' x).ne'
  have hd := (compactHeatNumerator_classical_heat F hf hc t ht.1 x).div
    (reference_density_classical_heat F t ht hscale x) hpos
  change HasDerivAt (fun s => compactHeatQuotient F f s x) _ t at hd
  convert hd using 1
  have hLap := compactTestLaplacian_mul hp hq x
  rw [← compactHeatNumerator_eq_density_mul F f t ht',
    reference_density_gradient F t ht', inner_smul_left, RCLike.conj_to_real] at hLap
  have hn := congrFun (compactHeatNumerator_eq_density_mul F f t ht') x
  rw [hLap, hn]
  field_simp
  ring

@[simp] theorem compactHeatQuotient_initial (F : ReferencePoissonFamily E a b)
    (f : E → ℝ) (x : E) : compactHeatQuotient F f a x = f x := by
  simp [compactHeatQuotient, compactHeatNumerator, heatAverage,
    (reference_density_pos F a ⟨le_rfl,F.ordered⟩ x).ne']

end AcceleratedLogConcave.Kinetic.Reheating
