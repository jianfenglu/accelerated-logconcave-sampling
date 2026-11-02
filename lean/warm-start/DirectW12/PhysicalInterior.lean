import DirectW12.WeakIncrement
import AcceleratedLogConcave.Analysis.Poisson.ReferencePoisson

/-!
# Actual Poisson material derivative and interior pure-flow increment

These are source joins, not assumptions about a generic Poisson inverse.
The physical pullback is defined from the genuine closed weighted inverse
at every closed-clock time. Its identification with the auxiliary source
`gradientInverse` is used only strictly inside the source interval.

This file does NOT prove the coupled-path weak chain rule or continuity of the
physical pullback at the right endpoint. Its increment theorem is intentionally
restricted to two strictly interior times and to the pure reverse-heat flow.
-/

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace

namespace AcceleratedLogConcave.Analysis.Poisson.ReferencePoissonFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {α β : ℝ} (P : ReferencePoissonFamily E α β)

/-- The physical gradient pullback, with no identity extension at endpoints. -/
def physicalGradientPullback (r : Icc α β) (g : Lp ℝ 2 (P.law α)) :
    Lp E 2 (P.law α) :=
  P.unitary r
    (gradientPoissonInverse (P.law r) (P.potential r) (P.potential_C2 r)
      (P.integrable r r.property) (P.gibbs_law r r.property)
      (P.lower r) 1 (P.lower_pos r r.property)
      (P.hessian_lower r r.property)
      (by simpa only [one_mul] using P.hessian_upper r r.property)
      ((P.unitary r).symm g))

theorem physicalGradientPullback_eq_gradientInverse
    {r : ℝ} (hr : r ∈ Ioo α β) (g : Lp ℝ 2 (P.law α)) :
    P.physicalGradientPullback ⟨r, hr.1.le, hr.2.le⟩ g = P.gradientInverse r g :=
  (P.gradientInverse_eq_physical r hr g).symm

/-- Actual interior material differentiation tested against a fixed L2 vector. -/
theorem material_pairing_hasDerivAt
    (g : Lp ℝ 2 (P.law α)) (ψ : Lp E 2 (P.law α))
    {r : ℝ} (hr : r ∈ Ioo α β) :
    HasDerivAt (fun s => inner ℝ (P.gradientInverse s g) ψ)
      (inner ℝ (P.materialOperator r hr g) ψ) r := by
  simpa only [inner_zero_right, zero_add] using
    (P.gradientInverse_hasDerivAt r hr g).inner ℝ (hasDerivAt_const r ψ)

/-- The actual material pairing has the gap-free source bound. -/
theorem material_pairing_bound
    (g : Lp ℝ 2 (P.law α)) (ψ : Lp E 2 (P.law α))
    {r : ℝ} (hr : r ∈ Ioo α β) :
    |inner ℝ (P.materialOperator r hr g) ψ| ≤ |P.scale r| * ‖g‖ * ‖ψ‖ := by
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right
      ((P.materialOperator r hr).le_of_opNorm_le (P.materialOperator_norm_le r hr) g)
      (norm_nonneg ψ))

/-- A concrete interior physical join: the pure-flow pullback gains the sharp
quadratic clock primitive, with no inverse lower-curvature factor. This is not
the coupled-flow estimate and makes no closed-endpoint continuity claim. -/
theorem physicalGradientPullback_interior_increment_le
    {a u R : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u) (huR : u ≤ R)
    (huI : u ∈ Ioo α β) (hRI : R ∈ Ioo α β)
    (hscale : ∀ r ∈ Ioo u R, P.scale r = a * r)
    (g : Lp ℝ 2 (P.law α)) :
    ‖P.physicalGradientPullback ⟨R, hRI.1.le, hRI.2.le⟩ g -
      P.physicalGradientPullback ⟨u, huI.1.le, huI.2.le⟩ g‖ ≤
      (a * (R ^ 2 - u ^ 2) / 2) * ‖g‖ := by
  rw [P.physicalGradientPullback_eq_gradientInverse hRI,
    P.physicalGradientPullback_eq_gradientInverse huI]
  let d : ℝ → Lp E 2 (P.law α) → ℝ := fun r ψ =>
    if hr : r ∈ Ioo α β then inner ℝ (P.materialOperator r hr g) ψ else 0
  have hmem (r : ℝ) (hr : r ∈ Icc u R) : r ∈ Ioo α β :=
    ⟨huI.1.trans_le hr.1, hr.2.trans_lt hRI.2⟩
  have hb := dense_pairing_increment_le_affine
    (fun r => P.gradientInverse r g) univ dense_univ d
    (ell := 0) (a := a) (G := ‖g‖) le_rfl ha (norm_nonneg g) hu huR
    (fun ψ _ r hr =>
      (((P.gradientInverse_continuousAt r (hmem r hr)).clm_apply
        continuousAt_const).inner continuousAt_const).continuousWithinAt)
    (fun ψ _ r hr => by
      simpa only [d, dite_eq_left (hmem r ⟨hr.1.le, hr.2.le⟩)] using
        P.material_pairing_hasDerivAt g ψ (hmem r ⟨hr.1.le, hr.2.le⟩))
    (fun ψ _ r hr => by
      have hb := P.material_pairing_bound g ψ (hmem r ⟨hr.1.le, hr.2.le⟩)
      rw [hscale r hr, abs_of_nonneg (mul_nonneg ha (hu.trans hr.1.le))] at hb
      simpa only [d, dite_eq_left (hmem r ⟨hr.1.le, hr.2.le⟩), zero_add] using hb)
  simpa only [zero_mul, zero_add] using hb

end AcceleratedLogConcave.Analysis.Poisson.ReferencePoissonFamily
