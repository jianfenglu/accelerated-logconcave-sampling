import DirectW12.PhysicalAssembly
import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.OriginalHeatVarianceSupplier

/-!

-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Root.RecursiveInnovation
open Numerics.AffineGraph Kinetic Kinetic.Reheating

/-- Positive-variance envelope [3A/4,2A]; physical clock variance remains A(1-r²). -/
def originalPhysicalReference
    {ι : Type*} [fi : Fintype ι] {V : (EuclideanSpace ℝ ι) → ℝ} {κ h : ℝ}
    (hV : ContDiff ℝ 2 V) (hκ : 0 < κ) (hh : 0 < h)
    (hlo : ∀ z v, κ⁻¹*‖v‖^2 ≤ fderiv ℝ (fderiv ℝ V) z v v)
    (hup : ∀ z v, fderiv ℝ (fderiv ℝ V) z v v ≤ ‖v‖^2) :
    Analysis.Poisson.ReferencePoissonFamily (EuclideanSpace ℝ ι) 0 (1/2) :=
  let hA : 0 < 2*h^2 := by positivity
  let hAB : 2*h^2 < 2*(2*h^2) := by nlinarith
  clockTransportFamily
    (originalVarianceHeatFamily (A := 2*h^2) (R := 2*(2*h^2)) hV hκ hA hAB hlo hup) hA hAB

theorem originalPhysicalReference_potential
    {ι : Type*} [fi : Fintype ι] {V : (EuclideanSpace ℝ ι) → ℝ} {κ h : ℝ}
    (hV : ContDiff ℝ 2 V) (hκ : 0 < κ) (hh : 0 < h)
    (hlo : ∀ z v, κ⁻¹*‖v‖^2 ≤ fderiv ℝ (fderiv ℝ V) z v v)
    (hup : ∀ z v, fderiv ℝ (fderiv ℝ V) z v v ≤ ‖v‖^2)
    (r : ℝ) (hr : r ∈ Icc (0:ℝ) (1/2)) :
    (originalPhysicalReference hV hκ hh hlo hup).potential r =
      Gibbs.heatPotential V (2*h^2*(1-r^2)) := by
  unfold originalPhysicalReference
  rw [clockTransportFamily_potential _ _ _ r hr]
  rfl

theorem originalPhysicalReference_scale
    {ι : Type*} [fi : Fintype ι] {V : (EuclideanSpace ℝ ι) → ℝ} {κ h : ℝ}
    (hV : ContDiff ℝ 2 V) (hκ : 0 < κ) (hh : 0 < h)
    (hlo : ∀ z v, κ⁻¹*‖v‖^2 ≤ fderiv ℝ (fderiv ℝ V) z v v)
    (hup : ∀ z v, fderiv ℝ (fderiv ℝ V) z v v ≤ ‖v‖^2)
    (r : ℝ) (hr : r ∈ Icc (0:ℝ) (1/2)) :
    (originalPhysicalReference hV hκ hh hlo hup).scale r = (2*h^2)*r := by
  unfold originalPhysicalReference
  exact clockTransportFamily_scale _ _ _ r hr

/-- Candidate original-C² conclusion. Its statement adds no supplier hypothesis;
validation still requires the original heat adapter AND the whole direct-W12 chain. -/
theorem original_C2_physicalDormantW12
    {ι : Type*} [fi : Fintype ι] [di : DecidableEq ι] {V : (EuclideanSpace ℝ ι) → ℝ} {κ h : ℝ} {m : ℕ}
    (hV : ContDiff ℝ 2 V) (hκ : 0 < κ) (hh : 0 < h) (hhalf : h ≤ 1/2)
    (hlo : ∀ z v, κ⁻¹*‖v‖^2 ≤ fderiv ℝ (fderiv ℝ V) z v v)
    (hup : ∀ z v, fderiv ℝ (fderiv ℝ V) z v v ≤ ‖v‖^2)
    (G : MeanGeometry m) (hm : 0 < m) (t : ℝ) (ht : 0 < t) (K : ℕ)
    (R : ClockLaw.Clock) :
    let P := originalPhysicalReference hV hκ hh hlo hup
    let hlo0 := fun z v => (mul_nonneg (inv_pos.mpr hκ).le (sq_nonneg ‖v‖)).trans (hlo z v)
    physicalDormantW12 P R
      (physicalSourceSection (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf)
      (V := V) (hV := hV) (hlo := hlo0) (hup := hup)
      (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := R))
      (physicalSourceSection_invariant (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf)
      (V := V) (hV := hV) (hlo := hlo0) (hup := hup)
      (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := R))
      1 (2*h^2) := by
  dsimp only
  exact physicalSourceSection_W12
    (ι := ι) (fi := fi) (di := di) (m := m) (h := h) (hh := hh) (hhalf := hhalf)
    (V := V) (hV := hV)
    (hlo := fun z v => (mul_nonneg (inv_pos.mpr hκ).le (sq_nonneg ‖v‖)).trans (hlo z v))
    (hup := hup) (G := G) (hm := hm) (t := t) (ht := ht) (K := K)
    (P := originalPhysicalReference hV hκ hh hlo hup)
    (hpotential := originalPhysicalReference_potential hV hκ hh hlo hup)
    (hscale := originalPhysicalReference_scale hV hκ hh hlo hup) (R := R)
end AcceleratedLogConcave.Root.RecursiveInnovation
