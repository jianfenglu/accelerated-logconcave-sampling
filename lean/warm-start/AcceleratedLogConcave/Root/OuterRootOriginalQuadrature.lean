import AcceleratedLogConcave.Root.OuterRootFlowIdentification
import AcceleratedLogConcave.Root.OuterRootStrongJetLp

/-! Original-data specialization of the root's common-seed quadrature estimate.
The source flow uses its literal Gaussian start. All polynomial moments and jet
budgets are proved suppliers; the remaining caller task is the prescribed row
and physical output-unit identification. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
namespace AcceleratedLogConcave.Root.OuterRootOriginalQuadrature
open OuterRootFlowIdentification OuterRootStrongJetLp
variable {ι : Type*} [Fintype ι]
variable {V : EuclideanSpace ℝ ι → ℝ} (hV : ContDiff ℝ 2 V)
  {m h : ℝ} (hm : 0 < m) (hh : 0 < h)
  (hlo : ∀ z v, m * ‖v‖^2 ≤ fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ V) z v v ≤ ‖v‖^2)

/-- Every common-seed polynomial moment follows from original curvature. -/
theorem source_input_moment (n : ℕ) :
    Integrable (fun p => ‖input (Real.sqrt h)⁻¹ p‖^n)
      (seedMeasure (family hV hm hh hlo hup)) :=
  input_moment (family hV hm hh hlo hup) _ n

/-- Literal Gaussian-start root jet quadrature with no assumed regularity
record or derivative/moment budget. The order, dimension, and mesh are visible. -/
theorem source_gauss_cell (hsmall : h ≤ 1/2) (n : ℕ)
    (x delta u v : ℝ) (hdelta : 0 < delta)
    (hu : u ∈ Icc (0:ℝ) 1) (hv : v ∈ Icc (0:ℝ) 1)
    (hcell : Icc x (x+delta) ⊆ Icc (0:ℝ) (1/2)) :
    let F := family hV hm hh hlo hup
    let d := OuterRootOriginalData.data hV hh (lower_nonneg hm hlo) hup
    ‖(∫ t in (x+delta*u)..(x+delta*v), jetLp F d (Real.sqrt h)⁻¹ 1 t) -
      ∑ i : Fin (n+1), Numerics.GaussLegendre.partialRow (n+1) x delta u v
        (fun _ => 1) i • jetLp F d (Real.sqrt h)⁻¹ 1
          (Numerics.GaussLegendre.cellNode (n+1) x delta i)‖ ≤
      2*delta^(n+2)*((2*h^2)*Numerics.ConditionalSmoothing.materialOrderFactor
        (Fintype.card ι) n / (3/4)^(n+1))/((n+1).factorial:ℝ) := by
  dsimp only
  have H := jetLp_gauss_cell (family hV hm hh hlo hup)
    (OuterRootOriginalData.data hV hh (lower_nonneg hm hlo) hup) (Real.sqrt h)⁻¹
    (OuterRootOriginalData.data_small hV hh (lower_nonneg hm hlo) hup hsmall)
    n x delta u v hdelta hu hv hcell
  have he : (OuterRootOriginalData.data hV hh (lower_nonneg hm hlo) hup).ell *
      (OuterRootOriginalData.data hV hh (lower_nonneg hm hlo) hup).r^2 = 2*h^2 := by
    change h * (Real.sqrt (2*h))^2 = _
    rw [Real.sq_sqrt (by positivity)]
    ring
  rw [he] at H
  have hb : 1 - (OuterRootOriginalData.data hV hh (lower_nonneg hm hlo) hup).b^2 =
      (3/4 : ℝ) := by norm_num [OuterRootOriginalData.data]
  rw [hb] at H
  exact H


end AcceleratedLogConcave.Root.OuterRootOriginalQuadrature
