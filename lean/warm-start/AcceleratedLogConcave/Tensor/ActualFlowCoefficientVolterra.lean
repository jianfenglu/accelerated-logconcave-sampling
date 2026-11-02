import AcceleratedLogConcave.Conditional.Transport.ActualFlowVolterra
import AcceleratedLogConcave.Tensor.ActualCoefficientBridge

/-!

-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped ContDiff BigOperators
namespace AcceleratedLogConcave.Tensor.ActualCoefficient
open Conditional Conditional.Transport.SpatialFlow
variable {D : ℕ}

/-- Full derivative and output indices remain free; every internal assignment is
summed, including repeated labels. The sign is terminal minus integral. -/
theorem actual_flow_coefficient_volterra
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (n : ℕ) (a : Fin n → Fin D) (o : Fin D) (y : Space D)
    {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    inner ℝ (basis D o)
      (iteratedFDeriv ℝ n (actualY d t) y (fun j => basis D (a j))) =
    inner ℝ (basis D o)
      (iteratedFDeriv ℝ n (id : Space D → Space D) y (fun j => basis D (a j))) -
      ∫ s in t..d.b,
        ∑ c : OrderedFinpartition n, ∑ w : Fin c.length → Fin D,
          (∏ i, inner ℝ (basis D (w i))
            (iteratedFDeriv ℝ (c.partSize i) (actualY d s) y
              (fun j => basis D (a (c.emb i j))))) *
          inner ℝ (basis D o)
            (iteratedFDeriv ℝ c.length (probabilityVelocity d.F d.x d.r s)
              (actualY d s y) (fun i => basis D (w i))) := by
  have h := actual_iteratedFDeriv_volterra_readout d hsmall n
    (fun j => basis D (a j)) y (innerSL ℝ (basis D o)) ht
  change inner ℝ (basis D o) _ = inner ℝ (basis D o) _ - _ at h
  rw [h]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht.2] at hs
  have hs0 : s ∈ Icc 0 d.b := ⟨ht.1.trans hs.1,hs.2⟩
  exact iteratedFDeriv_comp_coefficient (probabilityVelocity d.F d.x d.r s)
    (actualY d s) y
    (contDiff_probabilityVelocity_spatial d.hF d.hlo d.hhi d.x
      (r := d.r) (by linarith [hs0.1]) (hs0.2.trans_lt d.hb1)).contDiffAt
    (contDiff_backward_spatial d.hF d.hell d.hlo d.hhi d.x
      d.hr d.hb0 d.hb1 hsmall hs0).contDiffAt n a (innerSL ℝ (basis D o))

/-- D=0 is not handled by selecting a nonexistent basis coordinate: use the
vector identity itself. No Nonempty(Fin D) hypothesis exists upstream. -/
theorem actual_flow_volterra_dimension_zero
    (d : PositiveVarianceFlowData (Space 0)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (n : ℕ) (m : Fin n → Space 0) (y : Space 0)
    {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    iteratedFDeriv ℝ n (actualY d t) y m =
      iteratedFDeriv ℝ n (id : Space 0 → Space 0) y m -
        ∫ s in t..d.b, iteratedFDeriv ℝ n
          (fun z => probabilityVelocity d.F d.x d.r s (actualY d s z)) y m :=
  actual_iteratedFDeriv_volterra d hsmall n m y ht

end AcceleratedLogConcave.Tensor.ActualCoefficient
