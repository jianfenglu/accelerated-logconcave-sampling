import AcceleratedLogConcave.Tensor.MeanFlowPhysicalKernelHalfBudget
import AcceleratedLogConcave.Conditional.JetCumulantCoordinates
import AcceleratedLogConcave.Tensor.ActualCoefficientTerminal

/-!
NEW reconstruction of the minimal ordered physical K jet interface.
This is not a recovered historical module. The scalar entry and ordered
partialAlong formula are the same formulas visible in the recovered
CenterMeanPhysicalTransportJet source, but this file deliberately avoids that
module's absent phase-gradient/hessian dependency chain.

The coordinate/Frechet proof is adapted from the recovered
CenterMeanPhysicalTransportFrechet.lean, with original PositiveVarianceFlowData
and the already accepted literal actualK replacing the unavailable phase context.
No tensor identity or derivative budget is assumed.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff
namespace AcceleratedLogConcave.Tensor.PhysicalKernelBudget
open Conditional QuantitativeKernel AdjointReduction CoordinateReduction
open ActualCoefficientIntegrability
variable {D m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "e" => EuclideanSpace.basisFun (Fin D) ℝ

/-- Literal scalar entry of the original transported Stein kernel transpose. -/
def physicalKernelEntry (d : PositiveVarianceFlowData E) (row col : Fin D) (y : E) : ℝ :=
  inner ℝ (e row) (actualK d y (e col))

/-- Literal ordered coordinate derivatives, not a newly selected tensor field. -/
def orderedPhysicalKernelJet (d : PositiveVarianceFlowData E) (n : ℕ) (y : E) :
    Coeff (Fin n ⊕ Fin 2) D :=
  WithLp.toLp 2 (fun v => partialAlong
    (fun i : Fin n => coordinateDirection D (v (.inl i))) (List.finRange n)
    (physicalKernelEntry d (v (.inr 0)) (v (.inr 1))) y)

theorem smooth_physicalKernelEntry (d : PositiveVarianceFlowData E)
    (hsmall : d.r^2*d.ell ≤ 1/2) (row col : Fin D) :
    ContDiff ℝ ∞ (physicalKernelEntry d row col) := by
  exact contDiff_const.inner ℝ
    ((Transport.contDiff_infty_transportedSteinKernelTranspose d.hF d.hell d.hlo d.hhi
      d.x d.hr d.hb0 d.hb1 hsmall).clm_apply contDiff_const)

private theorem iteratedFDeriv_cast_apply {n k : ℕ} (hn : n = k)
    (f : E → ℝ) (y : E) (v : Fin k → E) :
    iteratedFDeriv ℝ n f y (fun i => v (Fin.cast hn i)) =
      iteratedFDeriv ℝ k f y v := by
  subst k
  rfl

/-- All-order exact identity from ordered coordinate differentiation to the
actual Frechet derivative of actualK, with row 0 and column 1 unchanged. -/
theorem orderedPhysicalKernelJet_eq_frechet
    (d : PositiveVarianceFlowData E) (hsmall : d.r^2*d.ell ≤ 1/2)
    (n : ℕ) (y : E) :
    orderedPhysicalKernelJet d n y = physicalOperatorJetCoeff n (actualK d) y := by
  ext v
  have hK : ContDiff ℝ ∞ (actualK d) :=
    Transport.contDiff_infty_transportedSteinKernelTranspose d.hF d.hell d.hlo d.hhi
      d.x d.hr d.hb0 d.hb1 hsmall
  have hj : orderedPhysicalKernelJet d n y v =
      iteratedFDeriv ℝ n (physicalKernelEntry d (v (.inr 0)) (v (.inr 1))) y
        (fun i => coordinateDirection D (v (.inl i))) := by
    change partialAlong _ _ _ _ = _
    rw [partialAlong_eq_jet]
    have hjet := JetCalculus.jet_eq_iteratedFDeriv
      (smooth_physicalKernelEntry d hsmall (v (.inr 0)) (v (.inr 1)))
      (fun i : Fin n => coordinateDirection D (v (.inl i))) (List.finRange n) y
    have hcast := iteratedFDeriv_cast_apply (D := D) (n := (List.finRange n).length)
      List.length_finRange (physicalKernelEntry d (v (.inr 0)) (v (.inr 1))) y
      (fun i : Fin n => coordinateDirection D (v (.inl i)))
    apply Eq.trans _ hcast
    simpa using hjet
  let ev : (E →L[ℝ] E) →L[ℝ] ℝ :=
    (innerSL ℝ (e (v (.inr 0)))).comp
      (ContinuousLinearMap.apply ℝ E (e (v (.inr 1))))
  have he := ev.iteratedFDeriv_comp_left (x := y) hK.contDiffAt
    (show (n : ℕ∞ω) ≤ (⊤ : ℕ∞) by simp)
  rw [hj]
  change iteratedFDeriv ℝ n (ev ∘ actualK d) y _ = _
  rw [he]
  have hb (i : Fin D) : coordinateDirection D i = e i := by
    simp [EuclideanSpace.basisFun_apply, coordinateDirection, EuclideanSpace.single]
  simp only [hb]
  rfl

/-- Original-data half-budget for the actual ordered physical primitive tensor. -/
theorem original_data_orderedPhysicalKernel_halfBudget
    (d : PositiveVarianceFlowData E) (hsmall : d.r^2*d.ell ≤ 1/2)
    {c : ℝ} (hc : 128 ≤ c) (n : ℕ) (y : E)
    (S : Finset (Fin n ⊕ Fin 2)) (hS : NontrivialSplit S) :
    splitNorm D S (orderedPhysicalKernelJet d n y) ≤
      (d.r*d.ell)*(c^(2+n)*((2+n).factorial : ℝ)*
        (Real.sqrt (1-d.b^2))^(-(n : ℝ)))/2 := by
  rw [orderedPhysicalKernelJet_eq_frechet d hsmall]
  exact original_data_physicalKernel_halfBudget d hsmall hc n y S hS

/-- The original common-seed physical radius and scale, at every finite order.
This is the precise primitive K half-budget; not a full Regularity statement. -/
theorem meanFlow_orderedPhysicalKernel_halfBudget
    (d : Numerics.MeanFlowLp.Data (Fin D) m) {c : ℝ} (hc : 128 ≤ c)
    (n : ℕ) (y : E) (S : Finset (Fin n ⊕ Fin 2)) (hS : NontrivialSplit S) :
    splitNorm D S
      (orderedPhysicalKernelJet (positiveVarianceData (Numerics.MeanFlowLp.kernelData d)) n y) ≤
      (d.r*d.ell)*(c^(2+n)*((2+n).factorial : ℝ)*d.G.R^(-(n : ℝ)))/2 := by
  rw [orderedPhysicalKernelJet_eq_frechet _ d.hsmall]
  exact meanFlow_physical_halfBudget d hc n y S hS

/-- Zero curvature annihilates every actual ordered physical split. -/
theorem orderedPhysicalKernel_allProper_zero_curvature
    (d : PositiveVarianceFlowData E) (hsmall : d.r^2*d.ell ≤ 1/2)
    (hell : d.ell = 0) (n : ℕ) (y : E) : AllProper D (orderedPhysicalKernelJet d n y) 0 := by
  rw [orderedPhysicalKernelJet_eq_frechet d hsmall]
  exact physicalKernel_allProper_zero_curvature d hsmall hell n y

/-- The singleton-slab boundary retains the outer b at every order. -/
theorem orderedPhysicalKernel_allProper_zero_endpoint
    (d : PositiveVarianceFlowData E) (hsmall : d.r^2*d.ell ≤ 1/2)
    (hb : d.b = 0) (n : ℕ) (y : E) : AllProper D (orderedPhysicalKernelJet d n y) 0 := by
  rw [orderedPhysicalKernelJet_eq_frechet d hsmall]
  exact physicalKernel_allProper_zero_endpoint d hsmall hb n y

end AcceleratedLogConcave.Tensor.PhysicalKernelBudget
